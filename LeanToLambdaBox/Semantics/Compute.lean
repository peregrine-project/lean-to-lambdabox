import LeanToLambdaBox.Semantics.Eval

/-!
# `lbEval` — a fuel-indexed executable evaluator for λ□

`WcbvEval` is a `Prop`-valued relation: it says what a λ□ term *may* evaluate to,
but it computes nothing. This module supplies the executable twin `lbEval`, a
fuel-indexed evaluator that implements every rule of `WcbvEval` — box, β, ζ, δ,
both constructor regimes, ι (spine, block and propositional), projections
(spine, block and propositional), guarded and unguarded `fix`, and the stuck
application congruence — under the same `WcbvFlags`, and the soundness theorem
`lbEval_sound` tying the two together: whatever `lbEval` returns is a value the
relation admits. Fuel exhaustion and every unmodelled shape return `none`, so
soundness is the only direction that can hold (and the only one we need).

The evaluator is structurally recursive on the fuel, so it reduces in the kernel:
target-side evaluation of a closed λ□ program becomes `by rfl`, and the same code
runs under `#eval` and in the `green-check` executable as a differential oracle
against `peregrine eval`.
-/

namespace LeanToLambdaBox

open Lean

/-! ### Decidable equality on the identifiers the ι and projection rules compare. -/

deriving instance DecidableEq for ModPath
deriving instance DecidableEq for Kername
deriving instance DecidableEq for InductiveId

/-- Every term is the `mkApps` spine of its own head and arguments; the bridge
    between the executable `spineHead`/`spineArgs` decomposition and the
    `mkApps`-shaped premises of the spine rules of `WcbvEval`. -/
theorem LBTerm.mkApps_spine : ∀ t : LBTerm,
    LBTerm.mkApps (LBTerm.spineHead t) (LBTerm.spineArgs t) = t
  | .app f a => by
    show LBTerm.mkApps (LBTerm.spineHead f) (LBTerm.spineArgs f ++ [a]) = LBTerm.app f a
    rw [LBTerm.mkApps_concat, LBTerm.mkApps_spine f]
  | .box | .bvar _ | .fvar _ | .lambda _ _ | .letIn _ _ _ | .const _
  | .construct _ _ _ | .case _ _ _ | .proj _ _ | .fix _ _ | .prim _ => rfl

/-! ### The evaluator -/

/-- Evaluate a block constructor's argument list left to right with `ev`,
    failing as soon as one argument fails. -/
def lbEvalArgs (ev : LBTerm → Option LBTerm) : List LBTerm → Option (List LBTerm)
  | [] => some []
  | t :: ts =>
    match ev t, lbEvalArgs ev ts with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Apply an evaluated non-λ, non-`box`, non-bare-`fix` head `f'` to the value
    `av`, dispatching on the head of `f'`'s application spine: a constructor
    spine accumulates (`construct_app`), a `fix` spine unfolds or accumulates
    (`fix_guarded`/`fix_stuck`), any other stuck head congruates (`app_cong`). -/
def lbEvalSpine (Γ : GlobalDeclarations) (fl : WcbvFlags) (ev : LBTerm → Option LBTerm)
    (f' av : LBTerm) : Option LBTerm :=
  match LBTerm.spineHead f' with
  | .construct iid c [] =>
    if fl.with_constructor_as_block then none
    else
      match constructorArity Γ iid c with
      | some ar => if (LBTerm.spineArgs f').length < ar then some (.app f' av) else none
      | none => none
  | .fix defs idx =>
    if fl.with_guarded_fix then
      match defs[idx]? with
      | some d =>
        if d.principalArgIdx = (LBTerm.spineArgs f').length then
          ev (.app (LBTerm.mkApps (LBTerm.substList (LBTerm.fixSubst defs) d.body)
                (LBTerm.spineArgs f')) av)
        else if (LBTerm.spineArgs f').length < d.principalArgIdx then some (.app f' av)
        else none
      | none => none
    else if isStuckApp fl f' then some (.app f' av) else none
  | _ => if isStuckApp fl f' then some (.app f' av) else none

/-- Apply the evaluated head `f'` to the evaluated argument `av`: β on a λ,
    `app_box` on `box`, the guarded/unguarded `fix` rules on a bare `fix`, and
    the spine dispatch otherwise. Every application rule of `WcbvEval` evaluates
    its argument, so `av` is computed once by the caller. -/
def lbEvalApp (Γ : GlobalDeclarations) (fl : WcbvFlags) (ev : LBTerm → Option LBTerm)
    (f' av : LBTerm) : Option LBTerm :=
  match f' with
  | .lambda _ b => ev (LBTerm.subst1 av b)
  | .box => some .box
  | .fix defs idx =>
    match defs[idx]? with
    | some d =>
      if fl.with_guarded_fix then
        if d.principalArgIdx = 0 then
          ev (.app (LBTerm.substList (LBTerm.fixSubst defs) d.body) av)
        else some (.app (.fix defs idx) av)
      else ev (.app (LBTerm.substList (LBTerm.fixSubst defs) d.body) av)
    | none => none
  | t => lbEvalSpine Γ fl ev t av

/-- Reduce a `case`: evaluate the discriminant, then take the propositional
    single-branch rule (`iota_sing`), the block ι rule (`iota_block`) or the
    spine ι rule (`iota`) according to the flags and the inductive. -/
def lbEvalCase (Γ : GlobalDeclarations) (fl : WcbvFlags) (ev : LBTerm → Option LBTerm)
    (iid : InductiveId) (np : Nat) (discr : LBTerm)
    (alts : List (List BinderName × LBTerm)) : Option LBTerm :=
  match ev discr with
  | none => none
  | some dv =>
    if isPropositionalInductive Γ iid then
      if fl.with_prop_case then
        match alts, dv with
        | [(names, body)], .box => ev (LBTerm.substList (List.replicate names.length .box) body)
        | _, _ => none
      else none
    else if fl.with_constructor_as_block then
      match dv with
      | .construct iid' k cargs =>
        if iid' = iid then
          match alts[k]? with
          | some (names, body) =>
            if (cargs.drop np).length = names.length then
              ev (LBTerm.substList ((cargs.drop np).reverse) body)
            else none
          | none => none
        else none
      | _ => none
    else
      match LBTerm.spineHead dv with
      | .construct iid' k [] =>
        if iid' = iid then
          match alts[k]? with
          | some (names, body) =>
            if ((LBTerm.spineArgs dv).drop np).length = names.length then
              ev (LBTerm.substList (((LBTerm.spineArgs dv).drop np).reverse) body)
            else none
          | none => none
        else none
      | _ => none

/-- Reduce a projection: evaluate the discriminant, then take `proj_prop`,
    `proj_block` or the spine `proj` rule according to the flags and the
    inductive, and evaluate the selected field. -/
def lbEvalProj (Γ : GlobalDeclarations) (fl : WcbvFlags) (ev : LBTerm → Option LBTerm)
    (p : ProjectionInfo) (discr : LBTerm) : Option LBTerm :=
  match ev discr with
  | none => none
  | some dv =>
    if isPropositionalInductive Γ p.indType then
      if fl.with_prop_case then
        match dv with
        | .box => some .box
        | _ => none
      else none
    else if fl.with_constructor_as_block then
      match dv with
      | .construct iid' 0 cargs =>
        if iid' = p.indType then
          match cargs[p.paramCount + p.fieldIdx]? with
          | some v => ev v
          | none => none
        else none
      | _ => none
    else
      match LBTerm.spineHead dv with
      | .construct iid' 0 [] =>
        if iid' = p.indType then
          match (LBTerm.spineArgs dv)[p.paramCount + p.fieldIdx]? with
          | some v => ev v
          | none => none
        else none
      | _ => none

/-- One evaluation step: the whole rule table of `WcbvEval` at the top node of
    `t`, with `ev` standing for evaluation at one unit less fuel. Values (box,
    λ, free variable, primitive, bare `fix`) return themselves; unmodelled
    shapes (a loose `bvar`, an over-applied constructor, a missing declaration)
    return `none`. -/
def lbEvalStep (Γ : GlobalDeclarations) (fl : WcbvFlags) (ev : LBTerm → Option LBTerm) :
    LBTerm → Option LBTerm
  | .box => some .box
  | .bvar _ => none
  | .fvar x => some (.fvar x)
  | .lambda n b => some (.lambda n b)
  | .prim p => some (.prim p)
  | .fix defs i => some (.fix defs i)
  | .const kn =>
    match LBTerm.envLookup Γ kn with
    | some (.constantDecl ⟨some body⟩) => ev body
    | _ => none
  | .letIn _ v b =>
    match ev v with
    | some vv => ev (LBTerm.subst1 vv b)
    | none => none
  | .app f a =>
    match ev f, ev a with
    | some f', some av => lbEvalApp Γ fl ev f' av
    | _, _ => none
  | .construct iid k args =>
    if fl.with_constructor_as_block then
      match lbEvalArgs ev args with
      | some vs => some (.construct iid k vs)
      | none => none
    else
      match args, constructorArity Γ iid k with
      | [], some _ => some (.construct iid k [])
      | _, _ => none
  | .case (iid, np) discr alts => lbEvalCase Γ fl ev iid np discr alts
  | .proj p discr => lbEvalProj Γ fl ev p discr

/-- Fuel-indexed executable weak call-by-value evaluation of λ□, relative to a
    global environment `Γ` and evaluation flags `fl`. Structurally recursive on
    the fuel: `lbEval Γ fl (n+1)` runs one `lbEvalStep` over `lbEval Γ fl n`, and
    exhausted fuel is `none`. Sound for `WcbvEval` (`lbEval_sound`). -/
def lbEval (Γ : GlobalDeclarations) (fl : WcbvFlags) : Nat → LBTerm → Option LBTerm
  | 0, _ => none
  | n + 1, t => lbEvalStep Γ fl (lbEval Γ fl n) t

/-! ### Soundness -/

/-- `lbEvalArgs` preserves the length of the argument list. -/
theorem lbEvalArgs_length {ev : LBTerm → Option LBTerm} :
    ∀ {args vs : List LBTerm}, lbEvalArgs ev args = some vs → args.length = vs.length := by
  intro args
  induction args with
  | nil => intro vs h; simp only [lbEvalArgs, Option.some.injEq] at h; subst h; rfl
  | cons t ts ih =>
    intro vs h
    simp only [lbEvalArgs] at h
    split at h
    · rename_i v vs' _ hvs
      cases h
      simp only [List.length_cons, ih hvs]
    · exact absurd h (by simp)

/-- Each argument accepted by `lbEvalArgs` is `ev`-evaluated to the corresponding
    element of the result. -/
theorem lbEvalArgs_get {ev : LBTerm → Option LBTerm} :
    ∀ {args vs : List LBTerm}, lbEvalArgs ev args = some vs →
      ∀ i (h : i < args.length) (h' : i < vs.length), ev args[i] = some vs[i] := by
  intro args
  induction args with
  | nil => intro vs h i hi _; exact absurd hi (by simp)
  | cons t ts ih =>
    intro vs h i hi hi'
    simp only [lbEvalArgs] at h
    split at h
    · rename_i v vs' hv hvs
      cases h
      cases i with
      | zero => exact hv
      | succ j =>
        exact ih hvs j (by simpa using hi) (by simpa using hi')
    · exact absurd h (by simp)

/-- Soundness of the spine dispatch: any value it returns for `f' av`, given that
    `f` evaluates to `f'` and `a` to `av`, is a `WcbvEval` result of `.app f a`
    (by `construct_app`, `fix_guarded`, `fix_stuck` or `app_cong`). -/
theorem lbEvalSpine_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev : LBTerm → Option LBTerm}
    (hev : ∀ t v, ev t = some v → WcbvEval Γ fl t v)
    {f a f' av r : LBTerm} (hf : WcbvEval Γ fl f f') (ha : WcbvEval Γ fl a av)
    (h : lbEvalSpine Γ fl ev f' av = some r) : WcbvEval Γ fl (.app f a) r := by
  unfold lbEvalSpine at h
  split at h
  · rename_i iid c heq
    have hsp : LBTerm.mkApps (.construct iid c []) (LBTerm.spineArgs f') = f' := by
      rw [← heq]; exact LBTerm.mkApps_spine f'
    split at h
    · simp at h
    · rename_i hb
      have hb' : fl.with_constructor_as_block = false := by simpa using hb
      split at h
      · rename_i ar har
        split at h
        · rename_i hlt
          injection h with h; subst h
          rw [← hsp] at hf ⊢
          exact .construct_app hb' hf har hlt ha
        · simp at h
      · simp at h
  · rename_i defs idx heq
    have hsp : LBTerm.mkApps (.fix defs idx) (LBTerm.spineArgs f') = f' := by
      rw [← heq]; exact LBTerm.mkApps_spine f'
    split at h
    · rename_i hg
      split at h
      · rename_i d hd
        split at h
        · rename_i hrarg
          rw [← hsp] at hf
          exact .fix_guarded hg hf ha hd hrarg (hev _ _ h)
        · split at h
          · rename_i hlt
            injection h with h; subst h
            rw [← hsp] at hf ⊢
            exact .fix_stuck hg hf ha hd hlt
          · simp at h
      · simp at h
    · split at h
      · rename_i hs
        injection h with h; subst h
        exact .app_cong hf hs ha
      · simp at h
  · split at h
    · rename_i hs
      injection h with h; subst h
      exact .app_cong hf hs ha
    · simp at h

/-- Soundness of the application dispatch: any value it returns for `f' av`,
    given that `f` evaluates to `f'` and `a` to `av`, is a `WcbvEval` result of
    `.app f a` (by `beta`, `app_box`, a `fix` rule, or the spine dispatch). -/
theorem lbEvalApp_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev : LBTerm → Option LBTerm}
    (hev : ∀ t v, ev t = some v → WcbvEval Γ fl t v)
    {f a f' av r : LBTerm} (hf : WcbvEval Γ fl f f') (ha : WcbvEval Γ fl a av)
    (h : lbEvalApp Γ fl ev f' av = some r) : WcbvEval Γ fl (.app f a) r := by
  unfold lbEvalApp at h
  split at h
  · exact .beta hf ha (hev _ _ h)
  · injection h with h; subst h
    exact .app_box hf ha
  · rename_i defs idx
    split at h
    · rename_i d hd
      split at h
      · rename_i hg
        split at h
        · rename_i hz
          exact .fix_guarded (argsv := []) hg hf ha hd hz (hev _ _ h)
        · rename_i hnz
          injection h with h; subst h
          exact .fix_stuck (argsv := []) hg hf ha hd (Nat.pos_of_ne_zero hnz)
      · rename_i hg
        have hg' : fl.with_guarded_fix = false := by simpa using hg
        exact .fix_unguarded hg' hf hd ha (hev _ _ h)
    · simp at h
  · exact lbEvalSpine_sound hev hf ha h

/-- Soundness of the `case` reduction: any value it returns is a `WcbvEval`
    result of the case term (by `iota`, `iota_block` or `iota_sing`). -/
theorem lbEvalCase_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev : LBTerm → Option LBTerm}
    (hev : ∀ t v, ev t = some v → WcbvEval Γ fl t v)
    {iid : InductiveId} {np : Nat} {discr r : LBTerm}
    {alts : List (List BinderName × LBTerm)}
    (h : lbEvalCase Γ fl ev iid np discr alts = some r) :
    WcbvEval Γ fl (.case (iid, np) discr alts) r := by
  unfold lbEvalCase at h
  split at h
  · simp at h
  · rename_i dv hdv
    split at h
    · rename_i hprop
      split at h
      · rename_i hpc
        split at h
        · rename_i names body
          exact .iota_sing hpc hprop (hev _ _ hdv) (hev _ _ h)
        · simp at h
      · simp at h
    · rename_i hprop
      have hprop' : isPropositionalInductive Γ iid = false := by simpa using hprop
      split at h
      · rename_i hb
        split at h
        · rename_i iid' k cargs
          split at h
          · rename_i hiid
            subst hiid
            split at h
            · rename_i names body halt
              split at h
              · rename_i hlen
                exact .iota_block hb hprop' (hev _ _ hdv) halt hlen (hev _ _ h)
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      · rename_i hb
        have hb' : fl.with_constructor_as_block = false := by simpa using hb
        split at h
        · rename_i iid' k heq
          have hsp : LBTerm.mkApps (.construct iid' k []) (LBTerm.spineArgs dv) = dv := by
            rw [← heq]; exact LBTerm.mkApps_spine dv
          split at h
          · rename_i hiid
            subst hiid
            split at h
            · rename_i names body halt
              split at h
              · rename_i hlen
                have hd := hev _ _ hdv
                rw [← hsp] at hd
                exact .iota hb' hprop' hd halt hlen (hev _ _ h)
              · simp at h
            · simp at h
          · simp at h
        · simp at h

/-- Soundness of the projection reduction: any value it returns is a `WcbvEval`
    result of the projection term (by `proj`, `proj_block` or `proj_prop`). -/
theorem lbEvalProj_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev : LBTerm → Option LBTerm}
    (hev : ∀ t v, ev t = some v → WcbvEval Γ fl t v)
    {p : ProjectionInfo} {discr r : LBTerm}
    (h : lbEvalProj Γ fl ev p discr = some r) : WcbvEval Γ fl (.proj p discr) r := by
  unfold lbEvalProj at h
  split at h
  · simp at h
  · rename_i dv hdv
    split at h
    · rename_i hprop
      split at h
      · rename_i hpc
        split at h
        · injection h with h; subst h
          exact .proj_prop hpc hprop (hev _ _ hdv)
        · simp at h
      · simp at h
    · rename_i hprop
      have hprop' : isPropositionalInductive Γ p.indType = false := by simpa using hprop
      split at h
      · rename_i hb
        split at h
        · rename_i iid' cargs
          split at h
          · rename_i hiid
            subst hiid
            split at h
            · rename_i v hv
              exact .proj_block hb hprop' (hev _ _ hdv) hv (hev _ _ h)
            · simp at h
          · simp at h
        · simp at h
      · rename_i hb
        have hb' : fl.with_constructor_as_block = false := by simpa using hb
        split at h
        · rename_i iid' heq
          have hsp : LBTerm.mkApps (.construct iid' 0 []) (LBTerm.spineArgs dv) = dv := by
            rw [← heq]; exact LBTerm.mkApps_spine dv
          split at h
          · rename_i hiid
            subst hiid
            split at h
            · rename_i v hv
              have hd := hev _ _ hdv
              rw [← hsp] at hd
              exact .proj hb' hprop' hd hv (hev _ _ h)
            · simp at h
          · simp at h
        · simp at h

/-- Soundness of one evaluation step: whatever `lbEvalStep` returns for `t`, the
    `WcbvEval` relation admits, provided `ev` is itself sound. -/
theorem lbEvalStep_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev : LBTerm → Option LBTerm}
    (hev : ∀ t v, ev t = some v → WcbvEval Γ fl t v)
    {t v : LBTerm} (h : lbEvalStep Γ fl ev t = some v) : WcbvEval Γ fl t v := by
  unfold lbEvalStep at h
  split at h
  · injection h with h; subst h; exact .box
  · simp at h
  · injection h with h; subst h; exact .fvar _
  · injection h with h; subst h; exact .lam _ _
  · injection h with h; subst h; exact .prim _
  · injection h with h; subst h; exact .fix_atom _ _
  · split at h
    · rename_i body hlook
      exact .delta hlook (hev _ _ h)
    · simp at h
  · split at h
    · rename_i vv hvv
      exact .zeta (hev _ _ hvv) (hev _ _ h)
    · simp at h
  · split at h
    · rename_i f' av hf ha
      exact lbEvalApp_sound hev (hev _ _ hf) (hev _ _ ha) h
    · simp at h
  · rename_i iid k args
    split at h
    · rename_i hb
      split at h
      · rename_i vs hvs
        injection h with h; subst h
        exact .construct hb (lbEvalArgs_length hvs)
          (fun i hi => hev _ _ (lbEvalArgs_get hvs i hi _))
      · simp at h
    · rename_i hb
      have hb' : fl.with_constructor_as_block = false := by simpa using hb
      split at h
      · rename_i ar har
        injection h with h; subst h
        exact .construct_atom hb' har
      · simp at h
  · exact lbEvalCase_sound hev h
  · exact lbEvalProj_sound hev h

/-- **Soundness of `lbEval`.** Every value the executable evaluator returns is a
    value the `WcbvEval` relation admits for the same term, environment and
    flags. The converse fails only by fuel exhaustion, which returns `none`. -/
theorem lbEval_sound {Γ : GlobalDeclarations} {fl : WcbvFlags} {n : Nat} {t v : LBTerm}
    (h : lbEval Γ fl n t = some v) : WcbvEval Γ fl t v := by
  induction n generalizing t v with
  | zero => simp [lbEval] at h
  | succ n ih => exact lbEvalStep_sound (fun _ _ h' => ih h') h

/-! ### Fuel monotonicity

Each layer transports a successful run along a pointwise-larger recursive
evaluator; iterating that up the fuel gives `lbEval_mono`. -/

/-- `lbEvalArgs` transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalArgs_mono {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v) :
    ∀ {args vs : List LBTerm}, lbEvalArgs ev args = some vs → lbEvalArgs ev' args = some vs := by
  intro args
  induction args with
  | nil => intro vs h; exact h
  | cons t ts ih =>
    intro vs h
    simp only [lbEvalArgs] at h ⊢
    split at h
    · rename_i v vs' hv hvs
      rw [hm _ _ hv, ih hvs]
      exact h
    · simp at h

/-- The spine dispatch transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalSpine_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v) {f' av r : LBTerm}
    (h : lbEvalSpine Γ fl ev f' av = some r) : lbEvalSpine Γ fl ev' f' av = some r := by
  unfold lbEvalSpine at h ⊢
  repeat' (split at h <;> (try split) <;> simp_all)

/-- The application dispatch transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalApp_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v) {f' av r : LBTerm}
    (h : lbEvalApp Γ fl ev f' av = some r) : lbEvalApp Γ fl ev' f' av = some r := by
  unfold lbEvalApp at h ⊢
  split at h <;> (try split) <;> simp_all [lbEvalSpine_mono hm]
  repeat' (split at h <;> (try split) <;> simp_all)

/-- The `case` reduction transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalCase_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v)
    {iid : InductiveId} {np : Nat} {discr r : LBTerm} {alts : List (List BinderName × LBTerm)}
    (h : lbEvalCase Γ fl ev iid np discr alts = some r) :
    lbEvalCase Γ fl ev' iid np discr alts = some r := by
  unfold lbEvalCase at h ⊢
  repeat' (split at h <;> (try split) <;> simp_all)

/-- The projection reduction transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalProj_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v) {p : ProjectionInfo} {discr r : LBTerm}
    (h : lbEvalProj Γ fl ev p discr = some r) : lbEvalProj Γ fl ev' p discr = some r := by
  unfold lbEvalProj at h ⊢
  repeat' (split at h <;> (try split) <;> simp_all)

/-- One evaluation step transports a successful run to any pointwise-larger `ev'`. -/
theorem lbEvalStep_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {ev ev' : LBTerm → Option LBTerm}
    (hm : ∀ t v, ev t = some v → ev' t = some v) {t v : LBTerm}
    (h : lbEvalStep Γ fl ev t = some v) : lbEvalStep Γ fl ev' t = some v := by
  cases t <;> (try simp only [lbEvalStep] at h ⊢) <;>
    first
      | exact h
      | exact lbEvalCase_mono hm h
      | exact lbEvalProj_mono hm h
      | repeat' (split at h <;> (try split) <;>
          simp_all [lbEvalApp_mono hm, lbEvalArgs_mono hm])

/-- One more unit of fuel never loses an answer. -/
theorem lbEval_succ {Γ : GlobalDeclarations} {fl : WcbvFlags} {n : Nat} {t v : LBTerm}
    (h : lbEval Γ fl n t = some v) : lbEval Γ fl (n + 1) t = some v := by
  induction n generalizing t v with
  | zero => simp [lbEval] at h
  | succ n ih => exact lbEvalStep_mono (fun _ _ h' => ih h') h

/-- **Fuel monotonicity.** An answer found with `n` units of fuel is found again
    with any larger amount, so a run may always be re-checked at more fuel. -/
theorem lbEval_mono {Γ : GlobalDeclarations} {fl : WcbvFlags} {n m : Nat} {t v : LBTerm}
    (h : lbEval Γ fl n t = some v) (hnm : n ≤ m) : lbEval Γ fl m t = some v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact lbEval_succ ih

/-! ### Non-vacuity: a hand-built environment the evaluator runs on

A one-inductive, two-constant environment (`nvEnv`) holding a Peano `N` with
constructors `O`/`S` and a `case`/`fix` program over it, in both constructor
regimes. The `example`s below are checked by the kernel (`rfl`), and
`lbEval_sound` turns each of them into a real `WcbvEval` derivation. -/

/-- Kername of the non-vacuity Peano inductive `N`. -/
def nvNatKn : Kername := rootKername "N"

/-- The non-vacuity Peano inductive: block `N`, first (only) body. -/
def nvNatIid : InductiveId := ⟨nvNatKn, 0⟩

/-- The mutual block of the non-vacuity Peano inductive: no parameters, one
    body with constructors `O` (0 fields) and `S` (1 field). -/
def nvNatMib : MutualInductiveBody :=
  { finite := .finite, npars := 0,
    bodies := [{ name := "N", propositional := false, kelim := .IntoAny,
                 ctors := [⟨"O", 0⟩, ⟨"S", 1⟩], projs := [] }] }

/-- The Peano numeral `n` in **applied** (non-block) form: `S` is a nullary
    constructor node applied through `.app`. -/
def nvPeanoA : Nat → LBTerm
  | 0 => .construct nvNatIid 0 []
  | n + 1 => .app (.construct nvNatIid 1 []) (nvPeanoA n)

/-- The Peano numeral `n` in **block** form: `S` carries its field inside the
    constructor node. -/
def nvPeanoB : Nat → LBTerm
  | 0 => .construct nvNatIid 0 []
  | n + 1 => .construct nvNatIid 1 [nvPeanoB n]

/-- Kername of the applied-form constant `twoA := S (S O)`. -/
def nvTwoAKn : Kername := rootKername "twoA"

/-- Kername of the block-form constant `twoB := S (S O)`. -/
def nvTwoBKn : Kername := rootKername "twoB"

/-- `addTwo` in applied form: `fix f. fun x => case x of O => S (S O) | S y => S (f y)`. -/
def nvAddTwoA : @FixDef LBTerm :=
  { name := .named "f", principalArgIdx := 0,
    body := .lambda (.named "x")
      (.case (nvNatIid, 0) (.bvar 0)
        [([], nvPeanoA 2),
         ([.named "y"], .app (.construct nvNatIid 1 []) (.app (.bvar 2) (.bvar 0)))]) }

/-- `addTwo` in block form: `fix f. fun x => case x of O => S (S O) | S y => S (f y)`. -/
def nvAddTwoB : @FixDef LBTerm :=
  { name := .named "f", principalArgIdx := 0,
    body := .lambda (.named "x")
      (.case (nvNatIid, 0) (.bvar 0)
        [([], nvPeanoB 2),
         ([.named "y"], .construct nvNatIid 1 [.app (.bvar 2) (.bvar 0)])]) }

/-- The predecessor `case` on a numeral `t`: `case t of O => O | S y => y`. The
    ι rule is the only rule that can reduce it. -/
def nvPredA (t : LBTerm) : LBTerm :=
  .case (nvNatIid, 0) t [([], nvPeanoA 0), ([.named "y"], .bvar 0)]

/-- The predecessor `case` on a block numeral. -/
def nvPredB (t : LBTerm) : LBTerm :=
  .case (nvNatIid, 0) t [([], nvPeanoB 0), ([.named "y"], .bvar 0)]

/-- The non-vacuity environment: the Peano inductive plus the two constants
    `twoA`/`twoB`, one per constructor regime. -/
def nvEnv : GlobalDeclarations :=
  [(nvNatKn, .inductiveDecl nvNatMib),
   (nvTwoAKn, .constantDecl ⟨some (nvPeanoA 2)⟩),
   (nvTwoBKn, .constantDecl ⟨some (nvPeanoB 2)⟩)]

/-- δ and the applied-constructor regime: the constant `twoA` runs to the Peano
    numeral `2` under `eraseFlags` (`with_constructor_as_block := false`). -/
example : lbEval nvEnv eraseFlags 1000 (.const nvTwoAKn) = some (nvPeanoA 2) := by rfl

/-- δ and the block-constructor regime: the constant `twoB` runs to the Peano
    numeral `2` under `blockFlags` (`with_constructor_as_block := true`). -/
example : lbEval nvEnv blockFlags 1000 (.const nvTwoBKn) = some (nvPeanoB 2) := by rfl

/-- ι on a constructor spine: the predecessor of `3` is `2` under `eraseFlags`. -/
example : lbEval nvEnv eraseFlags 1000 (nvPredA (nvPeanoA 3)) = some (nvPeanoA 2) := by rfl

/-- ι on a constructor block: the predecessor of `3` is `2` under `blockFlags`. -/
example : lbEval nvEnv blockFlags 1000 (nvPredB (nvPeanoB 3)) = some (nvPeanoB 2) := by rfl

/-- `fix` unfolding (twice, through ι and β) in the applied regime: `addTwo 2 = 4`. -/
example : lbEval nvEnv eraseFlags 1000 (.app (.fix [nvAddTwoA] 0) (nvPeanoA 2))
    = some (nvPeanoA 4) := by rfl

/-- `fix` unfolding in the block regime: `addTwo 2 = 4`. -/
example : lbEval nvEnv blockFlags 1000 (.app (.fix [nvAddTwoB] 0) (nvPeanoB 2))
    = some (nvPeanoB 4) := by rfl

/-- The point of `lbEval_sound`: a kernel-checked run is a `WcbvEval` derivation,
    here for the applied-form `fix`/ι/β program `addTwo 2 = 4`. -/
example : WcbvEval nvEnv eraseFlags (.app (.fix [nvAddTwoA] 0) (nvPeanoA 2)) (nvPeanoA 4) :=
  lbEval_sound (n := 1000) (by rfl)

/-- The same for the block-form `fix`/ι/β program. -/
example : WcbvEval nvEnv blockFlags (.app (.fix [nvAddTwoB] 0) (nvPeanoB 2)) (nvPeanoB 4) :=
  lbEval_sound (n := 1000) (by rfl)

end LeanToLambdaBox
