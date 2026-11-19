import EraseProof.Core.StepsCtor

/-!
# Steps of the shipping core's correctness: `casesOn` alternatives and the λ□ `case`

The pieces of `visitCases` (`LeanToLambdaBox/Erasure.lean:1092`) that build a λ□ `case`: what the
recognizer `casesInfo?` gives (`casesInfo?_facts`), an alternative erased under its fields'
binders by `visitAlt` (`:1249`, `visitAlt_spec`), and the `case` that `visitCasesOn` (`:1169`,
`visitCasesOn_spec`) builds from them.

`visitAlt` peels the alternative's λs and η-introduces the missing ones (`lambdaOrIntroToArity`,
`:662`), each binder a fresh local of the leading `Π` that `forallView?` reads off the type the
oracle infers; the marking traces this (`MarkAlt`). Each traversal variable is the next one of the
counter, to which the marking's fresh variable is renamed (`RenOK.push`), and `mkAlt` (`:563`)
closes the fields one depth each (`ErasesAlt.absN`); the λ□ binder names are the `Π`s', which the
oracle's type of a λ shares with it (`inferType_lamMatch`).

Reference: the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tCase` (`MR E/Extract.v:109`). Adapted from `ML-V Core/StepsCases.lean`,
`ML-V Core/StepsCasesBox.lean` and `ML-V Core/StepsCasesCase.lean`, whose typing premises are
replaced by the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas

/-! ## The recognizer -/

/-- What `casesInfo?` gives about a recognized `casesOn` `c`: the definition `c` of the inductive
`ci.indName` of `decls`, named `ci.indName.casesOn`, its arity and discriminant position, one
`.ctor` alternative per constructor and their range. Adapted from `ML-V Core/StepsCases.lean:30`,
`ML-V Core/StepsCasesBox.lean:256, 342`. -/
theorem casesInfo?_facts {decls : List ConstantInfo} {c : Name} {ci : CasesInfo}
    (h : casesInfo? decls c = some ci) :
    ∃ iv d alts, findDecl decls ci.indName = some (.inductInfo iv) ∧
      findDecl decls c = some (.defnInfo d) ∧ ci.declName = c ∧ c = .str ci.indName "casesOn" ∧
      ci.arity = casesArity iv ∧ ci.discrPos = casesMajor iv ∧
      ctorAlts decls iv.ctors = some alts ∧ ci.altNumParams = alts.toArray ∧
      ci.altsRange = (casesMajor iv + 1)...(casesArity iv) := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body alts before hj hb ha hbe =>
        split at h
        next hok =>
          cases h
          exact ⟨I, d, alts, hI, hd, rfl, rfl, rfl, rfl, ha, rfl, rfl⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-! ## The binders of an alternative -/

/-- The leading λs of `e` are the leading `Π`s of `T`, with the same binder names and domains.
Copy of `ML-V Core/StepsCasesCase.lean:29`. -/
def LamMatch : Expr → Expr → Prop
  | .lam x A b _, T => ∃ B bi, T = .forallE x A B bi ∧ LamMatch b B
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .app .., _
  | .forallE .., _ | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => True

/-- The oracle's type of a λ is a `Π` with the λ's binder name and domain. Copy of
`ML-V Core/StepsCasesCase.lean:35`. -/
theorem inferType_lamMatch {cx : Pure.Ctx} {ls : List Local} :
    ∀ (f : Nat) (Γo : List Expr) (e : Expr) {T : Expr}, Pure.inferType cx f ls Γo e = .ok T →
      LamMatch e T
  | 0, _, _, _, h => by simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, Γo, .lam x A b bi, T, h => by
    simp only [Pure.inferType] at h
    obtain ⟨B, hB, h⟩ := ok_of_bind h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨B, bi, rfl, inferType_lamMatch f _ b hB⟩
  | _ + 1, _, .bvar _, _, _ | _ + 1, _, .fvar _, _, _ | _ + 1, _, .mvar _, _, _
  | _ + 1, _, .sort _, _, _ | _ + 1, _, .const .., _, _ | _ + 1, _, .app .., _, _
  | _ + 1, _, .forallE .., _, _ | _ + 1, _, .letE .., _, _ | _ + 1, _, .lit _, _, _
  | _ + 1, _, .mdata .., _, _ | _ + 1, _, .proj .., _, _ => trivial

/-- Instantiating a bound variable with a free variable keeps `LamMatch`. Copy of
`ML-V Core/StepsCasesCase.lean:51`. -/
theorem LamMatch.inst (y : FVarId) : ∀ {e T : Expr} {d : Nat}, LamMatch e T →
    LamMatch (e.instantiate1' (.fvar y) d) (T.instantiate1' (.fvar y) d)
  | .lam x A b bi, T, d, h => by
    obtain ⟨B, bi', rfl, h⟩ := h
    exact ⟨_, bi', rfl, LamMatch.inst y h⟩
  | .bvar i, _, d, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · simp [LamMatch, Expr.liftLooseBVars']
      · trivial
  | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _
  | .app .., _, _, _ | .forallE .., _, _, _ | .letE .., _, _, _ | .lit _, _, _, _
  | .mdata .., _, _, _ | .proj .., _, _, _ => by simp [Expr.instantiate1', LamMatch]

/-- The λ□ names of the locals `xs`, as `fvar_to_name` finds them. Copy of
`ML-V Core/StepsCasesCase.lean:163`. -/
def namesOf (ls : List Local) (xs : List FVarId) : Option (List BinderName) :=
  xs.mapM fun x => (ls.find? (·.fvarId == x)).map (binderNameOf ·.userName)

/-- The body of an alternative closed over the locals `xs`, the last one innermost (`mkAlt`).
Copy of `ML-V Core/StepsCasesCase.lean:167`. -/
def altBody : List FVarId → LBTerm → LBTerm
  | [], r => r
  | x :: xs, r => _root_.toBvar x xs.length (altBody xs r)

/-- Copy of `ML-V Core/StepsCasesCase.lean:171`. -/
theorem altBody_foldl (r : LBTerm) : ∀ xs : List FVarId,
    xs.reverse.zipIdx.foldl (fun b p => _root_.toBvar p.1 p.2 b) r = altBody xs r
  | [] => rfl
  | x :: xs => by
    rw [List.reverse_cons, List.zipIdx_append, List.foldl_append, altBody_foldl r xs]
    simp [altBody]

section
variable {pc : PureCtx}

/-- `mkAlt xs body` returns the names of the locals and the body closed over them. Copy of
`ML-V Core/StepsCasesCase.lean:179`. -/
theorem mkAlt_run {xs : List FVarId} {ns : List BinderName} {body : LBTerm} {st : ErasureState}
    {tc : TravCtx} {ps : PureState} (h : namesOf tc.locals xs = some ns) :
    (mkAlt (m := PureM) xs body).runPure st tc pc ps = .ok (((ns, altBody xs body), st), ps) := by
  have hm : ∀ (ys : List FVarId) (ms : List BinderName), namesOf tc.locals ys = some ms →
      (ys.mapM (fvar_to_name (m := PureM))).runPure st tc pc ps = .ok ((ms, st), ps) := by
    intro ys
    induction ys with
    | nil => intro ms h; cases h; rfl
    | cons y ys ih =>
      intro ms h
      simp only [namesOf, List.mapM_cons, Option.bind_eq_bind] at h
      cases hf : List.find? (fun x => x.fvarId == y) tc.locals with
      | none => rw [hf] at h; cases h
      | some l =>
        rw [hf] at h
        cases hr : namesOf tc.locals ys with
        | none => simp [namesOf] at hr; simp [hr] at h
        | some ms' =>
          simp only [namesOf] at hr
          simp [hr] at h
          subst h
          rw [List.mapM_cons, runPure_bind, fvar_to_name_run hf, ok_bind']
          dsimp only
          rw [runPure_bind, ih ms' hr, ok_bind']
          rfl
  unfold mkAlt
  rw [runPure_bind, hm xs ns h, ok_bind']
  dsimp only
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [runPure_bind]
  rw [← altBody_foldl]
  rfl

end

/-- Copy of `ML-V Core/StepsCasesCase.lean:212`. -/
theorem namesOf_length {ls : List Local} : ∀ {xs : List FVarId} {ns : List BinderName},
    namesOf ls xs = some ns → ns.length = xs.length
  | [], ns, h => by cases h; rfl
  | x :: xs, ns, h => by
    simp only [namesOf, List.mapM_cons, Option.bind_eq_bind] at h
    cases hf : List.find? (fun l => l.fvarId == x) ls with
    | none => rw [hf] at h; cases h
    | some l =>
      rw [hf] at h
      cases hr : namesOf ls xs with
      | none => simp [namesOf] at hr; simp [hr] at h
      | some ms =>
        simp only [namesOf] at hr
        simp [hr] at h
        subst h
        simp [namesOf_length (show namesOf ls xs = some ms from hr)]

/-- Copy of `ML-V Core/StepsCasesCase.lean:229`. -/
theorem closedn_altBody {r : LBTerm} (hr : closedn 0 r = true) :
    ∀ xs : List FVarId, closedn xs.length (altBody xs r) = true
  | [] => hr
  | x :: xs => closedn_toBvar x _ xs.length (closedn_altBody hr xs)

/-- Copy of `ML-V Core/StepsCasesCase.lean:530`. -/
theorem ErasesDeps.altBody {cert : BoxCert} {σ : EvalEnv} {lenv : GlobalDeclarations} {r : LBTerm}
    (h : ErasesDeps cert σ lenv r) : ∀ xs, ErasesDeps cert σ lenv (Steps.altBody xs r)
  | [] => h
  | _ :: xs => ErasesDeps.toBvar (ErasesDeps.altBody h xs) xs.length

/-- The body that `lambdaMonocularOrIntro` passes on after opening a binder with `x`: the λ's
body instantiated, or the term applied to `x`. Copy of `ML-V Core/StepsCasesCase.lean:238`. -/
def openAlt (e : Expr) (x : FVarId) : Expr :=
  match e with
  | .lam _ _ b _ => b.instantiate1' (.fvar x)
  | _ => .app e (.fvar x)

/-- Copy of `ML-V Core/StepsCasesCase.lean:243`. -/
theorem lambdaMonocularOrIntro_eq {α : Type} [Inhabited α] (e T : Expr)
    (k : Expr → Expr → FVarId → EraseT PureM α) :
    lambdaMonocularOrIntro (m := PureM) e T k =
      forallMonocular (m := PureM) T fun x bt => k (openAlt e x) bt x := by
  cases e <;> rfl

/-- The local `x'` of `L ++ x' :: ls`, when `L` holds only counter variables from `k + 1` on and
`x'` is the counter's variable at `k`. -/
theorem find?_pushed {L ls : List Local} {k : Nat} {y : Name} {D : Expr}
    (hL : ∀ l ∈ L, ∃ j, k + 1 ≤ j ∧ l.fvarId = pureFVar j) :
    (L ++ ⟨pureFVar k, y, D, none⟩ :: ls).find? (·.fvarId == pureFVar k) =
      some ⟨pureFVar k, y, D, none⟩ := by
  rw [List.find?_append, List.find?_cons, (fvarId_beq_iff _ _).mpr rfl]
  have : L.find? (·.fvarId == pureFVar k) = none := by
    rw [List.find?_eq_none]
    intro l hl hb
    obtain ⟨j, hj, hjl⟩ := hL l hl
    rw [hjl] at hb
    have := pureFVar_inj ((fvarId_beq_iff _ _).mp hb)
    omega
  rw [this]
  rfl

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `lambdaOrIntroToArity e T k K` at the pure backend on a renamed alternative `e` of type `T`
with the marking `MarkAlt … k e T ê`: each binder is opened with the next variable of the counter
at the leading `Π` that `forallView?` reads (`forallMonocular_run`), to which the marking's fresh
variable is renamed (`RenOK.push`), and `K` runs on the renamed opened term with the opened
variables; whatever `K` guarantees (`Q`), given that a closed erasure of the opened marking closed
by `mkAlt` erases the marked alternative (`ErasesAlt`), holds of the run. Adapted from
`ML-V Core/StepsCasesCase.lean:420`. Reference: the branches of `MR E/Extract.v:109
erases_tCase`; DV-23. -/
theorem lambdaOrIntro_spec (hcl : ClosedDecls decls = true) {α : Type} [Inhabited α]
    {Sc : Name → Prop} (Q : α → ErasureState → PureState → Prop) :
    ∀ (k : Nat) {ls : List Local} {e T ê : Expr}, MarkAlt decls cfg ls k e T ê →
    ∀ {ρ : FVarId → FVarId} {S : FVarId → Prop} {tc : TravCtx} {ps : PureState}
      {st : ErasureState} {K : Expr → List FVarId → EraseT PureM α} {a : α} {st' : ErasureState}
      {ps' : PureState},
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ArgOK S Sc cfg decls e → FVarsIn S T →
      LamMatch e T →
      (∀ {ρ' : FVarId → FVarId} {S' : FVarId → Prop} {ls' : List Local} {e' ê' : Expr}
          {tc' : TravCtx} {ps₁ : PureState} {xs : List FVarId},
        MarkOf decls cfg ls' e' ê' → CtxOK cfg tc' → RenOK ρ' S' ls' tc'.locals ps₁.next →
        ArgOK S' Sc cfg decls e' → ps.next ≤ ps₁.next →
        (∃ L, tc'.locals = L ++ tc.locals ∧ ∀ l ∈ L, ∃ j, ps.next ≤ j ∧ l.fvarId = pureFVar j) →
        (∃ ns, namesOf tc'.locals xs = some ns) → xs.length = k →
        (∀ r ns, closedn 0 r = true →
          Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ' ê') r →
          namesOf tc'.locals xs = some ns →
          ErasesAlt noCert (evalEnvOf view cfg decls) [] k (renFV ρ ê) (ns, altBody xs r)) →
        (K (renFV ρ' e') xs).runPure st tc' ⟨decls, view⟩ ps₁ = .ok ((a, st'), ps') →
        Q a st' ps') →
      (lambdaOrIntroToArity (m := PureM) (renFV ρ e) (renFV ρ T) k K).runPure st tc
        ⟨decls, view⟩ ps = .ok ((a, st'), ps') → Q a st' ps' := by
  intro k
  induction k with
  | zero =>
    intro ls e T ê hm ρ S tc ps st K a st' ps' hctx hR he _ _ hK hrun
    cases hm with
    | done hmo =>
      rw [lambdaOrIntroToArity] at hrun
      refine hK hmo hctx hR he (Nat.le_refl _) ⟨[], rfl, fun _ h => nomatch h⟩ ⟨[], rfl⟩ rfl
        (fun r ns _ hr hns => ?_) hrun
      cases hns
      exact .done hr
  | succ k ih =>
    intro ls e T ê hm ρ S tc ps st K a st' ps' hctx hR he hT hLM hK hrun
    rw [lambdaOrIntroToArity, lambdaMonocularOrIntro_eq] at hrun
    -- both rules open one binder at the leading `Π` that `forallView?` reads
    obtain ⟨y, D, C, bi, x, es, e₁, bM, hv, hfr, hm₁, hoe, he₁, hLM₁, hlift⟩ :
        ∃ (y : Name) (D C : Expr) (bi : BinderInfo) (x : FVarId) (es : List Expr) (e₁ bM : Expr),
          forallView? decls ls T = some (y, D, C, bi) ∧ Fresh x ls es ∧
          MarkAlt decls cfg (⟨x, y, D, none⟩ :: ls) k e₁ (C.instantiate1' (.fvar x)) bM ∧
          openAlt (renFV ρ e) (pureFVar ps.next) = renFV (renExt ρ x (pureFVar ps.next)) e₁ ∧
          ArgOK (fun z => S z ∨ z = x) Sc cfg decls e₁ ∧ LamMatch e₁ (C.instantiate1' (.fvar x)) ∧
          ∀ ns tb, ErasesAlt noCert (evalEnvOf view cfg decls) [] k
              (renFV (renExt ρ x (pureFVar ps.next)) bM) (ns, tb) → closedn ns.length tb = true →
            ErasesAlt noCert (evalEnvOf view cfg decls) [] (k + 1) (renFV ρ ê)
              (binderNameOf y :: ns, _root_.toBvar (pureFVar ps.next) ns.length tb) := by
      cases hm with
      | @lam _ _ y D C bi' x b _ bM n A bi hv hfr hm₁ =>
        obtain ⟨B, bi'', rfl, hLMb⟩ := hLM
        have hv2 := hv
        simp only [forallView?, Option.some.injEq, Prod.mk.injEq] at hv2
        obtain ⟨hny, -, hBC, -⟩ := hv2
        have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
        have hR' := hR.push (n := y) (val := none) hfr hD (fun _ h => nomatch h)
        have hxb : FVarsIn (· ≠ x) b := hfr.2 b (by simp)
        have he₁ : ArgOK (fun z => S z ∨ z = x) Sc cfg decls (b.instantiate1' (.fvar x)) :=
          ⟨fvarsIn_open he.1.2, fun d hd => he.2.1 d (by rw [nameOccurs_inst_fvar] at hd; exact hd),
            NatPlain.inst_fvar he.2.2.1.2, ConstsIn_inst_fvar he.2.2.2.2⟩
        have hbMS := MarkAlt.fvarsIn hcl hm₁ hR'.supp he₁.1 (fvarsIn_open hC)
        have habs := absFV_renExt (d := 0) (fun z hz => hR.fresh z hz ps.next (Nat.le_refl _)) hbMS
        refine ⟨y, D, C, bi', x, _, _, bM, hv, hfr, hm₁, ?_, he₁,
          by rw [← hBC]; exact LamMatch.inst x hLMb, fun ns tb hE hc => ?_⟩
        · simp only [renFV, openAlt]
          rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxb]
          simp only [renFV, renExt_self]
        · simp only [renFV]
          rw [← habs]
          have := ErasesAlt.absN (pureFVar ps.next) hE 0 [(renFV ρ A, none)]
            (by rw [Nat.zero_add]; exact hc)
          rw [Nat.zero_add] at this
          rw [← hny]
          exact .lam this
      | @intro _ _ _ y D C bi' x _ bM hne hv hfr hm₁ =>
        have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
        have hR' := hR.push (n := y) (val := none) hfr hD (fun _ h => nomatch h)
        have hxe : FVarsIn (· ≠ x) e := hfr.2 e (by simp)
        have he₁ : ArgOK (fun z => S z ∨ z = x) Sc cfg decls (.app e (.fvar x)) :=
          ⟨⟨fvarsIn_mono (fun _ => .inl) he.1, .inr rfl⟩,
            fun d hd => he.2.1 d (by simpa [nameOccurs] using hd), ⟨he.2.2.1, trivial⟩,
            ⟨he.2.2.2, trivial⟩⟩
        have hbMS := MarkAlt.fvarsIn hcl hm₁ hR'.supp he₁.1 (fvarsIn_open hC)
        have habs := absFV_renExt (d := 0) (fun z hz => hR.fresh z hz ps.next (Nat.le_refl _)) hbMS
        refine ⟨y, D, C, bi', x, _, _, bM, hv, hfr, hm₁, ?_, he₁, trivial, fun ns tb hE hc => ?_⟩
        · have hren : renFV (renExt ρ x (pureFVar ps.next)) (.app e (.fvar x)) =
              .app (renFV ρ e) (.fvar (pureFVar ps.next)) := by
            simp only [renFV, renExt_self, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxe]
          rw [hren]
          cases e with
          | lam n A b bi => exact absurd rfl (hne n A b bi)
          | _ => rfl
        · simp only [renFV]
          rw [← habs]
          have := ErasesAlt.absN (pureFVar ps.next) hE 0 [(renFV ρ D, none)]
            (by rw [Nat.zero_add]; exact hc)
          rw [Nat.zero_add] at this
          exact .etaLam this
    have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
    have hv' : forallView? decls tc.locals (renFV ρ T) = some (y, renFV ρ D, renFV ρ C, bi) := by
      rw [(forallView?_ren hcl hR.supp hR.ren T hT).1, hv]; rfl
    rw [forallMonocular_run (pc := ⟨decls, view⟩) _ hv'] at hrun
    have hR' := hR.push (n := y) (val := none) hfr hD (fun _ h => nomatch h)
    have hxS := hR.not_mem hfr
    have hxC : FVarsIn (· ≠ x) C :=
      fvarsIn_mono (q := (· ≠ x)) (fun z hz (hzx : z = x) => hxS (hzx ▸ hz)) hC
    have hrenC : renFV (renExt ρ x (pureFVar ps.next)) (C.instantiate1' (.fvar x)) =
        (renFV ρ C).instantiate1' (.fvar (pureFVar ps.next)) := by
      rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxC]
      simp only [renFV, renExt_self]
    rw [hoe, ← hrenC] at hrun
    refine ih hm₁ (by exact ⟨hctx.config, hctx.fixvars⟩) hR' he₁ (fvarsIn_open hC) hLM₁ ?_ hrun
    intro ρ' S' ls' e' ê' tc' ps₁ xs hmo hctx' hR'' he' hps hL hns hlen hE hrun'
    obtain ⟨L, hLe, hLj⟩ := hL
    have hfind : tc'.locals.find? (·.fvarId == pureFVar ps.next) =
        some ⟨pureFVar ps.next, y, renFV ρ D, none⟩ := by
      rw [hLe]; exact find?_pushed hLj
    have hnames : ∀ ns, namesOf tc'.locals xs = some ns →
        namesOf tc'.locals (pureFVar ps.next :: xs) = some (binderNameOf y :: ns) := by
      intro ns h
      simp only [namesOf] at h ⊢
      simp [List.mapM_cons, hfind, h]
    refine hK hmo hctx' hR'' he' (by dsimp only at hps; omega)
      ⟨L ++ [⟨pureFVar ps.next, y, renFV ρ D, none⟩], by rw [hLe]; simp, fun l hl => ?_⟩
      (hns.elim fun ns h => ⟨_, hnames ns h⟩) (by simp [hlen]) (fun r ns hr her hns' => ?_) hrun'
    · rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨j, hj, hjl⟩ := hLj l hl
        exact ⟨j, by dsimp only at hj; omega, hjl⟩
      · simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨ps.next, Nat.le_refl _, rfl⟩
    · obtain ⟨ns₀, hns₀⟩ := hns
      rw [hnames ns₀ hns₀] at hns'
      cases hns'
      have hlen₀ := namesOf_length hns₀
      have := hlift ns₀ (altBody xs r) (hE r ns₀ hr her hns₀)
        (by rw [hlen₀]; exact closedn_altBody hr xs)
      rw [hlen₀] at this
      exact this

/-- `visitAlt (j + 1) k (replicate k keep) [] alt` at the pure backend on a renamed alternative,
with masks that keep every field and no substituted field, from `visitExpr` at `j` (`ih`): on an
alternative with the marking `MarkAlt` on the type the oracle infers for it, a successful run
erases the renamed marking under its `k` field binders (`ErasesAlt`), its body closed under them,
with erased λ□ dependencies, and grows. Adapted from `ML-V Core/StepsCasesCase.lean:539`.
Reference: the branches of the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitAlt_spec (hcl : ClosedDecls decls = true) {j : Nat}
    (ih : ∀ e, ExprSpec view cfg decls j e) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {Sc : Name → Prop} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {k : Nat} {alt T âlt : Expr} {br : List BinderName × LBTerm}
    (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc) (hR : RenOK ρ S ls tc.locals ps.next)
    (ha : ArgOK S Sc cfg decls alt) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hT : Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T)
    (hm : MarkAlt decls cfg ls k alt T âlt)
    (hrun : (visitAlt (m := PureM) (j + 1) k (Array.replicate k .keep) [] (renFV ρ alt)).runPure
      st tc ⟨decls, view⟩ ps = .ok ((br, st'), ps')) :
    ErasesAlt noCert (evalEnvOf view cfg decls) [] k (renFV ρ âlt) br ∧
      closedn br.1.length br.2 = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls br.2 ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  have hT' : Pure.inferType ⟨decls⟩ oracleFuel tc.locals [] (renFV ρ alt) = .ok (renFV ρ T) := by
    have := (inferType_ren (cx := ⟨decls⟩) hcl hR.supp hR.ren oracleFuel [] _ ha.1 (by simp)).1
    rw [hT] at this
    exact this
  rw [visitAlt, runPure_read_bind, runPure_read_bind, runPure_bind, inferType_runPure, hT'] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind'] at hrun
  dsimp only at hrun
  refine lambdaOrIntro_spec hcl (Sc := Sc) (fun br st' ps' =>
      ErasesAlt noCert (evalEnvOf view cfg decls) [] k (renFV ρ âlt) br ∧
      closedn br.1.length br.2 = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls br.2 ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps') k hm hctx hR ha
    (fvarsIn_oracle_ty hcl hR.supp ha.1 hT) (inferType_lamMatch _ _ _ hT) ?_ hrun
  intro ρ' S' ls' e' ê' tc' ps₁ xs hmo hctx' hR' he' hps _ hns hlen hE hrun'
  simp only [List.isEmpty_nil, ↓reduceIte] at hrun'
  rw [runPure_bind] at hrun'
  obtain ⟨⟨⟨r, st₁⟩, ps₂⟩, hr, hrun'⟩ := ok_of_bind hrun'
  dsimp only at hrun'
  obtain ⟨ns, hns⟩ := hns
  rw [filter_keep _ _ (by simp [hlen]), List.toList_toArray, mkAlt_run hns] at hrun'
  cases hrun'
  have ⟨her, hc0, hdeps, hgr⟩ := ih e' hctx' hR' he'.1 hsc he'.2.1 he'.2.2.1 he'.2.2.2 hok hmo hr
  refine ⟨hE r ns hc0 her hns, ?_, ErasesDeps.altBody hdeps xs,
    ⟨hgr.inv, hgr.ext, Nat.le_trans hps hgr.next, hgr.scope⟩⟩
  dsimp only
  rw [namesOf_length hns]
  exact closedn_altBody hc0 xs

end

/-! ## Loops of the pure traversal -/

section
variable {pc : PureCtx}

/-- A `for` loop over the list `L` at the pure backend whose body always continues: an invariant
`I` indexed by the processed prefix holds after every successful run. Copy of
`ML-V Core/StepsCasesCase.lean:603`. -/
theorem forIn_inv {α β : Type} {tc : TravCtx} {L : List α}
    (I : List α → β → ErasureState → PureState → Prop) (f : α → β → EraseT PureM (ForInStep β))
    (hf : ∀ pre a rest b st ps r st' ps', pre ++ a :: rest = L → I pre b st ps →
      (f a b).runPure st tc pc ps = .ok ((r, st'), ps') →
      ∃ b', r = .yield b' ∧ I (pre ++ [a]) b' st' ps') :
    ∀ (l pre : List α) (b : β) (st : ErasureState) (ps : PureState) (r : β) (st' : ErasureState)
      (ps' : PureState), pre ++ l = L → I pre b st ps →
      (forIn l b f).runPure st tc pc ps = .ok ((r, st'), ps') → I L r st' ps'
  | [], pre, b, st, ps, r, st', ps', hL, hI, h => by
    rw [List.forIn_nil] at h
    cases h
    simpa [← hL] using hI
  | a :: l, pre, b, st, ps, r, st', ps', hL, hI, h => by
    rw [List.forIn_cons, runPure_bind] at h
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, h⟩ := ok_of_bind h
    obtain ⟨b', rfl, hI'⟩ := hf pre a l b st ps x st₁ ps₁ hL hI hx
    exact forIn_inv I f hf l (pre ++ [a]) b' st₁ ps₁ r st' ps' (by simpa using hL) hI' h

/-- Copy of `ML-V Core/Frame.lean:950`. -/
theorem rco_forIn {β : Type} (r : Std.Rco Nat) (b : β) (f : Nat → β → EraseT PureM (ForInStep β)) :
    forIn r b f = forIn r.toList b f := by
  rw [← forIn'_eq_forIn r b (fun a _ acc => f a acc) f (fun _ _ _ => rfl),
    Std.Rco.forIn'_eq_forIn'_toList, forIn'_eq_forIn _ _ _ f (fun _ _ _ => rfl)]

/-- Copy of `ML-V Core/Frame.lean:955`. -/
theorem subarray_forIn {β : Type} (s : Subarray Expr) (b : β)
    (f : Expr → β → EraseT PureM (ForInStep β)) :
    forIn s b f = forIn s.toList b f := Subarray.forIn_eq_forIn_toList

/-- The loop of `visitCases` over its extra arguments is `visitAppArgs`. -/
theorem forIn_app_eq {j : Nat} {tc : TravCtx} : ∀ (l : List Expr) (b : LBTerm) (st : ErasureState)
    (ps : PureState),
    (forIn l b (fun arg r => do
        let x ← visitExpr (m := PureM) j arg
        pure (ForInStep.yield (LBTerm.app r x)))).runPure st tc pc ps =
      (visitAppArgs (m := PureM) (j + 1) b l.toArray).runPure st tc pc ps
  | [], b, st, ps => rfl
  | a :: l, b, st, ps => by
    rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray, List.forIn_cons,
      List.foldlM_cons, runPure_bind, runPure_bind, runPure_bind, runPure_bind]
    cases h : (visitExpr (m := PureM) j a).runPure st tc pc ps with
    | error err => rfl
    | ok res =>
      simp only [ok_bind']
      have := forIn_app_eq (j := j) (tc := tc) l (.app b res.1.1) res.1.2 res.2
      rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at this
      exact this

/-- The backend's `typeLevel` is the oracle's, at `oracleFuel`. Copy of
`ML-V Core/Frame.lean:343`. -/
theorem typeLevel_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.typeLevel (m := PureM) lctx ls e).run pc).run ps =
      (Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Level) | .error err => throw err).run pc).run ps) = _
  cases Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e <;> rfl

/-- `pure` returns its value, states unchanged. Copy of `ML-V Core/StepsCasesBox.lean:422`. -/
theorem runPure_pure {α : Type} {a : α} {st : ErasureState} {tc : TravCtx} {ps : PureState} :
    (Pure.pure a : EraseT PureM α).runPure st tc pc ps = .ok ((a, st), ps) := rfl

end

/-- Branches closed under their binders are closed. -/
theorem closednB_of {k : Nat} : ∀ {brs : List (List BinderName × LBTerm)},
    (∀ br ∈ brs, closedn (k + br.1.length) br.2 = true) → closednB k brs = true
  | [], _ => rfl
  | (ns, b) :: brs, h => by
    simp only [closednB, Bool.and_eq_true]
    exact ⟨h _ (.head _), closednB_of fun br hbr => h br (.tail _ hbr)⟩

/-! ## The λ□ `case` -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `visitCasesOn (f + 1) iv m ∅ none d` at the pure backend, from `visitExpr` below `f` (`ih`),
when the map `m` gives each constructor of `iv` its number of fields and its renamed alternative,
which has a marking `MarkAlt` on the type the oracle infers for it, and the machine branches are
not taken: a successful run registers `iv` and returns the λ□ `case` of its λ□ inductive on `d`,
whose branches erase the renamed markings of the alternatives under their fields' binders, closed,
with erased dependencies. Adapted from `ML-V Core/StepsCasesCase.lean:672`. Reference: the `tCase`
case of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitCasesOn_spec (hG : CoreEnv view cfg decls) {f : Nat}
    (ih : ∀ j < f, ∀ e, ExprSpec view cfg decls j e) {iv : InductiveVal}
    (hiv : findDecl decls iv.name = some (.inductInfo iv))
    (hnm : cfg.nat = .machine → iv.name ≠ ``Nat ∧ iv.name ≠ ``Int)
    {m : Std.HashMap Name (Nat × Expr)} {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {Sc : Name → Prop} {alts âlts : List Expr} {st st' : ErasureState}
    {tc : TravCtx} {ps ps' : PureState} {d r : LBTerm}
    (hm : ∀ (i : Nat) cn, iv.ctors[i]? = some cn → ∃ cv alt âlt T,
      findDecl decls cn = some (.ctorInfo cv) ∧ alts[i]? = some alt ∧ âlts[i]? = some âlt ∧
      m[cn]? = some (cv.numFields, renFV ρ alt) ∧
      Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T ∧
      MarkAlt decls cfg ls cv.numFields alt T âlt)
    (halts : ∀ alt ∈ alts, ArgOK S Sc cfg decls alt)
    (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc) (hR : RenOK ρ S ls tc.locals ps.next)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hdd : ErasesDeps noCert (evalEnvOf view cfg decls) st.gdecls d) (hcd : closedn 0 d = true)
    (hrun : (visitCasesOn (m := PureM) (f + 1) iv m ∅ none d).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ iid brs, IndIdOf (evalEnvOf view cfg decls) iv.name = some iid ∧
      r = .case (iid, iv.numParams) d brs ∧ brs.length = iv.ctors.length ∧
      (∀ (i : Nat) cn âlt br k, iv.ctors[i]? = some cn → âlts[i]? = some âlt → brs[i]? = some br →
        ctorFields (evalEnvOf view cfg decls) cn = some k →
        ErasesAlt noCert (evalEnvOf view cfg decls) [] k (renFV ρ âlt) br) ∧
      closedn 0 r = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  rw [visitCasesOn, runPure_bind, runPure_pure, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_read_bind] at hrun
  split at hrun
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).1 h1).elim
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).2 h1).elim
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨⟨indid, argmasks⟩, st₂⟩, ps₂⟩, hreg, hrun₂⟩ := ok_of_bind hrun
  clear hrun
  obtain ⟨hok₂, hext₂, hcst₂, hid, hind, hkm, hps₂⟩ := register_inductive_spec hG hctx hok hiv hreg
  subst ps₂
  have hgr₂ : Grows (evalEnvOf view cfg decls) Sc st st₂ ps ps :=
    ⟨hok₂, hext₂, Nat.le_refl _, fun c kn h h' => by rw [hcst₂, h] at h'; cases h'⟩
  dsimp only at hrun₂
  rw [runPure_bind] at hrun₂
  obtain ⟨⟨⟨⟨brs, s'⟩, st₃⟩, ps₃⟩, hloop, hrun₃⟩ := ok_of_bind hrun₂
  cases hrun₃
  have hlenm := hkm.1
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv.ctors)
    (fun pre (b : Array (List BinderName × LBTerm) × List ConstructorArgMask) st₁ ps₁ =>
      b.2 = argmasks.drop pre.length ∧ b.1.toList.length = pre.length ∧
      (∀ (i : Nat) cn âlt br k, iv.ctors[i]? = some cn → âlts[i]? = some âlt →
        b.1.toList[i]? = some br → ctorFields (evalEnvOf view cfg decls) cn = some k →
        ErasesAlt noCert (evalEnvOf view cfg decls) [] k (renFV ρ âlt) br) ∧
      (∀ br ∈ b.1.toList, closedn br.1.length br.2 = true ∧
        ErasesDeps noCert (evalEnvOf view cfg decls) st₁.gdecls br.2) ∧
      Grows (evalEnvOf view cfg decls) Sc st₂ st₁ ps ps₁) _ ?_ iv.ctors [] (#[], argmasks)
    st₂ ps _ _ _ rfl ⟨rfl, rfl, fun i _ _ br _ _ _ h => by simp at h, fun _ h => by simp at h,
      .refl hok₂⟩ hloop
  · obtain ⟨-, hlen, hE, hD, hgr⟩ := hI
    refine ⟨indid, brs.toList, hid, rfl, hlen, hE, ?_, ?_, hgr₂.trans hgr⟩
    · simp only [closedn, Bool.and_eq_true]
      exact ⟨hcd, closednB_of fun br hbr => by rw [Nat.zero_add]; exact (hD br hbr).1⟩
    · exact .case (T := iv.name) hid (ErasesInd.ext hgr.ext hind)
        (ErasesDeps.ext (LenvExt.trans hext₂ hgr.ext) hdd) fun br hbr => (hD br hbr).2
  · intro pre cn rest ⟨as₁, s₁⟩ st₁ ps₁ res st₁' ps₁' hL ⟨hs, hlen, hE, hD, hgr⟩ hb
    dsimp only at hs hlen hE hD hb
    have hk : pre.length < iv.ctors.length := by rw [← hL]; simp
    have hcn : iv.ctors[pre.length]? = some cn := by rw [← hL]; simp
    obtain ⟨cv, alt, âlt, T, hcv, halt, hâlt, hmc, hT, hma⟩ := hm _ _ hcn
    have hmask := hkm.2 pre.length cn cv hcn hcv
    rw [hs, List.drop_eq_getElem_cons (by rw [hlenm]; exact hk),
      (List.getElem?_eq_some_iff.1 hmask).2] at hb
    simp only [show ∀ (a : ConstructorArgMask) (l : List ConstructorArgMask),
      Std.Stream.next? (a :: l) = some (a, l) from fun _ _ => rfl, hmc,
      Std.HashMap.getD_empty] at hb
    rw [runPure_bind] at hb
    obtain ⟨⟨⟨br, st₄⟩, ps₄⟩, hvis, hb⟩ := ok_of_bind hb
    cases hb
    cases f with
    | zero => rw [visitAlt] at hvis; cases hvis
    | succ f =>
    have ⟨hEa, hca, hDa, hga⟩ := visitAlt_spec hG.closed (ih f (by omega)) hctx hsc
      (hR.mono (Nat.le_trans (Nat.le_refl _) hgr.next)) (halts alt (List.mem_of_getElem? halt))
      hgr.inv hT hma hvis
    refine ⟨_, rfl, by simp, by simp [hlen], ?_, ?_, hgr.trans hga⟩
    · intro i cn' âlt' br' k hi hai hbi hk'
      rw [Array.toList_push] at hbi
      rcases Nat.lt_or_ge i pre.length with hlt | hge
      · rw [List.getElem?_append_left (by omega)] at hbi
        exact hE i cn' âlt' br' k hi hai hbi hk'
      · rw [List.getElem?_append_right (by omega)] at hbi
        obtain ⟨hi0, rfl⟩ := List.getElem?_eq_some_iff.1 hbi
        simp only [List.length_singleton] at hi0
        have hip : i = pre.length := by omega
        subst hip
        rw [hcn] at hi; cases hi
        rw [hâlt] at hai; cases hai
        have : k = cv.numFields := by
          simp only [ctorFields, evalEnvOf] at hk'
          rw [hcv] at hk'
          cases hk'; rfl
        subst this
        simpa using hEa
    · intro br' hbr
      rw [Array.toList_push] at hbr
      rcases List.mem_append.1 hbr with hbr | hbr
      · exact ⟨(hD br' hbr).1, ErasesDeps.ext hga.ext (hD br' hbr).2⟩
      · simp only [List.mem_singleton] at hbr
        subst hbr
        exact ⟨hca, hDa⟩

end

end Steps

end EraseProof
