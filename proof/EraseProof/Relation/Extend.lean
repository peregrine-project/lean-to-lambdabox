import EraseProof.Bridge.Cases
import EraseProof.Bridge.ProgEnv
import EraseProof.Bridge.Basic

/-!
# Moving the erasure relation to the program

An erasure in the evaluation environment of a dependency-closed sub-environment `decls` of the
program `P` is an erasure in the evaluation environment of `P` (`Erases.extend`): every constant
the relation reads is in `decls`, and `decls` and `P` agree on everything the relation reads about
it, in particular on whether it is a recognized `casesOn` (`Extend.casesOn?_agree`, which needs the
block of a recursor of `decls` in `decls`).
-/

open Lean Erasure

namespace EraseProof

namespace Extend

variable {D P : List ConstantInfo}

/-- A declaration of the sub-environment is the program's. -/
theorem findDecl_sub (hsub : SubEnv D P) {c : Name} {ci : ConstantInfo}
    (h : findDecl D c = some ci) : findDecl P c = some ci := by
  obtain ⟨hm, rfl⟩ := findDecl_eq_some h
  exact hsub ci hm

/-- The sub-environment and the program agree on the names of the sub-environment. -/
theorem findDecl_agree (hsub : SubEnv D P) {c : Name} (h : (findDecl D c).isSome) :
    findDecl D c = findDecl P c := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 h
  rw [hci, findDecl_sub hsub hci]

theorem ctorAlts_congr : ∀ {cs : List Name}, (∀ x ∈ cs, findDecl D x = findDecl P x) →
    ctorAlts D cs = ctorAlts P cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [ctorAlts]
    rw [show findConst D c = findConst P c from h c List.mem_cons_self,
      ctorAlts_congr fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem blockCtorCount_congr : ∀ {ts : List Name}, (∀ x ∈ ts, findDecl D x = findDecl P x) →
    blockCtorCount D ts = blockCtorCount P ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [blockCtorCount]
    rw [show findConst D t = findConst P t from h t List.mem_cons_self,
      blockCtorCount_congr fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The recognizer answers the same in two lists that agree on what it reads. -/
theorem casesInfo?_congr {n : Name} (h1 : findDecl D n = findDecl P n)
    (h : ∀ T, n = .str T "casesOn" → findDecl D T = findDecl P T ∧
      findDecl D (mkRecName T) = findDecl P (mkRecName T) ∧
      ∀ I R, findDecl P T = some (.inductInfo I) → findDecl P (mkRecName T) = some (.recInfo R) →
        (∀ x ∈ I.ctors, findDecl D x = findDecl P x) ∧ ∀ x ∈ R.all, findDecl D x = findDecl P x) :
    casesInfo? D n = casesInfo? P n := by
  unfold casesInfo?
  split
  next T =>
    obtain ⟨h2, h3, h4⟩ := h T rfl
    rw [show findConst D (.str T "casesOn") = findConst P (.str T "casesOn") from h1,
      show findConst D T = findConst P T from h2,
      show findConst D (mkRecName T) = findConst P (mkRecName T) from h3]
    split
    next d I R _ hI hR =>
      obtain ⟨hc, ha⟩ := h4 I R hI hR
      rw [ctorAlts_congr hc, blockCtorCount_congr fun x hx => ha x (List.mem_of_mem_take hx)]
    next => rfl
  next => rfl

/-- What the recognizer reads when it answers: `n` is `T.casesOn`, a definition, `T` an inductive,
`T.rec` a recursor whose block contains `T`. -/
theorem casesInfo?_reads {X : List ConstantInfo} {n : Name} {ci : CasesInfo}
    (h : casesInfo? X n = some ci) :
    ∃ T d I R, n = .str T "casesOn" ∧ ci.indName = T ∧ findDecl X n = some (.defnInfo d) ∧
      findDecl X T = some (.inductInfo I) ∧ findDecl X (mkRecName T) = some (.recInfo R) ∧
      T ∈ R.all := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j _ _ _ hj _ _ _ =>
        split at h
        next =>
          cases h
          exact ⟨T, d, I, R, rfl, rfl, hd, hI, hR, List.isSome_idxOf?.1 (by rw [hj]; rfl)⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-! ## Constants of terms -/

section ConstsIn
variable {p : Name → Prop}

theorem ConstsIn_foldl : ∀ {f : Expr} {as : List Expr},
    ConstsIn p (as.foldl .app f) ↔ ConstsIn p f ∧ ∀ a ∈ as, ConstsIn p a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, ConstsIn_foldl]
    simp only [ConstsIn, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem ConstsIn_mkAppN {f : Expr} {as : List Expr} :
    ConstsIn p (mkAppN f as.toArray) ↔ ConstsIn p f ∧ ∀ a ∈ as, ConstsIn p a := by
  rw [mkAppN_toArray, ConstsIn_foldl]

theorem ConstsIn_peelLams : ∀ {k : Nat} {v b : Expr}, peelLams k v = some b → ConstsIn p v →
    ConstsIn p b
  | 0, _, _, h, hv => by cases h; exact hv
  | k + 1, .lam _ _ v _, b, h, hv => ConstsIn_peelLams (k := k) h hv.2
  | _ + 1, .bvar _, _, h, _ | _ + 1, .fvar _, _, h, _ | _ + 1, .mvar _, _, h, _
  | _ + 1, .sort _, _, h, _ | _ + 1, .const .., _, h, _ | _ + 1, .app .., _, h, _
  | _ + 1, .forallE .., _, h, _ | _ + 1, .letE .., _, h, _ | _ + 1, .lit _, _, h, _
  | _ + 1, .mdata .., _, h, _ | _ + 1, .proj .., _, h, _ => by cases h

theorem ConstsIn_getAppFn : ∀ {e : Expr}, ConstsIn p e → ConstsIn p e.getAppFn
  | .app f _, h => ConstsIn_getAppFn (e := f) h.1
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => h

theorem ConstsIn_lift : ∀ {e : Expr} {s d : Nat}, ConstsIn p e →
    ConstsIn p (e.liftLooseBVars' s d)
  | .bvar _, _, _, _ => trivial
  | .app f a, _, _, h => ⟨ConstsIn_lift (e := f) h.1, ConstsIn_lift (e := a) h.2⟩
  | .lam _ t b _, _, _, h | .forallE _ t b _, _, _, h =>
    ⟨ConstsIn_lift (e := t) h.1, ConstsIn_lift (e := b) h.2⟩
  | .letE _ t v b _, _, _, h =>
    ⟨ConstsIn_lift (e := t) h.1, ConstsIn_lift (e := v) h.2.1, ConstsIn_lift (e := b) h.2.2⟩
  | .mdata _ e, _, _, h => ConstsIn_lift (e := e) h
  | .proj _ _ e, _, _, h => ⟨h.1, ConstsIn_lift (e := e) h.2⟩
  | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h | .const .., _, _, h
  | .lit _, _, _, h => h

theorem ConstsIn_instantiate1' {a : Expr} (ha : ConstsIn p a) : ∀ {e : Expr} {d : Nat},
    ConstsIn p e → ConstsIn p (e.instantiate1' a d)
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact ConstsIn_lift ha
      · trivial
  | .app f b, _, h => ⟨ConstsIn_instantiate1' ha (e := f) h.1, ConstsIn_instantiate1' ha (e := b) h.2⟩
  | .lam _ t b _, _, h | .forallE _ t b _, _, h =>
    ⟨ConstsIn_instantiate1' ha (e := t) h.1, ConstsIn_instantiate1' ha (e := b) h.2⟩
  | .letE _ t v b _, _, h =>
    ⟨ConstsIn_instantiate1' ha (e := t) h.1, ConstsIn_instantiate1' ha (e := v) h.2.1,
      ConstsIn_instantiate1' ha (e := b) h.2.2⟩
  | .mdata _ e, _, h => ConstsIn_instantiate1' ha (e := e) h
  | .proj _ _ e, _, h => ⟨h.1, ConstsIn_instantiate1' ha (e := e) h.2⟩
  | .fvar _, _, h | .mvar _, _, h | .sort _, _, h | .const .., _, h | .lit _, _, h => h

theorem ConstsIn_instLevels {ps : List Name} {us : List Level} : ∀ {e : Expr}, ConstsIn p e →
    ConstsIn p (Pure.instLevels ps us e)
  | .app f a, h => ⟨ConstsIn_instLevels (e := f) h.1, ConstsIn_instLevels (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨ConstsIn_instLevels (e := t) h.1, ConstsIn_instLevels (e := b) h.2⟩
  | .letE _ t v b _, h =>
    ⟨ConstsIn_instLevels (e := t) h.1, ConstsIn_instLevels (e := v) h.2.1,
      ConstsIn_instLevels (e := b) h.2.2⟩
  | .mdata _ e, h => ConstsIn_instLevels (e := e) h
  | .proj _ _ e, h => ⟨h.1, ConstsIn_instLevels (e := e) h.2⟩
  | .const .., h => h
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lit _, h => h

theorem ConstsIn_piInst : ∀ {as : List Expr} {ty ty' : Expr}, piInst as ty = some ty' →
    (∀ a ∈ as, ConstsIn p a) → ConstsIn p ty → ConstsIn p ty'
  | [], _, _, h, _, hty => by cases h; exact hty
  | a :: as, .forallE _ _ b _, _, h, has, hty =>
    ConstsIn_piInst (as := as) h (fun x hx => has x (List.mem_cons_of_mem _ hx))
      (ConstsIn_instantiate1' (has a List.mem_cons_self) hty.2)
  | _ :: _, .bvar _, _, h, _, _ | _ :: _, .fvar _, _, h, _, _ | _ :: _, .mvar _, _, h, _, _
  | _ :: _, .sort _, _, h, _, _ | _ :: _, .const .., _, h, _, _ | _ :: _, .app .., _, h, _, _
  | _ :: _, .lam .., _, h, _, _ | _ :: _, .letE .., _, h, _, _ | _ :: _, .lit _, _, h, _, _
  | _ :: _, .mdata .., _, h, _, _ | _ :: _, .proj .., _, h, _, _ => by cases h

theorem ConstsIn_lamsOf : ∀ {k : Nat} {ty body e : Expr}, lamsOf k ty body = some e →
    ConstsIn p ty → ConstsIn p body → ConstsIn p e
  | 0, _, _, _, h, _, hb => by cases h; exact hb
  | k + 1, .forallE _ d b _, body, e, h, hty, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    exact ⟨hty.1, ConstsIn_lamsOf (k := k) h' hty.2 hb⟩
  | _ + 1, .bvar _, _, _, h, _, _ | _ + 1, .fvar _, _, _, h, _, _ | _ + 1, .mvar _, _, _, h, _, _
  | _ + 1, .sort _, _, _, h, _, _ | _ + 1, .const .., _, _, h, _, _ | _ + 1, .app .., _, _, h, _, _
  | _ + 1, .lam .., _, _, h, _, _ | _ + 1, .letE .., _, _, h, _, _ | _ + 1, .lit _, _, _, h, _, _
  | _ + 1, .mdata .., _, _, h, _, _ | _ + 1, .proj .., _, _, h, _, _ => by cases h

end ConstsIn

/-- Whether a constant of a dependency-closed sub-environment is a recognized `casesOn`, and of
which inductive, is the same in the program: when either recognizes it, the recursor `T.rec` is in
`D` (in `D` by the recognizer; in `P`, as the head of the value, which `D` reads when it does not
recognize the constant), hence by `DepClosed` its block, `T` and `T`'s constructors. -/
theorem casesOn?_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) (a a' : ConstantInfo → Bool) :
    EvalEnv.casesOn? ⟨D, a⟩ c = EvalEnv.casesOn? ⟨P, a'⟩ c := by
  -- From `T.rec ∈ D` the recognizer reads the same in `D` and `P`, and `T ∈ D`.
  have key : ∀ T R, c = .str T "casesOn" → findDecl D (mkRecName T) = some (.recInfo R) →
      T ∈ R.all → casesInfo? D c = casesInfo? P c ∧ (findDecl D T).isSome := by
    intro T R hT hR hTR
    obtain ⟨-, -, -, -, hrall⟩ := hcl _ (findDecl_eq_some hR).1
    have hTD : (findDecl D T).isSome := hrall R rfl T hTR
    refine ⟨casesInfo?_congr (findDecl_agree hsub hc) fun T' hT' => ?_, hTD⟩
    rw [hT, Name.str.injEq] at hT'
    obtain ⟨rfl, -⟩ := hT'
    refine ⟨findDecl_agree hsub hTD, findDecl_agree hsub (by rw [hR]; rfl),
      fun I R' hI hR' => ?_⟩
    rw [← findDecl_agree hsub hTD] at hI
    rw [← findDecl_agree hsub (by rw [hR]; rfl), hR] at hR'
    cases hR'
    obtain ⟨-, -, hctors, -, -⟩ := hcl _ (findDecl_eq_some hI).1
    exact ⟨fun x hx => findDecl_agree hsub (hctors I rfl x hx),
      fun x hx => findDecl_agree hsub (hrall R rfl x hx)⟩
  have hci : casesInfo? D c = casesInfo? P c ∧
      ∀ ci, casesInfo? P c = some ci → (findDecl D ci.indName).isSome := by
    cases hD : casesInfo? D c with
    | some ci =>
      obtain ⟨T, d, I, R, hT, hci, -, -, hR, hTR⟩ := casesInfo?_reads hD
      obtain ⟨heq, hTD⟩ := key T R hT hR hTR
      rw [← heq, hD]
      refine ⟨rfl, fun ci' h => ?_⟩
      cases h
      rw [hci]; exact hTD
    | none =>
      cases hP : casesInfo? P c with
      | none => exact ⟨rfl, fun _ h => nomatch h⟩
      | some ci =>
        obtain ⟨T, d, I, R, hT, hci, hd, hI, hR, hTR⟩ := casesInfo?_reads hP
        -- `D` does not recognize `c`, so it reads `c`'s value, whose head is `T.rec`.
        have hσ : EvalEnv.casesOn? ⟨P, a'⟩ c = some I := by
          unfold EvalEnv.casesOn?
          rw [hP]; dsimp only; rw [hci, hI]
        obtain ⟨d', R', -, -, -, body, args, -, hd', -, hR', -, -, -, -, -, -, -, hb, hbody, -⟩ :=
          casesOn_shape hσ
        change findDecl P c = _ at hd'
        rw [hd] at hd'
        cases hd'
        have hdD : findDecl D c = some (.defnInfo d) := by rw [findDecl_agree hsub hc, hd]
        have hread : ReadExpr D (.defnInfo d) d.value := by
          refine .inr (.inl ⟨d, rfl, rfl, ?_⟩)
          have hdn : d.name = c := (findDecl_eq_some hdD).2
          rw [hdn]
          unfold EvalEnv.casesOn?
          dsimp only
          rw [hD]; rfl
        obtain ⟨hreads, -⟩ := hcl _ (findDecl_eq_some hdD).1
        have hhead := (ConstsIn_mkAppN.1 (hbody ▸ ConstsIn_peelLams hb (hreads _ hread))).1
        have hIT : I.name = T := (findDecl_eq_some hI).2
        rw [hIT] at hR'
        have hRD : (findDecl D (mkRecName T)).isSome := by
          rw [← (findDecl_eq_some hR').2]; exact hhead
        rw [findDecl_agree hsub hRD, hR] at hRD
        have hRD' : findDecl D (mkRecName T) = some (.recInfo R) := by
          rw [findDecl_agree hsub (by rw [← (findDecl_eq_some hR').2]; exact hhead), hR]
        rw [(key T R hT hRD' hTR).1, hP] at hD
        cases hD
  unfold EvalEnv.casesOn?
  dsimp only
  rw [hci.1]
  split
  next ci h => rw [findDecl_agree hsub (hci.2 ci h)]
  next => rfl

variable {a : ConstantInfo → Bool}

/-- Constructor and `casesOn` arities agree on the sub-environment's names. -/
theorem specialArity_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : specialArity ⟨D, a⟩ c = specialArity ⟨P, a⟩ c := by
  unfold specialArity
  rw [casesOn?_agree hsub hcl hc a a]
  dsimp only
  rw [findDecl_agree hsub hc]

/-- δ agrees on the sub-environment's names. -/
theorem unfold?_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : EvalEnv.unfold? ⟨D, a⟩ c = EvalEnv.unfold? ⟨P, a⟩ c := by
  unfold EvalEnv.unfold?
  rw [casesOn?_agree hsub hcl hc a a]
  dsimp only
  rw [findDecl_agree hsub hc]

/-- Evident propositions agree on terms whose constants are in the sub-environment. -/
theorem EvidentProp_agree (hsub : SubEnv D P) (x : Expr)
    (h : ConstsIn (fun c => (findDecl D c).isSome) x) : EvidentProp D x = EvidentProp P x := by
  induction x with
  | forallE _ _ b _ _ ihb => simp only [EvidentProp]; exact ihb h.2
  | mdata _ e ih => simp only [EvidentProp]; exact ih h
  | _ =>
    have hh := ConstsIn_getAppFn h
    simp only [EvidentProp]
    revert hh
    generalize Expr.getAppFn _ = g
    intro hh
    cases g <;> try rfl
    simp only [ConstsIn] at hh
    dsimp only
    rw [findDecl_agree hsub hh]

/-- Atoms agree on the sub-environment's names. -/
theorem isAtom_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : EvalEnv.isAtom ⟨D, a⟩ c = EvalEnv.isAtom ⟨P, a⟩ c := by
  unfold EvalEnv.isAtom
  rw [casesOn?_agree hsub hcl hc a a, unfold?_agree hsub hcl hc]
  dsimp only
  cases hD : findDecl D c with
  | none => rw [hD] at hc; cases hc
  | some ci =>
    rw [← findDecl_agree hsub hc, hD]
    dsimp only
    obtain ⟨hreads, -⟩ := hcl ci (findDecl_eq_some hD).1
    rw [EvidentProp_agree hsub _ (hreads _ (.inl rfl))]

/-- Special spines of the program whose head is in the sub-environment are special there. -/
theorem specialSpine_of_agree (hsub : SubEnv D P) (hcl : DepClosed D) {f : Expr}
    (hf : ConstsIn (fun c => (findDecl D c).isSome) f) (h : SpecialSpine ⟨P, a⟩ f) :
    SpecialSpine ⟨D, a⟩ f := by
  obtain ⟨c, us, hfn, hs⟩ := h
  have hc : (findDecl D c).isSome := by
    have := ConstsIn_getAppFn hf
    rw [hfn] at this
    exact this
  refine ⟨c, us, hfn, ?_⟩
  dsimp only at hs ⊢
  rw [findDecl_agree hsub hc, casesOn?_agree hsub hcl hc a a]
  exact hs

theorem IndIdOf_sub (hsub : SubEnv D P) {T : Name} {iid : InductiveId}
    (h : IndIdOf ⟨D, a⟩ T = some iid) : IndIdOf ⟨P, a⟩ T = some iid := by
  unfold IndIdOf at h ⊢
  dsimp only at h ⊢
  split at h
  next iv hT => rw [findDecl_sub hsub hT]; exact h
  next => cases h

theorem ctorFields_sub (hsub : SubEnv D P) {c : Name} {k : Nat}
    (h : ctorFields ⟨D, a⟩ c = some k) : ctorFields ⟨P, a⟩ c = some k := by
  unfold ctorFields at h ⊢
  dsimp only at h ⊢
  split at h
  next cv hc => rw [findDecl_sub hsub hc]; exact h
  next => cases h

/-- The η-expansion of a spine of the sub-environment is the program's, and its constants are in
the sub-environment. -/
theorem etaSpine?_sub (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name} {us : List Level}
    {as : List Expr} {e' : Expr} (h : EvalEnv.etaSpine? ⟨D, a⟩ c us as = some e')
    (hc : ConstsIn (fun c => (findDecl D c).isSome) (mkAppN (.const c us) as.toArray)) :
    EvalEnv.etaSpine? ⟨P, a⟩ c us as = some e' ∧ ConstsIn (fun c => (findDecl D c).isSome) e' := by
  have hcD : (findDecl D c).isSome := (ConstsIn_mkAppN.1 hc).1
  refine ⟨?_, ?_⟩
  · unfold EvalEnv.etaSpine? at h ⊢
    dsimp only at h ⊢
    rw [← findDecl_agree hsub hcD, ← specialArity_agree hsub hcl hcD]
    exact h
  · unfold EvalEnv.etaSpine? at h
    dsimp only at h
    split at h
    next ci ar hci _ =>
      split at h
      next =>
        obtain ⟨ty, hty, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨hreads, -⟩ := hcl ci (findDecl_eq_some hci).1
        have has := (ConstsIn_mkAppN.1 hc).2
        refine ConstsIn_lamsOf h (ConstsIn_piInst hty has
          (ConstsIn_instLevels (hreads _ (.inl rfl)))) (ConstsIn_mkAppN.2 ⟨hcD, fun x hx => ?_⟩)
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact ConstsIn_lift (has y hy)
        · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
          trivial
      next => cases h
    next => cases h

end Extend

open Extend in
/-- Moving the relation from a dependency-closed sub-environment to the program (the final
theorem's last step): the relation reads, about the constants of the term, only what `decls` and
`P` agree on. Reference: `erases_extends` (`MR E/ESubstitution.v:73`), weakening of the global
environment. -/
theorem Erases.extend {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
    {decls P : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr} {tb : LBTerm}
    (hsub : SubEnv decls P) (hcl : DepClosed decls)
    (hc : ConstsIn (fun c => (findDecl decls c).isSome) e)
    (h : Erases E B lps (evalEnvOf view cfg decls) Γ Δ e tb) :
    Erases E B lps (evalEnvOf view cfg P) Γ Δ e tb := by
  have mem : ∀ {l : List Expr} {i : Nat} {x : Expr}, l[i]? = some x → x ∈ l :=
    fun h => List.mem_of_getElem? h
  refine Erases.rec
    (motive_1 := fun Γ Δ e tb _ => ConstsIn (fun c => (findDecl decls c).isSome) e →
      Erases E B lps (evalEnvOf view cfg P) Γ Δ e tb)
    (motive_2 := fun Γ Δ k e br _ => ConstsIn (fun c => (findDecl decls c).isSome) e →
      ErasesAlt E B lps (evalEnvOf view cfg P) Γ Δ k e br)
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?mdata ?box ?done ?alam ?intro h hc
  case bvar => intros; exact .bvar
  case fvar => intros; exact .fvar
  case lam => intro _ _ _ _ _ _ _ _ _ hA hAt _ ih hC; exact .lam hA hAt (ih hC.2)
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv hvt _ _ ihv ihb hC
    exact .letE hv hvt (ihv hC.2.1) (ihb hC.2.2)
  case app =>
    intro _ _ _ _ _ _ _ hns _ _ ihf iha hC
    exact .app (fun hs => hns (specialSpine_of_agree hsub hcl hC.1 hs)) (ihf hC.1) (iha hC.2)
  case const =>
    intro c _ _ _ _ hat hsa hC
    refine .const ?_ ?_
    · exact (isAtom_agree (a := axiomatized view cfg) hsub hcl hC).symm.trans hat
    · exact (specialArity_agree (a := axiomatized view cfg) hsub hcl hC).symm.trans hsa
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih hC
    have has := (ConstsIn_mkAppN.1 hC).2
    exact .ctor (findDecl_sub hsub hcv) hnp (IndIdOf_sub hsub hid) hle hlen
      fun i a a' ha ha' => ih i a a' ha ha' (has a (mem ha))
  case cases =>
    intro c iv _ _ _ _ _ _ _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe hC
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hC
    have hco' : (evalEnvOf view cfg P).casesOn? c = some iv :=
      (casesOn?_agree hsub hcl hcD _ _).symm.trans hco
    refine .cases hco' hnr hss (IndIdOf_sub hsub hid) hpre halts (ihm (has _ (by simp))) hbrs
      (fun i cn h => ?_) (fun i cn alt br k h1 h2 h3 h4 => ?_) hlex
      (fun i a a' ha ha' => ihe i a a' ha ha' (has a (by simp [mem ha])))
    · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hcf i cn h)
      exact (ctorFields_sub (a := axiomatized view cfg) hsub hk).symm ▸ rfl
    · obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (hcf i cn h1)
      have := (ctorFields_sub hsub hk').symm.trans h4
      cases this
      exact iha i cn alt br k h1 h2 h3 hk' (has alt (by simp [mem h2]))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ _ _ extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe hC
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hC
    have hco' : (evalEnvOf view cfg P).casesOn? c = some iv :=
      (casesOn?_agree hsub hcl hcD _ _).symm.trans hco
    exact .casesReduced hco' hfe hcs (findDecl_sub hsub hcv) hidx hpre (iha (has alt (by simp)))
      hlex fun i a a' ha ha' => ihe i a a' ha ha' (has a (by simp [mem ha]))
  case eta =>
    intro _ _ _ _ _ _ _ _ heta _ ih hC
    obtain ⟨heta', hC'⟩ := etaSpine?_sub hsub hcl heta hC
    exact .eta heta' (ih hC')
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih hC
    exact .proj hss (IndIdOf_sub hsub hid) (findDecl_sub hsub hS) hsort (ih hC.2)
  case litZero => intro _ _ _ _ hid _; exact .litZero (IndIdOf_sub hsub hid)
  case litSucc => intro _ _ _ _ _ _ hid _ ih hC; exact .litSucc (IndIdOf_sub hsub hid) (ih hC)
  case quotMk =>
    intros; rename_i hcq hk _ hlex _ iha ihe hC
    obtain ⟨-, has⟩ := ConstsIn_mkAppN.1 hC
    exact .quotMk (findDecl_sub hsub hcq) hk (iha (has _ (by simp))) hlex
      fun i a a' ha ha' => ihe i a a' ha ha' (has a (by simp [mem ha]))
  case quotLift =>
    intros; rename_i hcq hk _ _ hlex _ ihf ihq ihe hC
    obtain ⟨-, has⟩ := ConstsIn_mkAppN.1 hC
    exact .quotLift (findDecl_sub hsub hcq) hk (ihf (has _ (by simp))) (ihq (has _ (by simp)))
      hlex fun i a a' ha ha' => ihe i a a' ha ha' (has a (by simp [mem ha]))
  case mdata => intro _ _ _ _ _ _ _ ih hC; exact .mdata (ih hC)
  case box => intro _ _ _ _ hb _; exact .box hb
  case done => intro _ _ _ _ _ _ ih hC; exact .done (ih hC)
  case alam => intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih hC; exact .lam hA hAt (ih hC.2)
  case intro =>
    intro _ _ _ _ _ _ _ _ _ _ _ he hty _ ih hC
    exact .intro he hty (ih ⟨ConstsIn_lift hC, trivial⟩)


end EraseProof
