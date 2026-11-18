import EraseProof.Spec

/-!
# Restricting evaluation to a dependency-closed sub-environment

An evaluation in the program `P` of a term whose constants lie in a dependency-closed
sub-environment `decls` is an evaluation in `decls`, and the constants of its result lie in
`decls` (`SrcEval.restrict`). Every rule reads, about a constant or the structure of a projection
of the term, only what `decls` and `P` agree on, and the terms it moves into the result come from
the term, from a value `decls` reads (`DepClosed`) marked as over `decls`, or from the
evaluation's own frozen placeholders. The constants are counted outside the domains of λs
(`BodyConstsIn`): an `eta`-marked λ has the domain the oracle infers, which no rule reads.
-/

open Lean Erasure

namespace EraseProof

/-- `decls` is closed under what the pure traversal and the recognizer read: the constants of the
expressions the traversal reads (`ReadExpr`), the block members (`ConstantInfo.all`), the
constructors of an inductive, the inductive of a constructor, and the block of a recursor
(`RecursorVal.all`, which `Erasure.casesInfo?` reads). Port of `ML-V Spec.lean:1075`. Reference:
the closure property of `MR E/ErasureFunction.v:1602 erase_global_deps`. -/
def DepClosed (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, (∀ x, ReadExpr decls ci x → ConstsIn (fun c => (findDecl decls c).isSome) x) ∧
    (∀ n ∈ ci.all, (findDecl decls n).isSome) ∧
    (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, (findDecl decls n).isSome) ∧
    (∀ cv, ci = .ctorInfo cv → (findDecl decls cv.induct).isSome) ∧
    (∀ r, ci = .recInfo r → ∀ n ∈ r.all, (findDecl decls n).isSome)

/-- Every constant of `e` outside the domains of its λs, and the structure of every projection of
`e`, satisfies `p` (`ConstsIn` without the λ domains, which the source semantics never reads).
Reference: `term_global_deps` (`MR E/EAstUtils.v:406`), which has no domains. -/
def BodyConstsIn (p : Name → Prop) : Expr → Prop
  | .const c _ => p c
  | .app f a => BodyConstsIn p f ∧ BodyConstsIn p a
  | .lam _ _ b _ => BodyConstsIn p b
  | .forallE _ t b _ => BodyConstsIn p t ∧ BodyConstsIn p b
  | .letE _ t v b _ => BodyConstsIn p t ∧ BodyConstsIn p v ∧ BodyConstsIn p b
  | .mdata _ e => BodyConstsIn p e
  | .proj S _ e => p S ∧ BodyConstsIn p e
  | _ => True

namespace Restrict

/-! ## Constants of terms -/

section Consts
variable {p : Name → Prop}

/-- The head of a term satisfies `ConstsIn` if the term does. Port of
`ML-V Relation/Extend.lean:121`. -/
theorem ConstsIn_getAppFn : ∀ {e : Expr}, ConstsIn p e → ConstsIn p e.getAppFn
  | .app f _, h => ConstsIn_getAppFn (e := f) h.1
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => h

/-- A body under peeled λs satisfies `ConstsIn` if the term does. Port of
`ML-V Relation/Extend.lean:112`. -/
theorem ConstsIn_peelLams : ∀ {k : Nat} {v b : Expr}, peelLams k v = some b → ConstsIn p v →
    ConstsIn p b
  | 0, _, _, h, hv => by cases h; exact hv
  | k + 1, .lam _ _ v _, b, h, hv => ConstsIn_peelLams (k := k) h hv.2
  | _ + 1, .bvar _, _, h, _ | _ + 1, .fvar _, _, h, _ | _ + 1, .mvar _, _, h, _
  | _ + 1, .sort _, _, h, _ | _ + 1, .const .., _, h, _ | _ + 1, .app .., _, h, _
  | _ + 1, .forallE .., _, h, _ | _ + 1, .letE .., _, h, _ | _ + 1, .lit _, _, h, _
  | _ + 1, .mdata .., _, h, _ | _ + 1, .proj .., _, h, _ => by cases h

/-- The head of a term's `spine` satisfies `ConstsIn` if the term does. Reference: none. -/
theorem ConstsIn_spine : ∀ {e : Expr}, ConstsIn p e → ConstsIn p (spine e).1
  | .app f _, h => by simp only [spine]; exact ConstsIn_spine (e := f) h.1
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => h

/-- `ConstsIn` gives `BodyConstsIn`. Reference: none. -/
theorem BodyConstsIn.of_constsIn : ∀ {e : Expr}, ConstsIn p e → BodyConstsIn p e
  | .app f a, h => ⟨of_constsIn (e := f) h.1, of_constsIn (e := a) h.2⟩
  | .lam _ _ b _, h => of_constsIn (e := b) h.2
  | .forallE _ t b _, h => ⟨of_constsIn (e := t) h.1, of_constsIn (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨of_constsIn (e := t) h.1, of_constsIn (e := v) h.2.1,
      of_constsIn (e := b) h.2.2⟩
  | .mdata _ e, h => of_constsIn (e := e) h
  | .proj _ _ e, h => ⟨h.1, of_constsIn (e := e) h.2⟩
  | .const .., h => h
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ => trivial

/-- `BodyConstsIn` of a left fold of applications. Port of `ML-V Relation/Extend.lean:101`. -/
theorem BodyConstsIn_foldl : ∀ {f : Expr} {as : List Expr},
    BodyConstsIn p (as.foldl .app f) ↔ BodyConstsIn p f ∧ ∀ a ∈ as, BodyConstsIn p a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, BodyConstsIn_foldl]
    simp only [BodyConstsIn, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `BodyConstsIn` of an application spine. Port of `ML-V Relation/Extend.lean:108`. -/
theorem BodyConstsIn_mkAppN {f : Expr} {as : List Expr} :
    BodyConstsIn p (mkAppN f as.toArray) ↔ BodyConstsIn p f ∧ ∀ a ∈ as, BodyConstsIn p a := by
  rw [show mkAppN f as.toArray = as.foldl .app f by simp only [mkAppN, List.foldl_toArray]; rfl,
    BodyConstsIn_foldl]

/-- The head of a term satisfies `BodyConstsIn` if the term does. Port of
`ML-V Relation/Extend.lean:121`. -/
theorem BodyConstsIn_getAppFn : ∀ {e : Expr}, BodyConstsIn p e → BodyConstsIn p e.getAppFn
  | .app f _, h => BodyConstsIn_getAppFn (e := f) h.1
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => h

/-- Lifting keeps `BodyConstsIn`. Port of `ML-V Relation/Extend.lean:126`. -/
theorem BodyConstsIn_lift : ∀ {e : Expr} {s d : Nat}, BodyConstsIn p e →
    BodyConstsIn p (e.liftLooseBVars' s d)
  | .bvar _, _, _, _ => trivial
  | .app f a, _, _, h => ⟨BodyConstsIn_lift (e := f) h.1, BodyConstsIn_lift (e := a) h.2⟩
  | .lam _ _ b _, _, _, h => BodyConstsIn_lift (e := b) h
  | .forallE _ t b _, _, _, h => ⟨BodyConstsIn_lift (e := t) h.1, BodyConstsIn_lift (e := b) h.2⟩
  | .letE _ t v b _, _, _, h =>
    ⟨BodyConstsIn_lift (e := t) h.1, BodyConstsIn_lift (e := v) h.2.1,
      BodyConstsIn_lift (e := b) h.2.2⟩
  | .mdata _ e, _, _, h => BodyConstsIn_lift (e := e) h
  | .proj _ _ e, _, _, h => ⟨h.1, BodyConstsIn_lift (e := e) h.2⟩
  | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h | .const .., _, _, h
  | .lit _, _, _, h => h

/-- Instantiation keeps `BodyConstsIn`. Port of `ML-V Relation/Extend.lean:139`. -/
theorem BodyConstsIn_instantiate1' {a : Expr} (ha : BodyConstsIn p a) : ∀ {e : Expr} {d : Nat},
    BodyConstsIn p e → BodyConstsIn p (e.instantiate1' a d)
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact BodyConstsIn_lift ha
      · trivial
  | .app f b, _, h =>
    ⟨BodyConstsIn_instantiate1' ha (e := f) h.1, BodyConstsIn_instantiate1' ha (e := b) h.2⟩
  | .lam _ _ b _, _, h => BodyConstsIn_instantiate1' ha (e := b) h
  | .forallE _ t b _, _, h =>
    ⟨BodyConstsIn_instantiate1' ha (e := t) h.1, BodyConstsIn_instantiate1' ha (e := b) h.2⟩
  | .letE _ t v b _, _, h =>
    ⟨BodyConstsIn_instantiate1' ha (e := t) h.1, BodyConstsIn_instantiate1' ha (e := v) h.2.1,
      BodyConstsIn_instantiate1' ha (e := b) h.2.2⟩
  | .mdata _ e, _, h => BodyConstsIn_instantiate1' ha (e := e) h
  | .proj _ _ e, _, h => ⟨h.1, BodyConstsIn_instantiate1' ha (e := e) h.2⟩
  | .fvar _, _, h | .mvar _, _, h | .sort _, _, h | .const .., _, h | .lit _, _, h => h

/-- Universe instantiation keeps `BodyConstsIn`. Port of `ML-V Relation/Extend.lean:158`. -/
theorem BodyConstsIn_instLevels {ps : List Name} {us : List Level} : ∀ {e : Expr},
    BodyConstsIn p e → BodyConstsIn p (Pure.instLevels ps us e)
  | .app f a, h => ⟨BodyConstsIn_instLevels (e := f) h.1, BodyConstsIn_instLevels (e := a) h.2⟩
  | .lam _ _ b _, h => BodyConstsIn_instLevels (e := b) h
  | .forallE _ t b _, h =>
    ⟨BodyConstsIn_instLevels (e := t) h.1, BodyConstsIn_instLevels (e := b) h.2⟩
  | .letE _ t v b _, h =>
    ⟨BodyConstsIn_instLevels (e := t) h.1, BodyConstsIn_instLevels (e := v) h.2.1,
      BodyConstsIn_instLevels (e := b) h.2.2⟩
  | .mdata _ e, h => BodyConstsIn_instLevels (e := e) h
  | .proj _ _ e, h => ⟨h.1, BodyConstsIn_instLevels (e := e) h.2⟩
  | .const .., h => h
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lit _, h => h

/-- Abstracting a free variable keeps `BodyConstsIn`. Reference: none. -/
theorem BodyConstsIn_absFV {x : FVarId} : ∀ {d : Nat} {e : Expr}, BodyConstsIn p e →
    BodyConstsIn p (absFV x d e)
  | _, .bvar _, _ => trivial
  | _, .fvar y, _ => by simp only [absFV]; split <;> trivial
  | _, .app f a, h => ⟨BodyConstsIn_absFV (e := f) h.1, BodyConstsIn_absFV (e := a) h.2⟩
  | _, .lam _ _ b _, h => BodyConstsIn_absFV (e := b) h
  | _, .forallE _ t b _, h => ⟨BodyConstsIn_absFV (e := t) h.1, BodyConstsIn_absFV (e := b) h.2⟩
  | _, .letE _ t v b _, h =>
    ⟨BodyConstsIn_absFV (e := t) h.1, BodyConstsIn_absFV (e := v) h.2.1,
      BodyConstsIn_absFV (e := b) h.2.2⟩
  | _, .mdata _ e, h => BodyConstsIn_absFV (e := e) h
  | _, .proj _ _ e, h => ⟨h.1, BodyConstsIn_absFV (e := e) h.2⟩
  | _, .mvar _, h | _, .sort _, h | _, .const .., h | _, .lit _, h => h

end Consts

/-! ## Agreement of the sub-environment and the program -/

variable {D P : List ConstantInfo}

/-- A found declaration is a member with that name. Port of `ML-V Bridge/ProgEnv.lean:28`. -/
theorem findDecl_eq_some {l : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (h : findDecl l c = some ci) : ci ∈ l ∧ ci.name = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A declaration of the sub-environment is the program's. Port of
`ML-V Relation/Extend.lean:24`. -/
theorem findDecl_sub (hsub : SubEnv D P) {c : Name} {ci : ConstantInfo}
    (h : findDecl D c = some ci) : findDecl P c = some ci := by
  obtain ⟨hm, rfl⟩ := findDecl_eq_some h
  exact hsub ci hm

/-- The sub-environment and the program agree on the names of the sub-environment. Port of
`ML-V Relation/Extend.lean:30`. -/
theorem findDecl_agree (hsub : SubEnv D P) {c : Name} (h : (findDecl D c).isSome) :
    findDecl D c = findDecl P c := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 h
  rw [hci, findDecl_sub hsub hci]

/-- `ctorAlts` on two lists that agree on the constructors. Port of
`ML-V Relation/Extend.lean:35`. -/
theorem ctorAlts_congr : ∀ {cs : List Name}, (∀ x ∈ cs, findDecl D x = findDecl P x) →
    ctorAlts D cs = ctorAlts P cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [ctorAlts]
    rw [show findConst D c = findConst P c from h c List.mem_cons_self,
      ctorAlts_congr fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `blockCtorCount` on two lists that agree on the block. Port of
`ML-V Relation/Extend.lean:43`. -/
theorem blockCtorCount_congr : ∀ {ts : List Name}, (∀ x ∈ ts, findDecl D x = findDecl P x) →
    blockCtorCount D ts = blockCtorCount P ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [blockCtorCount]
    rw [show findConst D t = findConst P t from h t List.mem_cons_self,
      blockCtorCount_congr fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The recognizer answers the same in two lists that agree on what it reads. Port of
`ML-V Relation/Extend.lean:52`. -/
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

/-- A constant at the head. Reference: none. -/
theorem isConstAt_const {e : Expr} {c : Name} {lps : List Name} (h : isConstAt e c lps = true) :
    ∃ us, e = .const c us := by
  cases e <;> simp only [isConstAt, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at h
  exact ⟨_, by rw [h.1.1]⟩

/-- What the recognizer reads when it answers: `n` is `T.casesOn`, a definition whose value is
λs around an application of the recursor `T.rec`, `T` an inductive, `T.rec` a recursor whose block
contains `T`. Port of `ML-V Relation/Extend.lean:74`, with the head of the value. -/
theorem casesInfo?_reads {X : List ConstantInfo} {n : Name} {ci : CasesInfo}
    (h : casesInfo? X n = some ci) :
    ∃ T d I R k body us, n = .str T "casesOn" ∧ ci.indName = T ∧
      findDecl X n = some (.defnInfo d) ∧ findDecl X T = some (.inductInfo I) ∧
      findDecl X (mkRecName T) = some (.recInfo R) ∧ T ∈ R.all ∧
      peelLams k d.value = some body ∧ (spine body).1 = .const R.name us := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body _ _ hj hb _ _ =>
        split at h
        next hok =>
          cases h
          simp only [Bool.and_eq_true] at hok
          obtain ⟨us, hus⟩ := isConstAt_const hok.1.1.1.1.1.1.2
          exact ⟨T, d, I, R, _, body, us, rfl, rfl, hd, hI, hR,
            List.isSome_idxOf?.1 (by rw [hj]; rfl), hb, hus⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h


/-- Whether a constant of a dependency-closed sub-environment is a recognized `casesOn`, and of
which inductive, is the same in the program: when either recognizes it, the recursor `T.rec` is in
`D` (in `D` by the recognizer; in `P`, as the head of the value, which `D` reads when it does not
recognize the constant), hence by `DepClosed` its block, `T` and `T`'s constructors. Port of
`ML-V Relation/Extend.lean:200`. -/
theorem casesOnOf?_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : casesOnOf? D c = casesOnOf? P c := by
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
      obtain ⟨T, -, -, R, -, -, -, hT, hci, -, -, hR, hTR, -, -⟩ := casesInfo?_reads hD
      obtain ⟨heq, hTD⟩ := key T R hT hR hTR
      rw [← heq, hD]
      refine ⟨rfl, fun ci' h => ?_⟩
      cases h
      rw [hci]; exact hTD
    | none =>
      cases hP : casesInfo? P c with
      | none => exact ⟨rfl, fun _ h => nomatch h⟩
      | some ci =>
        obtain ⟨T, d, -, R, _, _, us, hT, -, hd, -, hR, hTR, hb, hhd⟩ := casesInfo?_reads hP
        -- `D` does not recognize `c`, so it reads `c`'s value, whose head is `T.rec`.
        have hdD : findDecl D c = some (.defnInfo d) := by rw [findDecl_agree hsub hc, hd]
        have hread : ReadExpr D (.defnInfo d) d.value := by
          refine .inr (.inl ⟨d, rfl, rfl, ?_⟩)
          have hdn : d.name = c := (findDecl_eq_some hdD).2
          rw [hdn]
          unfold casesOnOf?
          rw [hD]; rfl
        have hhead :=
          ConstsIn_spine (ConstsIn_peelLams hb ((hcl _ (findDecl_eq_some hdD).1).1 _ hread))
        rw [hhd] at hhead
        have hRn : R.name = mkRecName T := (findDecl_eq_some hR).2
        change (findDecl D R.name).isSome = true at hhead
        rw [hRn] at hhead
        have hRD : findDecl D (mkRecName T) = some (.recInfo R) := by
          rw [findDecl_agree hsub hhead, hR]
        rw [(key T R hT hRD hTR).1, hP] at hD
        cases hD
  unfold casesOnOf?
  rw [hci.1]
  split
  next ci h => rw [findDecl_agree hsub (hci.2 ci h)]
  next => rfl

variable {a : ConstantInfo → Bool} {k : ErasureConfig}

/-- Constructor and `casesOn` arities agree on the sub-environment's names. Port of
`ML-V Relation/Extend.lean:273`. -/
theorem specialArity_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : specialArity ⟨D, a, k⟩ c = specialArity ⟨P, a, k⟩ c := by
  unfold specialArity EvalEnv.casesOn?
  dsimp only
  rw [casesOnOf?_agree hsub hcl hc, findDecl_agree hsub hc]

/-- δ agrees on the sub-environment's names. Port of `ML-V Relation/Extend.lean:281`. -/
theorem unfold?_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) :
    EvalEnv.unfold? ⟨D, a, k⟩ c = EvalEnv.unfold? ⟨P, a, k⟩ c := by
  unfold EvalEnv.unfold? EvalEnv.casesOn?
  dsimp only
  rw [casesOnOf?_agree hsub hcl hc, findDecl_agree hsub hc]

/-- Evident propositions agree on terms whose constants are in the sub-environment. Port of
`ML-V Relation/Extend.lean:289`. -/
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

/-- Atoms agree on the sub-environment's names. Port of `ML-V Relation/Extend.lean:306`. -/
theorem isAtom_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name}
    (hc : (findDecl D c).isSome) : EvalEnv.isAtom ⟨D, a, k⟩ c = EvalEnv.isAtom ⟨P, a, k⟩ c := by
  unfold EvalEnv.isAtom
  rw [unfold?_agree hsub hcl hc]
  unfold EvalEnv.casesOn?
  dsimp only
  rw [casesOnOf?_agree hsub hcl hc]
  cases hD : findDecl D c with
  | none => rw [hD] at hc; cases hc
  | some ci =>
    rw [← findDecl_agree hsub hc, hD]
    dsimp only
    obtain ⟨hreads, -⟩ := hcl ci (findDecl_eq_some hD).1
    rw [EvidentProp_agree hsub _ (hreads _ (.inl rfl))]

/-! ## What the source semantics reads -/

/-- The head constant of a term whose constants lie in `D` is in `D`. Port of
`ML-V Source/Restrict.lean:26`. -/
theorem head_mem {x : Expr} {c : Name} {us : List Level}
    (hx : BodyConstsIn (fun c => (findDecl D c).isSome) x)
    (h : x.getAppFn = .const c us) : (findDecl D c).isSome := by
  have := BodyConstsIn_getAppFn hx
  rw [h] at this
  exact this

/-- Short spines agree on terms whose constants lie in the sub-environment. Port of
`ML-V Source/Restrict.lean:34`. -/
theorem shortSpine_iff (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (hx : BodyConstsIn (fun c => (findDecl D c).isSome) x) :
    ShortSpine ⟨D, a, k⟩ x ↔ ShortSpine ⟨P, a, k⟩ x := by
  constructor
  · rintro ⟨c, us, ar, hfn, hs, hn⟩
    exact ⟨c, us, ar, hfn, (specialArity_agree hsub hcl (head_mem hx hfn)).symm.trans hs, hn⟩
  · rintro ⟨c, us, ar, hfn, hs, hn⟩
    exact ⟨c, us, ar, hfn, (specialArity_agree hsub hcl (head_mem hx hfn)).trans hs, hn⟩

/-- `Prop` inductives agree on the sub-environment's names. Port of
`ML-V Source/Restrict.lean:52`. -/
theorem propInd_agree (hsub : SubEnv D P) {S : Name} (hS : (findDecl D S).isSome) :
    EvalEnv.propInd ⟨D, a, k⟩ S = EvalEnv.propInd ⟨P, a, k⟩ S := by
  unfold EvalEnv.propInd
  dsimp only
  rw [findDecl_agree hsub hS]

/-- A constructor value of the program is one of the sub-environment, and its fields' constants
lie in the sub-environment. Port of `ML-V Source/Restrict.lean:70`. -/
theorem CtorValue.restrict (hsub : SubEnv D P) {T : Name} {m : Expr} {i : Nat} {fs : List Expr}
    (h : CtorValue ⟨P, a, k⟩ T m i fs) (hm : BodyConstsIn (fun c => (findDecl D c).isSome) m) :
    CtorValue ⟨D, a, k⟩ T m i fs ∧ ∀ x ∈ fs, BodyConstsIn (fun c => (findDecl D c).isSome) x := by
  obtain ⟨C, us, cv, ps, hC, h1, h2, h3, h4, rfl⟩ := h
  have ⟨hCD, has⟩ := BodyConstsIn_mkAppN.1 hm
  exact ⟨⟨C, us, cv, ps, (findDecl_agree hsub hCD).trans hC, h1, h2, h3, h4, rfl⟩,
    fun x hx => has x (List.mem_append_right _ hx)⟩

/-- `natLitCtor` changes only Nat literals. Port of `ML-V Bridge/Proj.lean:48`. -/
theorem natLitCtor_cases (e : Expr) : (∃ k, e = .lit (.natVal k)) ∨ natLitCtor e = e := by
  match e with
  | .lit (.natVal k) => exact .inl ⟨k, rfl⟩
  | .lit (.strVal _) | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam ..
  | .forallE .. | .letE .. | .mdata .. | .proj .. => exact .inr rfl

/-- The constructor form (`natLitCtor`) of a value whose constants lie in the sub-environment has
its constants there, given that the program lists every constructor among its inductive's: the
constructor of a Nat literal's form is one of `T`, which the sub-environment contains with its
constructors. Port of `ML-V Source/Restrict.lean:82`. -/
theorem natLitCtor_restrict (hsub : SubEnv D P) (hcl : DepClosed D)
    (hctors : ∀ C cv, findDecl P C = some (.ctorInfo cv) →
      ∃ iv, findDecl P cv.induct = some (.inductInfo iv) ∧ C ∈ iv.ctors)
    {T : Name} {mj : Expr} {i : Nat} {fs : List Expr} (hT : (findDecl D T).isSome)
    (hcv : CtorValue ⟨P, a, k⟩ T (natLitCtor mj) i fs)
    (hmj : BodyConstsIn (fun c => (findDecl D c).isSome) mj) :
    BodyConstsIn (fun c => (findDecl D c).isSome) (natLitCtor mj) := by
  obtain ⟨C, us, cv, ps, hC, hind, -, -, -, hm⟩ := hcv
  have hCD : (findDecl D C).isSome := by
    obtain ⟨iv, hiv, hmem⟩ := hctors C cv hC
    rw [hind, ← findDecl_agree hsub hT] at hiv
    exact (hcl _ (findDecl_eq_some hiv).1).2.2.1 iv rfl C hmem
  have hfold : ∀ (l : List Expr) (f : Expr), (l.foldl .app f).getAppFn = f.getAppFn := by
    intro l
    induction l with
    | nil => intro; rfl
    | cons x l ih => intro f; exact (ih _).trans rfl
  have hfn : (natLitCtor mj).getAppFn = .const C us := by
    rw [hm, show mkAppN (.const C us) (ps ++ fs).toArray = (ps ++ fs).foldl .app (.const C us) by
      simp only [mkAppN, List.foldl_toArray]; rfl, hfold]; rfl
  rcases natLitCtor_cases mj with ⟨n, rfl⟩ | h
  · cases n with
    | zero => cases hfn; exact hCD
    | succ n => cases hfn; exact ⟨hCD, trivial⟩
  · rw [h]; exact hmj

/-- The inductive of a recognized `casesOn` is a declaration of the environment, under its
name. Port of `ML-V Source/Restrict.lean:134`. -/
theorem casesOnOf?_ind {X : List ConstantInfo} {c : Name} {iv : InductiveVal}
    (h : casesOnOf? X c = some iv) : findDecl X iv.name = some (.inductInfo iv) := by
  unfold casesOnOf? at h
  split at h
  next ci _ =>
    split at h
    next iv' hf =>
      obtain rfl : iv' = iv := Option.some.inj h
      have hn : iv'.name = ci.indName := (findDecl_eq_some hf).2
      rw [hn]; exact hf
    next => cases h
  next => cases h

/-- The constructors of the inductive of a recognized `casesOn` of the sub-environment lie in it.
Port of `ML-V Source/Restrict.lean:171`. -/
theorem ctor_mem_of_casesOn? (hcl : DepClosed D) {c n : Name} {iv : InductiveVal}
    (h : casesOnOf? D c = some iv) (hn : n ∈ iv.ctors) : (findDecl D n).isSome :=
  (hcl _ (findDecl_eq_some (casesOnOf?_ind h)).1).2.2.1 iv rfl n hn

/-- A δ-unfolding of the sub-environment unfolds one of its declarations to an expression it
reads. Port of `ML-V Source/Restrict.lean:145`. -/
theorem unfold?_read {c : Name} {ci : ConstantInfo} {body : Expr}
    (h : EvalEnv.unfold? ⟨D, a, k⟩ c = some (ci, body)) : ci ∈ D ∧ ReadExpr D ci body := by
  unfold EvalEnv.unfold? at h
  split at h
  next d hd =>
    split at h
    next => cases h
    next hno =>
      cases h
      refine ⟨(findDecl_eq_some hd).1, .inr (.inl ⟨d, rfl, rfl, ?_⟩)⟩
      have hn : d.name = c := (findDecl_eq_some hd).2
      rw [hn]
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff] at hno
      exact hno.2
  next => cases h

/-- A `mapM` into `Option` that succeeds with `f` succeeds with the same results with any `g`
that agrees with `f` on the list where `f` succeeds. Port of `ML-V Source/Restrict.lean:177`. -/
theorem mapM_restrict {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {r : List β}, (∀ x ∈ l, ∀ y, f x = some y → g x = some y) →
      l.mapM f = some r → l.mapM g = some r
  | [], _, _, h => h
  | x :: l, r, hfg, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    exact ⟨y, hfg x (.head _) y hy, ys, mapM_restrict (fun z hz => hfg z (.tail _ hz)) hys, rfl⟩

/-- A result of a successful `mapM` is the image of an element. Port of
`ML-V Source/Restrict.lean:188`. -/
theorem mem_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by simp at h; subst h; cases hy
  | x :: l, r, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, .head _, hz⟩
    · obtain ⟨x', hx', h'⟩ := mem_mapM hzs y hy
      exact ⟨x', .tail _ hx', h'⟩

/-- The block of a recursor of the sub-environment, read in the program, is read the same in the
sub-environment: its inductives and their constructors lie in it (`DepClosed`). Port of
`ML-V Source/Restrict.lean:202`. -/
theorem recBlock?_restrict (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name} {rv : RecursorVal}
    (hr : findDecl D c = some (.recInfo rv)) {r}
    (h : EvalEnv.recBlock? ⟨P, a, k⟩ rv = some r) : EvalEnv.recBlock? ⟨D, a, k⟩ rv = some r := by
  obtain ⟨-, -, -, -, hrall⟩ := hcl _ (findDecl_eq_some hr).1
  have hall := hrall rv rfl
  unfold EvalEnv.recBlock? recBlockOf? at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨ivs, hivs, cvs, hcvs, rfl⟩ := h
  refine ⟨ivs, mapM_restrict (fun t ht y hy => ?_) hivs, cvs,
    mapM_restrict (fun x hx y hy => ?_) hcvs, rfl⟩
  · rw [findDecl_agree hsub (hall t ht)]; exact hy
  · obtain ⟨iv, hiv, hx'⟩ := List.mem_flatMap.1 hx
    obtain ⟨t, ht, hti⟩ := mem_mapM hivs iv hiv
    have hiv' : findDecl P t = some (.inductInfo iv) := by
      revert hti
      cases findDecl P t with
      | none => intro h; cases h
      | some ci => cases ci <;> intro h <;> simp at h; subst h; rfl
    rw [← findDecl_agree hsub (hall t ht)] at hiv'
    obtain ⟨-, -, hctors, -, -⟩ := hcl _ (findDecl_eq_some hiv').1
    rw [findDecl_agree hsub (hctors iv rfl x hx')]
    exact hy


/-- Heads that block `appCong` in the sub-environment block it in the program. Port of
`ML-V Source/Restrict.lean:113`. -/
theorem BlocksCong_sub (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (hx : BodyConstsIn (fun c => (findDecl D c).isSome) x) (h : BlocksCong ⟨D, a, k⟩ x) :
    BlocksCong ⟨P, a, k⟩ x := by
  have key : ((∃ c us cv, x.getAppFn = .const c us ∧ findDecl D c = some (.ctorInfo cv)) ∨
      (∃ c us iv, x.getAppFn = .const c us ∧ EvalEnv.casesOn? ⟨D, a, k⟩ c = some iv) ∨
      (∃ c us qv, x.getAppFn = .const c us ∧ findDecl D c = some (.quotInfo qv) ∧
        qv.kind = .ctor)) →
      (∃ c us cv, x.getAppFn = .const c us ∧ findDecl P c = some (.ctorInfo cv)) ∨
      (∃ c us iv, x.getAppFn = .const c us ∧ EvalEnv.casesOn? ⟨P, a, k⟩ c = some iv) ∨
      (∃ c us qv, x.getAppFn = .const c us ∧ findDecl P c = some (.quotInfo qv) ∧
        qv.kind = .ctor) := by
    rintro (⟨c, us, cv, hfn, hcv⟩ | ⟨c, us, iv, hfn, hco⟩ | ⟨c, us, qv, hfn, hqv, hk⟩)
    · exact .inl ⟨c, us, cv, hfn, findDecl_sub hsub hcv⟩
    · exact .inr (.inl ⟨c, us, iv, hfn,
        (casesOnOf?_agree hsub hcl (head_mem hx hfn)).symm.trans hco⟩)
    · exact .inr (.inr ⟨c, us, qv, hfn, findDecl_sub hsub hqv, hk⟩)
  unfold BlocksCong at h ⊢
  split at h <;> first | trivial | exact key h

/-! ## Marks keep the constants -/

section Marks
variable {p : Name → Prop} {ds : List ConstantInfo} {cfg : ErasureConfig}

/-- Two lists related elementwise by a relation that keeps `BodyConstsIn`. Reference: none. -/
theorem forall_mem_of_rel {as âs : List Expr} (hl : as.length = âs.length)
    (h : ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → BodyConstsIn p a → BodyConstsIn p â)
    (ha : ∀ a ∈ as, BodyConstsIn p a) : ∀ â ∈ âs, BodyConstsIn p â := by
  intro â hâ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hâ
  have hi' : i < as.length := by omega
  exact h i as[i] âs[i] (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hi)
    (ha _ (List.getElem_mem hi'))

/-- A marking has the constants of the term outside λ domains: the marks add `mdata`, the
`eta`-marked λs (whose domains the oracle infers) and fresh variables, which are abstracted.
Reference: none (DV-32). -/
theorem MarkOf.bodyConstsIn {ls : List Local} {e ê : Expr} (h : MarkOf ds cfg ls e ê) :
    BodyConstsIn p e → BodyConstsIn p ê := by
  refine MarkOf.rec
    (motive_1 := fun _ e ê _ => BodyConstsIn p e → BodyConstsIn p ê)
    (motive_2 := fun _ _ _ c _ as ê _ => p c → (∀ a ∈ as, BodyConstsIn p a) → BodyConstsIn p ê)
    (motive_3 := fun _ c _ as ê _ => p c → (∀ a ∈ as, BodyConstsIn p a) → BodyConstsIn p ê)
    (motive_4 := fun _ _ e _ ê _ => BodyConstsIn p e → BodyConstsIn p ê)
    ?erase ?fvar ?mdata ?lam ?letE ?proj ?litZero ?litSucc ?app ?constApp ?special
    ?sat ?eintro ?casesProp ?casesReduced ?cases ?ctor ?quotMk ?quotLift ?recr
    ?done ?alam ?aintro h
  case erase | fvar | litZero | litSucc => intros; rename_i h; exact h
  case mdata => intros; rename_i ih h; exact ih h
  case lam | alam =>
    intros; rename_i ih h
    exact BodyConstsIn_absFV (ih (BodyConstsIn_instantiate1' (p := p) (a := .fvar _) trivial h))
  case letE =>
    intros; rename_i ihv ihb h
    exact ⟨h.1, ihv h.2.1,
      BodyConstsIn_absFV (ihb (BodyConstsIn_instantiate1' (p := p) (a := .fvar _) trivial h.2.2))⟩
  case proj => intros; rename_i ih h; exact ⟨h.1, ih h.2⟩
  case app =>
    intros; rename_i hlen _ ihf iha h
    rw [BodyConstsIn_mkAppN] at h ⊢
    exact ⟨ihf h.1, forall_mem_of_rel hlen iha h.2⟩
  case constApp =>
    intros; rename_i hlen _ iha h
    rw [BodyConstsIn_mkAppN] at h ⊢
    exact ⟨h.1, forall_mem_of_rel hlen iha h.2⟩
  case special => intros; rename_i ih h; rw [BodyConstsIn_mkAppN] at h; exact ih h.1 h.2
  case sat => intros; rename_i ih hc has; exact ih hc has
  case eintro =>
    intros; rename_i ih hc has
    refine BodyConstsIn_absFV (ih hc fun a ha => ?_)
    rcases List.mem_append.1 ha with ha | ha
    · exact has a ha
    · rw [List.mem_singleton.1 ha]; trivial
  case casesProp => intros; rename_i hc has; exact BodyConstsIn_mkAppN.2 ⟨hc, has⟩
  case casesReduced =>
    intros; rename_i hlx _ iha ihx hc has
    refine BodyConstsIn_mkAppN.2 ⟨hc, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hx | rfl) | rfl) | hx
    · exact has x (by simp [hx])
    · simp only [BodyConstsIn]; exact has _ (by simp)
    · exact iha (has _ (by simp))
    · exact forall_mem_of_rel hlx ihx (fun a ha => has a (by simp [ha])) x hx
  case cases =>
    intros; rename_i hlalt _ _ _ hlen hcv hT _ hlx _ ihd iha ihx hc has
    refine BodyConstsIn_mkAppN.2 ⟨hc, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hx | rfl) | hx) | hx
    · exact has x (by simp [hx])
    · exact ihd (has _ (by simp))
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi' := hi
      rw [← hlen] at hi'
      have hic := hi'
      rw [hlalt] at hic
      obtain ⟨cv, hcv'⟩ := hcv i _ (List.getElem?_eq_getElem hic)
      obtain ⟨T, hT'⟩ := hT i _ (List.getElem?_eq_getElem hi')
      exact iha i _ cv _ _ T (List.getElem?_eq_getElem hic) hcv' (List.getElem?_eq_getElem hi')
        (List.getElem?_eq_getElem hi) hT' (has _ (by simp [List.getElem_mem hi']))
    · exact forall_mem_of_rel hlx ihx (fun a ha => has a (by simp [ha])) x hx
  case ctor =>
    intros; rename_i hlen _ iha hc has
    exact BodyConstsIn_mkAppN.2 ⟨hc, forall_mem_of_rel hlen iha has⟩
  case quotMk =>
    intros; rename_i hlx _ iha ihx hc has
    refine BodyConstsIn_mkAppN.2 ⟨hc, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | hx
    · exact has _ (by simp)
    · exact has _ (by simp)
    · exact iha (has _ (by simp))
    · exact forall_mem_of_rel hlx ihx (fun a ha => has a (by simp [ha])) x hx
  case quotLift =>
    intros; rename_i hlx _ ihf ihq ihx hc has
    refine BodyConstsIn_mkAppN.2 ⟨hc, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | hx
    · exact has _ (by simp)
    · exact has _ (by simp)
    · exact has _ (by simp)
    · exact ihf (has _ (by simp))
    · exact has _ (by simp)
    · exact ihq (has _ (by simp))
    · exact forall_mem_of_rel hlx ihx (fun a ha => has a (by simp [ha])) x hx
  case recr =>
    intros; rename_i hlm _ hli _ _ hlx _ ihmin ihis ihmaj ihx hc has
    refine BodyConstsIn_mkAppN.2 ⟨hc, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | rfl) | hx
    · exact has x (by simp [hx])
    · exact has x (by simp [hx])
    · exact forall_mem_of_rel hlm ihmin (fun a ha => has a (by simp [ha])) x hx
    · exact forall_mem_of_rel hli ihis (fun a ha => has a (by simp [ha])) x hx
    · exact ihmaj (has _ (by simp))
    · exact forall_mem_of_rel hlx ihx (fun a ha => has a (by simp [ha])) x hx
  case done => intros; rename_i ih h; exact ih h
  case aintro => intros; rename_i ih h; exact BodyConstsIn_absFV (ih ⟨h, trivial⟩)

end Marks

end Restrict

open Restrict in
/-- Evaluation in the program restricts to a dependency-closed sub-environment that contains the
constants of the term outside λ domains, and the result's constants lie in it, in a program that
lists every constructor among its inductive's constructors, if the marking of every expression the
sub-environment reads is the same over the program as over the sub-environment (`δ` marks the
value it unfolds over the environment it evaluates in; `markOf_agree_statement`). Port of
`ML-V Source/Restrict.lean:238` without pre-definitions and with the frozen rules. Reference:
weakening of the global environment for evaluation (`MR E/EWcbvEval.v`, `eval_weakening`), read in
the restricting direction. -/
theorem SrcEval.restrict {env : ConLeche.Env} {decls P : List ConstantInfo} {e v : Expr}
    {view : EnvView} {cfg : ErasureConfig} (hsub : SubEnv decls P) (hcl : DepClosed decls)
    (hctors : ∀ C cv, findDecl P C = some (.ctorInfo cv) →
      ∃ iv, findDecl P cv.induct = some (.inductInfo iv) ∧ C ∈ iv.ctors)
    (hmark : ∀ ci ∈ decls, ∀ x xM, ReadExpr decls ci x → MarkOf P cfg [] x xM →
      MarkOf decls cfg [] x xM)
    (hc : BodyConstsIn (fun c => (findDecl decls c).isSome) e)
    (hev : SrcEval env (evalEnvOf view cfg P) e v) :
    SrcEval env (evalEnvOf view cfg decls) e v ∧
      BodyConstsIn (fun c => (findDecl decls c).isSome) v := by
  have mem : ∀ {l : List Expr} {i : Nat} {x : Expr}, l[i]? = some x → x ∈ l :=
    fun h => List.mem_of_getElem? h
  have agreeCases : ∀ {c : Name} {iv : InductiveVal}, (findDecl decls c).isSome →
      (evalEnvOf view cfg P).casesOn? c = some iv →
      (evalEnvOf view cfg decls).casesOn? c = some iv := fun hcD hco =>
    (casesOnOf?_agree hsub hcl hcD).trans hco
  revert hc
  induction hev with
  | beta hns _ _ hok _ ihf iha ihb =>
    intro hc
    obtain ⟨ef, hlam⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    obtain ⟨eb, hv⟩ := ihb (BodyConstsIn_instantiate1' ha' hlam)
    exact ⟨.beta (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef ea hok eb, hv⟩
  | etaBeta hns _ _ hok _ ihf iha ihb =>
    intro hc
    obtain ⟨ef, hlam⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    obtain ⟨eb, hv⟩ := ihb (BodyConstsIn_instantiate1' ha' hlam)
    exact ⟨.etaBeta (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef ea hok eb, hv⟩
  | zeta _ hok _ ihv ihb =>
    intro hc
    obtain ⟨ev, hv'⟩ := ihv hc.2.1
    obtain ⟨eb, hv⟩ := ihb (BodyConstsIn_instantiate1' hv' hc.2.2)
    exact ⟨.zeta ev hok eb, hv⟩
  | delta hu hm _ ih =>
    intro hc
    have hu' := (unfold?_agree hsub hcl hc).trans hu
    obtain ⟨hci, hread⟩ := unfold?_read hu'
    have hm' := hmark _ hci _ _ hread hm
    obtain ⟨eb, hv⟩ := ih (BodyConstsIn_instLevels (MarkOf.bodyConstsIn hm'
      (BodyConstsIn.of_constsIn ((hcl _ hci).1 _ hread))))
    exact ⟨.delta hu' hm' eb, hv⟩
  | constAtom ha =>
    intro hc
    exact ⟨.constAtom ((isAtom_agree hsub hcl hc).trans ha), hc⟩
  | @ctor c cv us as vs hcv hl hlv _ hok ih =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    refine ⟨.ctor ((findDecl_agree hsub hcD).trans hcv) hl hlv
      (fun i x w hx hw => (ih i x w hx hw (has x (mem hx))).1) hok,
      BodyConstsIn_mkAppN.2 ⟨hcD, ?_⟩⟩
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hx : as[i]? = some as[i] := List.getElem?_eq_getElem (by omega)
    exact (ih i _ _ hx (List.getElem?_eq_getElem hi) (has _ (mem hx))).2
  | casesIota hco hlen hm _ hcv hok halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    obtain ⟨em, hmv⟩ := ihm (has _ (mem hm))
    obtain ⟨hcv', hfs⟩ := CtorValue.restrict hsub hcv hmv
    obtain ⟨ea, hv⟩ := iha (BodyConstsIn_mkAppN.2 ⟨has _ (mem halt), hfs⟩)
    exact ⟨.casesIota (agreeCases hcD hco) hlen hm em hcv' hok halt ea, hv⟩
  | casesLitZero hco hN hlen hm _ halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    obtain ⟨ea, hv⟩ := iha (has _ (mem halt))
    exact ⟨.casesLitZero (agreeCases hcD hco) hN hlen hm (ihm (has _ (mem hm))).1 halt ea, hv⟩
  | casesLitSucc hco hN hlen hm _ halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    obtain ⟨ea, hv⟩ := iha ⟨has _ (mem halt), trivial⟩
    exact ⟨.casesLitSucc (agreeCases hcD hco) hN hlen hm (ihm (has _ (mem hm))).1 halt ea, hv⟩
  | @casesFrozen c iv cn cv d alt v us as hco hlen hcs hcn hd herr halt _ iha =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    have hco' := agreeCases hcD hco
    have hcnD := ctor_mem_of_casesOn? hcl hco' (by rw [hcs]; exact List.mem_singleton_self _)
    have hdC : BodyConstsIn (fun c => (findDecl decls c).isSome) d := has (markReduced d) (mem hd)
    have hivD : (findDecl decls iv.name).isSome := by
      rw [show findDecl decls iv.name = _ from casesOnOf?_ind hco']; rfl
    have hfs : ∀ x ∈ (List.range cv.numFields).map (fun j => markErase (.proj iv.name j d)),
        BodyConstsIn (fun c => (findDecl decls c).isSome) x := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨hivD, hdC⟩
    obtain ⟨ea, hv⟩ := iha (BodyConstsIn_mkAppN.2 ⟨has _ (mem halt), hfs⟩)
    exact ⟨.casesFrozen hco' hlen hcs ((findDecl_agree hsub hcnD).trans hcn) hd herr halt ea, hv⟩
  | quotMk hcq hk _ hok ih =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    obtain ⟨ea, ha'⟩ := ih (has _ (by simp))
    refine ⟨.quotMk ((findDecl_agree hsub hcD).trans hcq) hk ea hok,
      BodyConstsIn_mkAppN.2 ⟨hcD, ?_⟩⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact has _ (by simp)
    · exact has _ (by simp)
    · exact ha'
  | quotLift hcq hk _ _ hcq' hk' hok _ ihf ihq ihb =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    obtain ⟨ef, hfC⟩ := ihf (has _ (by simp))
    obtain ⟨eq, hqC⟩ := ihq (has _ (by simp))
    have ⟨hcD', has'⟩ := BodyConstsIn_mkAppN.1 hqC
    obtain ⟨eb, hv⟩ := ihb (BodyConstsIn_instantiate1' (has' _ (by simp)) hfC)
    exact ⟨.quotLift ((findDecl_agree hsub hcD).trans hcq) hk ef eq
      ((findDecl_agree hsub hcD').trans hcq') hk' hok eb, hv⟩
  | @recIota c rv T iv cvs motives minors maj mj k mi mk us v ps ms mins mvs fs rfs ihvs hcr hall
      hcT hblk hni hshape hihs hps hms hmins hlm _ _ hcv hmi hmk hok hrfs hrl _ _ ihmin ihmaj ihih
      ihb =>
    intro hc
    have ⟨hcD, has⟩ := BodyConstsIn_mkAppN.1 hc
    have hcr' := (findDecl_agree hsub hcD).trans hcr
    have hmv : ∀ i m mv, mins[i]? = some m → mvs[i]? = some mv →
        SrcEval env (evalEnvOf view cfg decls) m mv ∧
          BodyConstsIn (fun c => (findDecl decls c).isSome) mv :=
      fun i m mv h1 h2 => ihmin i m mv h1 h2 (has m (by simp [mem h1]))
    obtain ⟨em, hmjC⟩ := ihmaj (has _ (by simp))
    have hTD : (findDecl decls T).isSome :=
      (hcl _ (findDecl_eq_some hcr').1).2.2.2.2 rv rfl T
        (by rw [hall]; exact List.mem_singleton_self _)
    obtain ⟨hcv', hfs⟩ :=
      CtorValue.restrict hsub hcv (natLitCtor_restrict hsub hcl hctors hTD hcv hmjC)
    have hmvC : ∀ x ∈ mvs, BodyConstsIn (fun c => (findDecl decls c).isSome) x := fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact (hmv i m _ hm (List.getElem?_eq_getElem hi)).2
    have hIC : ∀ f ∈ rfs, BodyConstsIn (fun c => (findDecl decls c).isSome)
        (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) := by
      intro f hf
      refine BodyConstsIn_mkAppN.2 ⟨hcD, fun y hy => ?_⟩
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_append.1 hy with hy | hy
        · exact has y (List.mem_append_left _ (List.mem_append_left _ hy))
        · exact hmvC y hy
      · rw [List.mem_singleton.1 hy]
        obtain ⟨h, -, hh⟩ := mem_mapM hrfs f hf
        exact hfs f (List.mem_of_getElem? hh)
    have hih : ∀ i f w, rfs[i]? = some f → ihvs[i]? = some w →
        SrcEval env (evalEnvOf view cfg decls)
          (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w ∧
          BodyConstsIn (fun c => (findDecl decls c).isSome) w :=
      fun i f w h1 h2 => ihih i f w h1 h2 (hIC f (List.mem_of_getElem? h1))
    have hK : BodyConstsIn (fun c => (findDecl decls c).isSome)
        (mkAppN mk (fs ++ ihvs).toArray) := by
      refine BodyConstsIn_mkAppN.2 ⟨hmvC _ (List.mem_of_getElem? hmk), fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hfs x hx
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        obtain ⟨f, hf⟩ : ∃ f, rfs[i]? = some f := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        exact (hih i f _ hf (List.getElem?_eq_getElem hi)).2
    obtain ⟨eb, hv⟩ := ihb hK
    exact ⟨.recIota hcr' hall hcT (recBlock?_restrict hsub hcl hcr' hblk) hni hshape hihs hps
      hms hmins hlm (fun i m mv h1 h2 => (hmv i m mv h1 h2).1) em hcv' hmi hmk hok hrfs hrl
      (fun i f w h1 h2 => (hih i f w h1 h2).1) eb, hv⟩
  | proj _ hcv hfs hok ihm =>
    intro hc
    obtain ⟨em, hmv⟩ := ihm hc.2
    obtain ⟨hcv', hfsC⟩ := CtorValue.restrict hsub hcv hmv
    exact ⟨.proj em hcv' hfs hok, hfsC _ (mem hfs)⟩
  | projFrozen hS _ herr ihm =>
    intro hc
    obtain ⟨em, hmv⟩ := ihm hc.2
    exact ⟨.projFrozen ((propInd_agree hsub hc.1).trans hS) em herr, hc.1, hmv⟩
  | lit hok => intro hc; exact ⟨.lit hok, hc⟩
  | appCong hns _ hb _ hok ihf iha =>
    intro hc
    obtain ⟨ef, hf'⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    exact ⟨.appCong (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef
      (fun hb' => hb (BlocksCong_sub hsub hcl hf' hb')) ea hok, hf', ha'⟩
  | atom h => intro hc; exact ⟨.atom h, hc⟩
  | etaLam => intro hc; exact ⟨.etaLam, hc⟩
  | frozen h => intro hc; exact ⟨.frozen h, hc⟩
  | frozenApp hns _ _ herr ihf iha =>
    intro hc
    obtain ⟨ef, hf'⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    exact ⟨.frozenApp (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef ea herr, hf', ha'⟩

end EraseProof
