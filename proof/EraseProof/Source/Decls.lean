import EraseProof.Spec

/-!
# Lookups in a list of declarations

The closure property of a list of declarations (`DepClosed`); what a successful lookup
(`findDecl`), a recognized `casesOn` (`Erasure.casesInfo?`, `casesOnOf?`) and a successful `mapM`
give; the recognizer on two lists that agree on what it reads; the constants of the parts of a term
the recognizer reads.
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

namespace Decls

section Consts
variable {p : Name → Prop}

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

end Consts

/-- A found declaration is a member with that name. Port of `ML-V Bridge/ProgEnv.lean:28`. -/
theorem findDecl_eq_some {l : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (h : findDecl l c = some ci) : ci ∈ l ∧ ci.name = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

variable {D P : List ConstantInfo}

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

/-- `natLitCtor` changes only Nat literals. Port of `ML-V Bridge/Proj.lean:48`. -/
theorem natLitCtor_cases (e : Expr) : (∃ k, e = .lit (.natVal k)) ∨ natLitCtor e = e := by
  match e with
  | .lit (.natVal k) => exact .inl ⟨k, rfl⟩
  | .lit (.strVal _) | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam ..
  | .forallE .. | .letE .. | .mdata .. | .proj .. => exact .inr rfl

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

end Decls

end EraseProof
