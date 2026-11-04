import EraseProof.Bridge.Proj

/-!
# Recognized `casesOn` constants

What the shipping recognizer `Erasure.casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:103`)
establishes about a recognized `T.casesOn` (`casesOn_shape`): it is a definition of the program
whose value is `λ^D, T.rec.{lps} args` with `D = casesArity`, the recursor's parameters, own motive,
indices and major the corresponding binders, and each own minor `fun y₁ … y_L => mᵢ y₁ … y_nf`.
Reference: `Lean.mkCasesOn`; DV-25.
-/

open Lean Erasure

namespace EraseProof

namespace CasesShape

/-- `isBVarAt` as a statement about the list. -/
theorem isBVarAt_iff {as : List Expr} {i m : Nat} :
    isBVarAt as i m = true ↔ as[i]? = some (.bvar m) := by
  unfold isBVarAt
  split
  · rename_i j h; simp [h]
  · rename_i h; simp only [Bool.false_eq_true, false_iff]; exact fun h' => h _ h' 

/-- `isConstAt` as an equation. -/
theorem isConstAt_iff {e : Expr} {c : Name} {lps : List Name} :
    isConstAt e c lps = true → e = .const c (lps.map .param) := by
  unfold isConstAt
  split
  · rename_i c' us
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    rintro ⟨⟨rfl, hl⟩, hz⟩
    congr 1
    induction us generalizing lps with
    | nil => cases lps <;> simp_all
    | cons u us ih =>
      cases lps with
      | nil => simp at hl
      | cons p lps =>
        simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hz
        obtain ⟨hu, hz⟩ := hz
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨?_, ih hz (by simpa using hl)⟩
        cases u <;> simp_all
  · simp

/-- A term is its `spine` reassembled. -/
theorem spine_mkAppN (e : Expr) : mkAppN (spine e).1 (spine e).2.toArray = e := by
  rw [mkAppN_eq_foldl]
  induction e with
  | app f a ihf _ =>
    simp only [spine]
    rw [List.foldl_append, ihf]; rfl
  | _ => rfl

end CasesShape

open CasesShape in
/-- The shape of a recognized `casesOn` (the recognizer's checks, as statements): `c` is
`T.casesOn` for the inductive `iv` named `T`, a definition whose value is `D = casesArity iv`
λ's around `T.rec.{lps} args`, `lps` its level parameters (those of `T.rec`); the recursor's
parameters, own motive (at the inductive's position `j` in the block), indices and major are the
binders of the parameters, motive, indices and major; the own minor of constructor `i` is
`fun y₁ … y_L => mᵢ y₁ … y_nf`, `L` the arity of its premise in the recursor's type and
`nf = numFields`. Reference: `Lean.mkCasesOn`, `Lean.getCasesInfo?`; DV-25. -/
theorem casesOn_shape {σ : EvalEnv} {c : Name} {iv : InductiveVal}
    (h : σ.casesOn? c = some iv) :
    ∃ (d : DefinitionVal) (R : RecursorVal) (j before : Nat) (alts : List CasesAltInfo)
      (body : Expr) (args : List Expr),
      c = .str iv.name "casesOn" ∧ findDecl σ.decls c = some (.defnInfo d) ∧
      findDecl σ.decls iv.name = some (.inductInfo iv) ∧
      findDecl σ.decls (mkRecName iv.name) = some (.recInfo R) ∧
      iv.isUnsafe = false ∧ iv.numNested = 0 ∧ d.levelParams = R.levelParams ∧
      R.numMotives = iv.all.length ∧ R.all.idxOf? iv.name = some j ∧
      blockCtorCount σ.decls (R.all.take (R.all.idxOf iv.name)) = some before ∧
      ctorAlts σ.decls iv.ctors = some alts ∧
      peelLams (casesArity iv) d.value = some body ∧
      body = mkAppN (.const R.name (R.levelParams.map .param)) args.toArray ∧
      args.length = R.numParams + R.numMotives + R.numMinors + R.numIndices + 1 ∧
      (∀ i < iv.numParams, args[i]? = some (.bvar (casesArity iv - 1 - i))) ∧
      args[iv.numParams + j]? = some (.bvar (casesArity iv - 1 - iv.numParams)) ∧
      (∀ i < alts.length, ∃ a m,
        args[iv.numParams + R.numMotives + before + i]? = some a ∧
        peelLams (minorArity R.type (iv.numParams + R.numMotives + before + i)) a = some m ∧
        isMinorBody m (minorArity R.type (iv.numParams + R.numMotives + before + i) +
            (casesArity iv - 1 - (casesMajor iv + 1 + i)))
          (minorArity R.type (iv.numParams + R.numMotives + before + i)) (altFields alts i) = true) ∧
      (∀ i < iv.numIndices, args[iv.numParams + R.numMotives + R.numMinors + i]? =
        some (.bvar (casesArity iv - 1 - (iv.numParams + 1 + i)))) ∧
      args[iv.numParams + R.numMotives + R.numMinors + iv.numIndices]? =
        some (.bvar (casesArity iv - 1 - casesMajor iv)) := by
  unfold EvalEnv.casesOn? at h
  split at h
  next ci hci =>
    split at h
    next iv' hiv =>
      cases h
      unfold casesInfo? at hci
      split at hci
      next T =>
        split at hci
        next d I R hd hI hR =>
          dsimp only at hci
          split at hci
          next j body alts before hj hb ha hbe =>
            split at hci
            next hok =>
              cases hci
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
                List.mem_range] at hok
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hn⟩, hlp⟩, hmot⟩, hhd⟩, hlen⟩, hps⟩, hm⟩, hmin⟩, his⟩, hmaj⟩ := hok
              change findDecl σ.decls T = _ at hiv
              change findDecl σ.decls T = _ at hI
              rw [hiv] at hI
              cases hI
              have hT : iv.name = T := (findDecl_eq_some hiv).2
              subst hT
              refine ⟨d, R, j, before, alts, body, (spine body).2, rfl, hd, hiv, hR, hu, hn, hlp,
                hmot, hj, hbe, ha, hb, ?_, hlen, fun i hi => isBVarAt_iff.mp (hps i hi),
                isBVarAt_iff.mp hm, fun i hi => ?_, fun i hi => isBVarAt_iff.mp (his i hi),
                isBVarAt_iff.mp hmaj⟩
              · conv => lhs; rw [← spine_mkAppN body]
                rw [isConstAt_iff hhd]
              · have hi' := hmin i hi
                split at hi'
                · rename_i a m ha' hm'
                  rw [ha'] at hm'
                  refine ⟨a, m, ha', hm', ?_⟩
                  unfold casesArity casesMajor
                  simpa [Nat.add_assoc] using hi'
                · cases hi'
            next => cases hci
          next => cases hci
        next => cases hci
      next => cases hci
    next => cases h
  next => cases h

end EraseProof
