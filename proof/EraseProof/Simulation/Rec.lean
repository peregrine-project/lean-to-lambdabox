import EraseProof.Simulation.Iota
import EraseProof.Simulation.RecFix

/-!
# The recursor ι case of the simulation

A saturated recursor of a single inductive without indices (`SrcEval.recIota`) is erased to the λ□
fixpoint of `recFix` under `let`s of its erased minors (`Erases.recLet`), or with the minors' values
substituted (`Erases.recFix`). The λ□ evaluation binds the minors' values, unfolds the fixpoint on
the major's value, selects the constructor's alternative (a λ□ `case`, or the alternative applied
to `□` when the major is erased in the reduced form) and applies the minor's value to the fields
and to the recursive calls on the recursive fields, which are erasures of the source induction
hypotheses (`Erases.recFix`). Reference: none (MetaRocq has no recursors; DV-30); the λ□ steps are
`eval_zeta`, `eval_fix`, `eval_beta` and `eval_iota` (`MR E/EWcbvEval.v`).
-/

open Lean Erasure

namespace EraseProof

namespace SimRec

open TargetSubst TargetLift RecEval RecFix

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- The alternatives of the fixpoint of a recursor of a single inductive, one per constructor. -/
def recCs (minors : List RecMinor) : List (Nat × RecMinor × ConstructorArgMask) :=
  (List.range minors.length).map fun ci =>
    (ci, minors.getD ci default, Array.replicate (minors.getD ci default).fields.length .keep)

/-- The fixpoint `recFix` of a recursor of a single inductive without indices whose recursive
fields take no arguments: one λ for the major premise around the `case` (or the reduced form), the
alternative of the constructor `ci` applying the bound minor `ci` to the fields and to the
fixpoint on the recursive fields. -/
theorem recFix_shape (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors minors' : List RecMinor} {us : List Level} {F : LBTerm}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hRF : RecFixOf E B σ rv us minors' F) :
    minors' = minors ∧ minors.length = rv.numMinors ∧ minors.length = iv.ctors.length ∧
    (∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
        mi.fields.length = cv.numFields) ∧
    (∀ c ∈ recCs minors, SimpleAlt c) ∧
    ∃ indid direct nm x, IndIdOf σ iv.name = some indid ∧
      F = .fix [{ name := nm, principalArgIdx := 0, body := .lambda x (innerS direct indid
        rv.numParams (recCs minors)
        (altG (fun gi B => .bvar (B + 2 + (rv.numMinors - 1 - gi))) (fun B => .bvar (B + 1)))) }] 0 ∧
      (direct = false → ∃ l, casesSortLevel iv us = some l ∧ l.isNeverZero = true) ∧
      (direct = true → iv.ctors.length = 1 → FieldsErasable E B iv.name) ∧
      Subsingleton E B T := by
  obtain ⟨ivs, cvs', motives', members, T', ivT, j, direct, hblk', hshape', hml, hmem, -, hivT,
    hj, hd1, hd2, hss, rfl, -, -⟩ := hRF
  rw [hblk] at hblk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hblk')
  rw [hshape] at hshape'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape')
  obtain ⟨⟨x, rfl⟩, hcl, hmc, hmin⟩ := RecWhred.rec_minors henv hsub hcr hall hcT hblk hni hshape
  rw [hall, List.idxOf?_eq_some_iff] at hj
  obtain ⟨hj1, hj2, -⟩ := hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj1
  subst hj1
  have hT' : T' = T := hj2.symm
  subst hT'
  have hTiv := (RecWhred.recBlock?_single hall hblk).1
  rw [hTiv] at hivT
  cases hivT
  have hlen : minors.length = iv.ctors.length := by omega
  simp [recMembers, Option.bind_eq_some_iff] at hmem
  obtain ⟨indid, hid, masks, hmasks, rfl⟩ := hmem
  -- the minors and the masks
  have hcvs := (RecWhred.recBlock?_single hall hblk).2
  have hfl : ∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
      mi.fields.length = cv.numFields := fun i cv h => by
    obtain ⟨mi, h1, h2, -⟩ := hmin i cv h
    exact ⟨mi, h1, h2⟩
  have hcs : (List.range (min iv.ctors.length minors.length)).map (fun ci =>
      (ci, (minors.take iv.ctors.length)[ci]?.getD default, masks[ci]?.getD #[])) = recCs minors := by
    unfold recCs
    rw [← hlen, Nat.min_self, List.take_length]
    refine List.map_congr_left fun ci hci => ?_
    have hci' := List.mem_range.1 hci
    simp only [List.getD_eq_getElem?_getD, Prod.mk.injEq, true_and]
    obtain ⟨n, hn⟩ : ∃ n, iv.ctors[ci]? = some n := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hml', hmget⟩ := RecWhred.mapM_get hmasks
    obtain ⟨mk, hmk, hfk⟩ := hmget ci n hn
    obtain ⟨-, hcget⟩ := RecWhred.mapM_get hcvs
    obtain ⟨cv, hcv, hcvd⟩ := hcget ci n hn
    obtain ⟨mi, hmi, hmf⟩ := hfl ci cv hcv
    rw [hmk, hmi]
    simp only [Option.getD_some]
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hfk
    unfold ctorFields at hk
    unfold EvalEnv.ctorOf? at hcvd
    split at hcvd
    · rename_i cv' hcv'
      cases hcvd
      rw [hcv'] at hk
      cases hk
      rw [hmf]
    · cases hcvd
  have hsimple : ∀ c ∈ recCs minors, SimpleAlt c := by
    intro c hc
    unfold recCs at hc
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
    have hci' := List.mem_range.1 hci
    obtain ⟨cv, hcv⟩ : ∃ cv, cvs[ci]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by rw [hcl]; omega)⟩
    obtain ⟨mi, hmi, -, hle, hmem0⟩ := hmin ci cv hcv
    rw [List.getD_eq_getElem?_getD, hmi, Option.getD_some]
    simp only [SimpleAlt]
    refine ⟨trivial, fun h hh => ⟨?_, hmem0 h hh, ?_⟩⟩
    · have := hihs mi (List.mem_of_getElem? hmi)
      have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [this] at hm
      obtain ⟨f, -, hf⟩ := List.mem_map.1 hm
      exact (Prod.mk.inj hf).2.symm
    · have := hihs mi (List.mem_of_getElem? hmi)
      have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [this] at hm
      obtain ⟨f, hf, hf'⟩ := List.mem_map.1 hm
      rw [List.mem_range'_1] at hf
      have := (Prod.mk.inj hf').1
      omega
  refine ⟨rfl, hml, hlen, hfl, hsimple, indid, direct, fixDefName (mkRecName iv.name),
    binderNameOf x, hid, ?_,
    fun h => hd1 h, fun h h1 => hd2 h iv (.head _) h1, hss _ (by rw [hall]; exact .head _)⟩
  rw [recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.foldr_cons,
    List.foldr_nil, Nat.sub_self, Nat.zero_add]
  rw [hcs]
  congr 4
  refine innerS_congr fun c hc => ?_
  exact altF_simple _ ⟨iv.name, [x], indid, recCs minors⟩ rfl (hsimple c hc)

end SimRec

end EraseProof
