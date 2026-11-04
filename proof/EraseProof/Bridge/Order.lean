import EraseProof.Bridge.ProgEnv

/-!
# Field orders of the table

Every constructor binding of a table that `ProgEnv` builds carries Metalean's field order
(`MetaOrderOK`, in particular a permutation of the fields): the premise `hord` of `TrM.inst` and
`TrM.inst_let`. The orders come from the blocks (`IndBlock.ctor`); weakening the table keeps them.
-/

open Lean

namespace EraseProof

/-- A constructor binding of a weakened table is the weakening of one of the old table. -/
private theorem wk_ctor {ζ : Metalean.Sigs} {sig : Metalean.Sig} {x : Option (MBinding ζ)}
    {ι : Metalean.IndSig} {η : Metalean.Head (ζ.snoc sig) (.inductive ι)} {s : Fin ι.nsorts}
    {k : Fin (ι.nctors s)} {o : List Nat} (h : x.map MBinding.wk = some (.ctor η s k o)) :
    ∃ η', x = some (.ctor η' s k o) := by
  rcases x with _ | b
  · cases h
  · cases b <;> simp only [Option.map_some, MBinding.wk, Option.some.injEq, reduceCtorEq] at h
    cases h
    exact ⟨_, rfl⟩

/-- Every constructor binding of the table has Metalean's field order for its constructor
(`metaOrderOf`, `ML Frontend/Inductive.lean:135`). -/
theorem ProgEnv.metaOrderOK {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} (h : ProgEnv P ζ E B) :
    ∀ c {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields := by
  induction h with
  | nil => intro c _ _ _ _ _ hc; cases hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ ih =>
    intro c ι η s k o hc
    by_cases hn : c = v.name
    · simp [Binds.set, hn] at hc
    · rw [set_wk_ne hn] at hc
      obtain ⟨η', hB⟩ := wk_ctor hc
      exact ih c η' s k o hB
  | @induct _ _ _ _ ι₀ _ _ _ Is Cs Rs _ _ _ _ hext hblk _ ih =>
    intro c ι η s k o hc
    by_cases hn : c ∈ (IndBlock.decls Is Cs Rs).map (·.name)
    · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
      rcases IndBlock.mem_decls hci with ⟨s', rfl⟩ | ⟨s', k', rfl⟩ | ⟨s', rfl⟩
      · rw [show (ConstantInfo.recInfo (Rs s')).name = (Rs s').name from rfl,
          (hblk.recr s').2.1] at hc
        cases hc
      · obtain ⟨hB, -, -, -, -, -, -, hmo⟩ := hblk.ctor s' k'
        rw [show (ConstantInfo.ctorInfo (Cs s' k')).name = (Cs s' k').name from rfl, hB] at hc
        cases hc
        exact hmo
      · rw [show (ConstantInfo.inductInfo (Is s')).name = (Is s').name from rfl,
          (hblk.ind s').1] at hc
        cases hc
    · rw [hext c hn] at hc
      obtain ⟨η', hB⟩ := wk_ctor hc
      exact ih c η' s k o hB
  | @quot _ _ _ _ _ qs _ _ _ _ _ hext hq ih =>
    intro c ι η s k o hc
    by_cases hn : c ∈ qs.map (·.name)
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hn
      rw [(hq q hq').1] at hc; cases hc
    · rw [hext c hn] at hc
      obtain ⟨η', hB⟩ := wk_ctor hc
      exact ih c η' s k o hB

end EraseProof
