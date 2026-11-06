import EraseProof.Bridge.Apps
import EraseProof.Bridge.Inst
import EraseProof.Bridge.Levels

/-!
# Quotient constants in the bridge

A program's quotient constants are bound to one quotient entry of the Metalean environment, at
their kinds (`ProgEnv.lookup_quot`, `ProgEnv.quot_bound`, `ProgEnv.quot_head_unique`): `ProgEnv.quot`
binds the four names `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and a second quotient entry would
bind them again. The translation of an application whose head is a saturated quotient spine is the
application of the translations (`TrM.wf_app_quot`), as `saturate` applies the node to the
arguments beyond the arity (`ML Frontend/Translate.lean:226`).
-/

open Lean Erasure
open Metalean (Defeq EnvWF)

namespace EraseProof

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- A weakened binding of a quotient entry is a binding of the entry before. -/
theorem MBinding.wk_quot_inv {sig : Metalean.Sig} {b : MBinding ζ}
    {η : Metalean.Head (ζ.snoc sig) .quot} {k : Metalean.Export.QuotKind}
    (h : b.wk = .quot η k) : ∃ η₀, b = .quot η₀ k ∧ η = η₀.there := by
  cases b with
  | quot η₀ k₀ => cases h; exact ⟨η₀, rfl, rfl⟩
  | _ => cases h

/-- A weakened table binds a name to a quotient entry only if the table did. -/
theorem Binds.wk_quot_inv {sig : Metalean.Sig} {x : Option (MBinding ζ)}
    {η : Metalean.Head (ζ.snoc sig) .quot} {k : Metalean.Export.QuotKind}
    (h : x.map MBinding.wk = some (.quot η k)) :
    ∃ η₀, x = some (.quot η₀ k) ∧ η = η₀.there := by
  obtain ⟨b, hb, hw⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨η₀, rfl, rfl⟩ := MBinding.wk_quot_inv hw
  exact ⟨η₀, hb, rfl⟩

/-- A quotient constant of the program is bound to a quotient entry at its kind. -/
theorem ProgEnv.lookup_quot (h : ProgEnv P ζ E B) {c : Name} {q : QuotVal}
    (hc : findDecl P c = some (.quotInfo q)) : ∃ η, B c = some (.quot η (quotKindOf q.kind)) := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨η, hB⟩ := ih hc
      exact ⟨η.there, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      exact ⟨η.there, by rw [hext c hnot, Binds.wk, hB]; rfl⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext hq ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp only [List.map_reverse, List.mem_reverse, List.mem_map] at hm
      obtain ⟨q', hq', heq⟩ := hm
      cases heq
      exact ⟨.here, by rw [← hn]; exact (hq q hq').1⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      exact ⟨η.there, by rw [hext c hnot, Binds.wk, hB]; rfl⟩

/-- A name bound to a quotient entry is a quotient constant of the program, of the entry's kind,
and one of the four quotient names. -/
theorem ProgEnv.quot_bound (h : ProgEnv P ζ E B) {c : Name} {η : Metalean.Head ζ .quot}
    {k : Metalean.Export.QuotKind} (hb : B c = some (.quot η k)) :
    ∃ q, findDecl P c = some (.quotInfo q) ∧ k = quotKindOf q.kind ∧
      c ∈ [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] := by
  induction h with
  | nil => simp at hb
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    by_cases hn : c = v.name
    · simp [Binds.set, hn] at hb
    · rw [set_wk_ne hn] at hb
      obtain ⟨η₀, hb₀, -⟩ := Binds.wk_quot_inv hb
      obtain ⟨q, hq, hk, hmem⟩ := ih hb₀
      refine ⟨q, ?_, hk, hmem⟩
      rw [findDecl_cons]
      split
      · rename_i h'; exact absurd (h' ▸ rfl : c = _) hn
      · exact hq
  | @induct _ _ _ _ ι _ B' _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    by_cases hn : c ∈ (IndBlock.decls Is Cs Rs).map (·.name)
    · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
      rcases IndBlock.mem_decls hci with ⟨s, rfl⟩ | ⟨s, j, rfl⟩ | ⟨s, rfl⟩
      · have h1 : B' (ConstantInfo.recInfo (Rs s)).name = _ := (hblk.recr s).2.1
        rw [h1] at hb; cases hb
      · have h1 : B' (ConstantInfo.ctorInfo (Cs s j)).name = _ := (hblk.ctor s j).1
        rw [h1] at hb; cases hb
      · have h1 : B' (ConstantInfo.inductInfo (Is s)).name = _ := (hblk.ind s).1
        rw [h1] at hb; cases hb
    · rw [hext c hn, Binds.wk] at hb
      obtain ⟨η₀, hb₀, -⟩ := Binds.wk_quot_inv hb
      obtain ⟨q, hq, hk, hmem⟩ := ih hb₀
      refine ⟨q, ?_, hk, hmem⟩
      rw [findDecl_append]
      have hd : findDecl (IndBlock.decls Is Cs Rs) c = none := by
        cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
        | none => rfl
        | some ci =>
          obtain ⟨hm, hn'⟩ := findDecl_eq_some hd
          exact absurd (List.mem_map.mpr ⟨ci, hm, hn'⟩) hn
      rw [hd]
      exact hq
  | @quot ζ₀ _ _ _ _ qs B' hP _ hnames hfr _ hext hq ih =>
    by_cases hn : c ∈ qs.map (·.name)
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hn
      rw [(hq q hq').1] at hb
      cases hb
      refine ⟨q, ?_, rfl, hnames ▸ hn⟩
      rw [findDecl_append]
      have hmem : ConstantInfo.quotInfo q ∈ qs.reverse.map ConstantInfo.quotInfo := by
        simp [hq']
      have hnd : ((qs.reverse.map ConstantInfo.quotInfo).map (·.name)).Nodup := by
        rw [quot_names_reverse, List.nodup_reverse, hnames]
        decide
      obtain ⟨ci, hci⟩ : ∃ ci, findDecl (qs.reverse.map ConstantInfo.quotInfo) q.name = some ci :=
        Option.isSome_iff_exists.mp (by
          unfold findDecl
          rw [List.find?_isSome]
          exact ⟨_, hmem, beq_self_eq_true _⟩)
      obtain ⟨hcm, hcn⟩ := findDecl_eq_some hci
      have : ci = .quotInfo q := by
        refine List.inj_on_of_nodup_map hnd hcm hmem ?_
        rw [hcn]; rfl
      rw [hci, this]; rfl
    · rw [hext c hn, Binds.wk] at hb
      obtain ⟨η₀, hb₀, -⟩ := Binds.wk_quot_inv hb
      obtain ⟨q, hq', hk, hmem⟩ := ih hb₀
      exact absurd (hnames ▸ hmem) hn

/-- The names bound to quotient entries are bound to one entry. -/
theorem ProgEnv.quot_head_unique (h : ProgEnv P ζ E B) {c c' : Name}
    {η η' : Metalean.Head ζ .quot} {k k' : Metalean.Export.QuotKind}
    (h₁ : B c = some (.quot η k)) (h₂ : B c' = some (.quot η' k')) : η = η' := by
  induction h with
  | nil => simp at h₁
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    by_cases hn : c = v.name
    · simp [Binds.set, hn] at h₁
    by_cases hn' : c' = v.name
    · simp [Binds.set, hn'] at h₂
    rw [set_wk_ne hn] at h₁
    rw [set_wk_ne hn'] at h₂
    obtain ⟨η₀, hb₀, rfl⟩ := Binds.wk_quot_inv h₁
    obtain ⟨η₀', hb₀', rfl⟩ := Binds.wk_quot_inv h₂
    rw [ih hb₀ hb₀']
  | @induct _ _ _ _ ι _ B' _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    have notin : ∀ {x : Name} {θ : Metalean.Head _ .quot} {j : Metalean.Export.QuotKind},
        B' x = some (.quot θ j) → x ∉ (IndBlock.decls Is Cs Rs).map (·.name) := by
      intro x θ j hx hn
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
      rcases IndBlock.mem_decls hci with ⟨s, rfl⟩ | ⟨s, j, rfl⟩ | ⟨s, rfl⟩
      · have h1 : B' (ConstantInfo.recInfo (Rs s)).name = _ := (hblk.recr s).2.1
        rw [h1] at hx; cases hx
      · have h1 : B' (ConstantInfo.ctorInfo (Cs s j)).name = _ := (hblk.ctor s j).1
        rw [h1] at hx; cases hx
      · have h1 : B' (ConstantInfo.inductInfo (Is s)).name = _ := (hblk.ind s).1
        rw [h1] at hx; cases hx
    have hn := notin h₁
    have hn' := notin h₂
    rw [hext c hn, Binds.wk] at h₁
    rw [hext c' hn', Binds.wk] at h₂
    obtain ⟨η₀, hb₀, rfl⟩ := Binds.wk_quot_inv h₁
    obtain ⟨η₀', hb₀', rfl⟩ := Binds.wk_quot_inv h₂
    rw [ih hb₀ hb₀']
  | @quot ζ₀ _ _ _ _ qs B' hP _ hnames hfr _ hext hq ih =>
    have side : ∀ {x : Name} {θ : Metalean.Head (ζ₀.snoc .quot) .quot}
        {j : Metalean.Export.QuotKind}, B' x = some (.quot θ j) → θ = .here := by
      intro x θ j hx
      by_cases hn : x ∈ qs.map (·.name)
      · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hn
        rw [(hq q hq').1] at hx
        cases hx; rfl
      · rw [hext x hn, Binds.wk] at hx
        obtain ⟨θ₀, hb₀, -⟩ := Binds.wk_quot_inv hx
        obtain ⟨-, -, -, hmem⟩ := hP.quot_bound hb₀
        exact absurd (hnames ▸ hmem) hn
    rw [side h₁, side h₂]

/-- The number of universe levels of a quotient constant (`quotTerm`,
`ML Frontend/Translate.lean:197`). -/
def quotLevels : Metalean.Export.QuotKind → Nat
  | .lift => 2
  | _ => 1

/-- A successful `quotTerm` has the kind's number of levels. -/
theorem quotTerm_levels {ℓ : Nat} {η : Metalean.Head ζ .quot}
    {eqHead : Metalean.Head ζ (.inductive Metalean.Eq.sig)} {k : Metalean.Export.QuotKind}
    {ls : List (Metalean.Level ℓ)} {t : Metalean.Expr ζ ℓ 0}
    (h : Metalean.Frontend.quotTerm η eqHead k ls = .ok t) : ls.length = quotLevels k := by
  rcases ls with _ | ⟨u, _ | ⟨v, _ | ⟨w, ls⟩⟩⟩ <;> cases k <;> first | rfl | (cases h; done)

/-- A translated quotient spine has the kind's number of levels. -/
theorem SatTr.quot_levels {lps : List Name} {n : Nat} {η : Metalean.Head ζ .quot}
    {k : Metalean.Export.QuotKind} {us : List Level} {args : List (Metalean.Expr ζ lps.length n)}
    {t : Metalean.Expr ζ lps.length n} (h : SatTr E lps (.quot η k) us args t) :
    us.length = quotLevels k := by
  cases h with
  | quotType hu | quotMk hu | quotInd hu | quotLift hu =>
    have := (mapM_option_get hu).1; simp at this; simp [quotLevels]; omega
  | quotEta hu _ ht => rw [← (mapM_option_get hu).1]; exact quotTerm_levels ht

/-- A quotient constant of the program has its kind's number of universe parameters. -/
theorem ProgEnv.quot_levels (h : ProgEnv P ζ E B) {c : Name} {q : QuotVal}
    (hc : findDecl P c = some (.quotInfo q)) :
    q.levelParams.length = quotLevels (quotKindOf q.kind) := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · exact ih hc
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      exact ih hc
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext hq ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp only [List.map_reverse, List.mem_reverse, List.mem_map] at hm
      obtain ⟨q', hq', heq⟩ := hm
      cases heq
      obtain ⟨hB, -, t₀, -, ht₀, -⟩ := hq q hq'
      have ht₀' : TrM _ _ q.levelParams .nil []
          (mkAppN (.const q.name (q.levelParams.map .param)) ([] : List Lean.Expr).toArray) t₀ :=
        ht₀
      obtain ⟨_, -, -, hsat⟩ := TrM.special_inv hB rfl ht₀'
      simpa using hsat.quot_levels
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      exact ih hc

/-- Splitting the last element off a list that extends a shorter prefix. -/
theorem split_last {α : Type} {bs pre rest : List α} {a : α} (h : bs ++ [a] = pre ++ rest)
    (hle : pre.length ≤ bs.length) : ∃ r, bs = pre ++ r ∧ rest = r ++ [a] := by
  obtain ⟨r, hr⟩ : ∃ r, bs = pre ++ r :=
    ⟨bs.drop pre.length, by
      have := congrArg (List.take pre.length) h
      rw [List.take_append_of_le_length hle, List.take_left' rfl] at this
      conv_lhs => rw [← List.take_append_drop pre.length bs, this]⟩
  subst hr
  rw [List.append_assoc] at h
  exact ⟨r, rfl, (List.append_cancel_left h).symm⟩

/-- An application whose head is a quotient spine with at least its arity of arguments translates
to the application of the translations (`saturate`, `ML Frontend/Translate.lean:226`, applies the
node to the arguments beyond the arity). -/
theorem TrM.wf_app_quot {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {c : Name} {us : List Level} {bs : List Lean.Expr} {a : Lean.Expr}
    {η : Metalean.Head ζ .quot} {k : Metalean.Export.QuotKind}
    {t T : Metalean.Expr ζ lps.length n} (hb : B c = some (.quot η k))
    (hk : quotArity k ≤ bs.length)
    (he : TrM E B lps Γ Δ (.app (mkAppN (.const c us) bs.toArray) a) t) (ht : E[Γ] ⊢ t : T) :
    ∃ f' a', TrM E B lps Γ Δ (mkAppN (.const c us) bs.toArray) f' ∧ TrM E B lps Γ Δ a a' ∧
      t = .app f' a' ∧ (∃ F, E[Γ] ⊢ f' : F) ∧ ∃ A, E[Γ] ⊢ a' : A := by
  have hsnoc : Expr.app (mkAppN (.const c us) bs.toArray) a =
      mkAppN (.const c us) (bs ++ [a]).toArray := by
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl
  rw [hsnoc] at he
  obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hb rfl he
  obtain ⟨bs', a', rfl⟩ : ∃ bs' a', as' = bs' ++ [a'] := by
    rcases as'.eq_nil_or_concat with h | ⟨L, x, h⟩
    · subst h; simp at hlen
    · exact ⟨L, x, by simp [h]⟩
  simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
  have hargs' : ∀ (i : Nat) x x', bs[i]? = some x → bs'[i]? = some x' → TrM E B lps Γ Δ x x' :=
    fun i x x' hx hx' => hargs i x x'
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx)
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx').1]; exact hx')
  have ha : TrM E B lps Γ Δ a a' := hargs bs.length a a' (by simp) (by simp [hlen])
  -- the node with the arguments beyond the arity, the last one split off
  obtain ⟨f', hsat', rfl⟩ : ∃ f', SatTr E lps (.quot η k) us bs' f' ∧ t = .app f' a' := by
    have hk' : quotArity k ≤ bs'.length := hlen ▸ hk
    generalize hl : bs' ++ [a'] = l at hsat
    cases hsat with
    | quotEta _ hlt => subst hl; simp at hlt; omega
    | quotType hu | quotMk hu | quotLift hu | quotInd hu =>
      obtain ⟨r, rfl, rfl⟩ := split_last hl (by simp [quotArity] at hk' ⊢; omega)
      exact ⟨_, by first | exact .quotType hu | exact .quotMk hu | exact .quotLift hu |
        exact .quotInd hu, by rw [TrApps.appList_append]; rfl⟩
  obtain ⟨_, _, hf', ha', -⟩ := ht.app_inv
  exact ⟨f', a', .special hb rfl hlen hargs' hsat', ha, rfl, ⟨_, hf'⟩, _, ha'⟩

end EraseProof
