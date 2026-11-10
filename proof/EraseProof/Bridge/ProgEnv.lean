import EraseProof.Spec

/-!
# `ProgEnv`: lookups

What `ProgEnv P ζ E B` says about a declaration found in the program `P`: its names are distinct
(`ProgEnv.fresh`), and the table `B` binds an inductive type to its Metalean sort
(`ProgEnv.lookup_ind`), to no other name (`ProgEnv.ind_inj`), and a constructor to its Metalean
constructor with its counts and field order (`ProgEnv.lookup_ctor`). Reference:
`declared_inductive`, `declared_constructor` (`MR P/PCUICTyping.v`), MC §3.6.
-/

open Lean

namespace EraseProof

/-- `findDecl` on a cons. -/
theorem findDecl_cons (x : ConstantInfo) (l : List ConstantInfo) (c : Name) :
    findDecl (x :: l) c = if x.name = c then some x else findDecl l c := by
  by_cases h : x.name = c <;> simp [findDecl, h]

/-- `findDecl` on an append. -/
theorem findDecl_append (l₁ l₂ : List ConstantInfo) (c : Name) :
    findDecl (l₁ ++ l₂) c = (findDecl l₁ c).or (findDecl l₂ c) :=
  List.find?_append

/-- A found declaration is a member with that name. -/
theorem findDecl_eq_some {l : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (h : findDecl l c = some ci) : ci ∈ l ∧ ci.name = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A name that is not found is not a name of the list. -/
theorem not_mem_of_findDecl_none {l : List ConstantInfo} {c : Name} (h : findDecl l c = none) :
    c ∉ l.map (·.name) := by
  simp only [findDecl, List.find?_eq_none, beq_iff_eq] at h
  simp only [List.mem_map, not_exists, not_and]
  exact fun ci hci heq => h ci hci heq

/-- The extended table on an old name. -/
theorem set_wk_ne {ζ : Metalean.Sigs} {sig : Metalean.Sig} {B : Binds ζ} {n c : Name}
    {b : MBinding (ζ.snoc sig)} (h : c ≠ n) : (B.wk.set n b) c = (B c).map MBinding.wk := by
  simp [Binds.set, Binds.wk, h]

/-- The names of the quotient declarations as `ProgEnv.quot` adds them. -/
theorem quot_names_reverse {qs : List QuotVal} :
    (qs.reverse.map ConstantInfo.quotInfo).map (·.name) = (qs.map (·.name)).reverse := by
  simp only [List.map_reverse, List.map_map]; rfl

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- The table binds only names of the program. -/
theorem ProgEnv.bound (h : ProgEnv P ζ E B) {c : Name} (hc : B c ≠ none) :
    c ∈ P.map (·.name) := by
  induction h with
  | nil => simp at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    by_cases hn : c = v.name
    · exact hn ▸ List.mem_cons_self
    · rw [set_wk_ne hn] at hc
      exact List.mem_cons_of_mem _ (ih (by simpa using hc))
  | @induct _ _ _ _ _ _ _ _ Is Cs Rs _ _ _ _ _ hext _ _ ih =>
    rw [List.map_append]
    by_cases hn : c ∈ (IndBlock.decls Is Cs Rs).map (·.name)
    · exact List.mem_append_left _ hn
    · rw [hext c hn] at hc
      exact List.mem_append_right _ (ih (by simpa [Binds.wk] using hc))
  | @quot _ _ _ _ _ qs _ _ _ _ _ _ hext _ ih =>
    rw [List.map_append]
    by_cases hn : c ∈ qs.map (·.name)
    · exact List.mem_append_left _ (by rw [quot_names_reverse]; exact List.mem_reverse.mpr hn)
    · rw [hext c hn] at hc
      exact List.mem_append_right _ (ih (by simpa [Binds.wk] using hc))

/-- The program's names are distinct. Reference: `fresh_global` (`MR common/theories/Environment.v`,
`wf_ext`). -/
theorem ProgEnv.fresh (h : ProgEnv P ζ E B) : (P.map (·.name)).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | «axiom» _ hfr _ _ _ ih | defn _ hfr _ _ _ _ _ ih | thm _ hfr _ _ _ _ _ ih
  | «opaque» _ hfr _ _ _ _ _ _ ih =>
    exact List.nodup_cons.mpr ⟨not_mem_of_findDecl_none hfr, ih⟩
  | induct _ hnd hfr _ _ _ _ ih =>
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hnd, ih, ?_⟩
    intro a ha b hb hab
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp ha
    exact not_mem_of_findDecl_none (hfr ci hci) (hab ▸ hb)
  | quot _ _ hq hfr _ _ _ ih =>
    rw [List.map_append, quot_names_reverse, hq]
    refine List.nodup_append.mpr ⟨by decide, ih, ?_⟩
    intro a ha b hb hab
    rw [← hq, List.mem_reverse] at ha
    obtain ⟨q, hq', rfl⟩ := List.mem_map.mp ha
    exact not_mem_of_findDecl_none (hfr q hq') (hab ▸ hb)

/-- The universe parameters of every declaration of the program are distinct. Reference: Lean's
kernel, `environment::check_duplicated_univ_params`. -/
theorem ProgEnv.levelParams_nodup (h : ProgEnv P ζ E B) {ci : ConstantInfo} (hci : ci ∈ P) :
    ci.levelParams.Nodup := by
  induction h with
  | nil => cases hci
  | «axiom» _ _ hnd _ _ ih | defn _ _ hnd _ _ _ _ ih | thm _ _ hnd _ _ _ _ ih
  | «opaque» _ _ hnd _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hci with rfl | h
    · exact hnd
    · exact ih h
  | induct _ _ _ hnd _ _ _ ih =>
    rcases List.mem_append.mp hci with h | h
    · exact hnd _ h
    · exact ih h
  | quot _ _ _ _ hnd _ _ ih =>
    rcases List.mem_append.mp hci with h | h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact hnd q (List.mem_reverse.mp hq)
    · exact ih h

/-- A declaration of an inductive block is one of its types, constructors or recursors. -/
theorem IndBlock.mem_decls {ι : Metalean.IndSig} {Is : Fin ι.nsorts → InductiveVal}
    {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal} {Rs : Fin ι.nsorts → RecursorVal}
    {ci : ConstantInfo} (h : ci ∈ IndBlock.decls Is Cs Rs) :
    (∃ s, ci = .recInfo (Rs s)) ∨ (∃ s c, ci = .ctorInfo (Cs s c)) ∨ ∃ s, ci = .inductInfo (Is s) := by
  simp only [IndBlock.decls, List.mem_append, List.mem_ofFn, List.mem_flatten] at h
  rcases h with (⟨s, rfl⟩ | ⟨l, ⟨s, rfl⟩, hl⟩) | ⟨s, rfl⟩
  · exact .inl ⟨s, rfl⟩
  · obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
    exact .inr (.inl ⟨s, c, rfl⟩)
  · exact .inr (.inr ⟨s, rfl⟩)

/-- An inductive type is bound to its Metalean sort, with its counts. Reference:
`declared_inductive` (MC §3.6). -/
theorem ProgEnv.lookup_ind {c : Name} {iv : InductiveVal} (h : ProgEnv P ζ E B)
    (hc : findDecl P c = some (.inductInfo iv)) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts),
      B c = some (.ind η s) ∧ iv.numParams = ι.nparams ∧ iv.numIndices = ι.nindices s ∧
      iv.ctors.length = ι.nctors s := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨ι, η, s, hB, h1⟩ := ih hc
      exact ⟨ι, η.there, s, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, h1⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
      obtain ⟨hB, -, -, hp, hi, hcs, -⟩ := hblk.ind s
      exact ⟨ι, .here, s, hn ▸ hB, hp, hi, by simp [hcs]⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨ι', η, s, hB, h1⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      exact ⟨ι', η.there, s, by rw [hext c hnot, Binds.wk, hB]; rfl, h1⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp at hm
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨ι', η, s, hB, h1⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      exact ⟨ι', η.there, s, by rw [hext c hnot, Binds.wk, hB]; rfl, h1⟩

/-- A constructor is bound to its Metalean constructor, with its counts and Metalean field order,
and its inductive type to the constructor's sort. Reference: `declared_constructor` (MC §3.6). -/
theorem ProgEnv.lookup_ctor {c : Name} {cv : ConstructorVal} (h : ProgEnv P ζ E B)
    (hc : findDecl P c = some (.ctorInfo cv)) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (order : List Nat), B c = some (.ctor η s k order) ∧
      cv.cidx = k.val ∧ cv.numParams = ι.nparams ∧
      cv.numFields = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields ∧
      MetaOrderOK order (ι.ctors s k).nfields (ι.ctors s k).nrecFields ∧
      B cv.induct = some (.ind η s) := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ hP hfr _ _ _ ih | @defn _ _ _ _ v _ _ hP hfr _ _ _ _ _ ih
  | @thm _ _ _ _ v _ hP hfr _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ hP hfr _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨ι, η, s, k, o, hB, h1, h2, h3, h4, hI⟩ := ih hc
      have hne : cv.induct ≠ v.name := fun he =>
        not_mem_of_findDecl_none hfr (he ▸ hP.bound (by simp [hI]))
      exact ⟨ι, η.there, s, k, o, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, h1, h2, h3, h4,
        by rw [set_wk_ne hne, hI]; rfl⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
      obtain ⟨hB, -, hind, hcidx, hp, hf, -, hmo⟩ := hblk.ctor s k
      exact ⟨ι, .here, s, k, _, hn ▸ hB, hcidx, hp, hf, hmo, hind ▸ (hblk.ind s).1⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨ι', η, s, k, o, hB, h1, h2, h3, h4, hI⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      have hnotI : cv.induct ∉ (IndBlock.decls Is Cs Rs).map (·.name) := fun hm => by
        obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hm
        exact not_mem_of_findDecl_none (hfr ci hci) (hn ▸ hP.bound (by simp [hI]))
      exact ⟨ι', η.there, s, k, o, by rw [hext c hnot, Binds.wk, hB]; rfl, h1, h2, h3, h4,
        by rw [hext _ hnotI, Binds.wk, hI]; rfl⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp at hm
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨ι', η, s, k, o, hB, h1, h2, h3, h4, hI⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      have hnotI : cv.induct ∉ qs.map (·.name) := fun hm => by
        obtain ⟨q, hq, hn⟩ := List.mem_map.mp hm
        exact not_mem_of_findDecl_none (hfr q hq) (hn ▸ hP.bound (by simp [hI]))
      exact ⟨ι', η.there, s, k, o, by rw [hext c hnot, Binds.wk, hB]; rfl, h1, h2, h3, h4,
        by rw [hext _ hnotI, Binds.wk, hI]; rfl⟩

/-- A weakened binding of an inductive sort weakens one. -/
theorem wk_ind {ζ : Metalean.Sigs} {sig : Metalean.Sig} {b : Option (MBinding ζ)}
    {ι : Metalean.IndSig} {η : Metalean.Head (ζ.snoc sig) (.inductive ι)} {s : Fin ι.nsorts}
    (h : b.map MBinding.wk = some (.ind η s)) :
    ∃ η₀ : Metalean.Head ζ (.inductive ι), η = η₀.there ∧ b = some (.ind η₀ s) := by
  obtain ⟨b, rfl, hb⟩ := Option.map_eq_some_iff.mp h
  cases b with
  | ind η₀ s₀ =>
    simp only [MBinding.wk, MBinding.ind.injEq] at hb
    obtain ⟨rfl, h1, h2⟩ := hb
    cases h1; cases h2
    exact ⟨η₀, rfl, rfl⟩
  | const | ctor | recr | quot => simp [MBinding.wk] at hb

/-- The table binds a Metalean inductive sort to at most one name. -/
theorem ProgEnv.ind_inj (h : ProgEnv P ζ E B) {ι : Metalean.IndSig} {s : Fin ι.nsorts} :
    ∀ {η : Metalean.Head ζ (.inductive ι)} {x y : Name}, B x = some (.ind η s) →
      B y = some (.ind η s) → x = y := by
  induction h with
  | nil => intro _ _ _ hx; simp at hx
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ _ _ ih =>
    intro η x y hx hy
    have hxn : x ≠ v.name := by rintro rfl; simp [Binds.set] at hx
    have hyn : y ≠ v.name := by rintro rfl; simp [Binds.set] at hy
    rw [set_wk_ne hxn] at hx
    rw [set_wk_ne hyn] at hy
    obtain ⟨η₀, rfl, hx'⟩ := wk_ind hx
    obtain ⟨η₁, hη, hy'⟩ := wk_ind hy
    cases hη
    exact ih hx' hy'
  | @induct _ _ _ _ ι' _ B' _ Is Cs Rs _ _ _ _ _ hext hblk _ ih =>
    intro η x y hx hy
    have inBlock : ∀ {z : Name} {η' : Metalean.Head _ (.inductive ι)},
        z ∈ (IndBlock.decls Is Cs Rs).map (·.name) → B' z = some (.ind η' s) →
        ∃ t, z = (Is t).name ∧ B' z = some (.ind .here t) := by
      intro z η' hz hb
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hz
      rcases IndBlock.mem_decls hci with ⟨t, rfl⟩ | ⟨t, c, rfl⟩ | ⟨t, rfl⟩
      · rw [show (ConstantInfo.recInfo (Rs t)).name = (Rs t).name from rfl,
          (hblk.recr t).2.1] at hb
        cases hb
      · rw [show (ConstantInfo.ctorInfo (Cs t c)).name = (Cs t c).name from rfl,
          (hblk.ctor t c).1] at hb
        cases hb
      · exact ⟨t, rfl, (hblk.ind t).1⟩
    by_cases hxm : x ∈ (IndBlock.decls Is Cs Rs).map (·.name) <;>
      by_cases hym : y ∈ (IndBlock.decls Is Cs Rs).map (·.name)
    · obtain ⟨t, rfl, hxt⟩ := inBlock hxm hx
      obtain ⟨t', rfl, hyt⟩ := inBlock hym hy
      rw [hxt] at hx
      rw [hyt] at hy
      simp only [Option.some.injEq, MBinding.ind.injEq] at hx hy
      obtain ⟨rfl, h1, h2⟩ := hx
      cases h1; cases h2
      obtain ⟨-, -, h3⟩ := hy
      cases h3
      rfl
    · obtain ⟨t, rfl, hxt⟩ := inBlock hxm hx
      rw [hxt] at hx
      simp only [Option.some.injEq, MBinding.ind.injEq] at hx
      obtain ⟨rfl, h1, h2⟩ := hx
      cases h1; cases h2
      rw [hext y hym] at hy; simp only [Binds.wk] at hy
      obtain ⟨η₀, hη, -⟩ := wk_ind hy
      cases hη
    · obtain ⟨t, rfl, hyt⟩ := inBlock hym hy
      rw [hyt] at hy
      simp only [Option.some.injEq, MBinding.ind.injEq] at hy
      obtain ⟨rfl, h1, h2⟩ := hy
      cases h1; cases h2
      rw [hext x hxm] at hx; simp only [Binds.wk] at hx
      obtain ⟨η₀, hη, -⟩ := wk_ind hx
      cases hη
    · rw [hext x hxm] at hx; simp only [Binds.wk] at hx
      rw [hext y hym] at hy; simp only [Binds.wk] at hy
      obtain ⟨η₀, rfl, hx'⟩ := wk_ind hx
      obtain ⟨η₁, hη, hy'⟩ := wk_ind hy
      cases hη
      exact ih hx' hy'
  | @quot _ _ _ _ _ qs B' _ _ _ _ _ hext hq ih =>
    intro η x y hx hy
    have hout : ∀ {z : Name} {η' : Metalean.Head _ (.inductive ι)}, B' z = some (.ind η' s) →
        z ∉ qs.map (·.name) := by
      intro z η' hz hm
      obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hm
      rw [(hq q hq').1] at hz
      cases hz
    rw [hext x (hout hx)] at hx; simp only [Binds.wk] at hx
    rw [hext y (hout hy)] at hy; simp only [Binds.wk] at hy
    obtain ⟨η₀, rfl, hx'⟩ := wk_ind hx
    obtain ⟨η₁, hη, hy'⟩ := wk_ind hy
    cases hη
    exact ih hx' hy'

end EraseProof
