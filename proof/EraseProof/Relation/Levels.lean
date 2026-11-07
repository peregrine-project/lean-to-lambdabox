import EraseProof.Bridge.Levels
import EraseProof.Erasable.Levels
import EraseProof.Relation.Extend
import EraseProof.Bridge.Quot
import EraseProof.Bridge.RecWhred
import EraseProof.Bridge.Lookup

/-!
# Universe instantiation of the erasure relation

An erasure of a closed translated term at universe parameters `lps'` is an erasure of its universe
instantiation (`Pure.instLevels lps' us`) at `lps`, with the same λ□ term (`Erases.instLevels`).
The only rule that reads levels is the η-expansion of a constructor or recognized `casesOn` spine,
which instantiates the declaration's type at the spine's levels; it commutes with the
instantiation because the spine's levels have the length of the declaration's level parameters
(the term translates, `TrM`) and the declared type's levels are among them (`ProgEnv`).
`¬ CasesReduced` survives because `Level.isNeverZero` is monotone under substitution.
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

namespace RelLevels

/-! ## Levels -/

theorem zip_map_find? {ps : List Name} {vs : List Level} (f : Level → Level) (p : Name) :
    (ps.zip (vs.map f)).find? (·.1 == p) =
      ((ps.zip vs).find? (·.1 == p)).map fun x => (x.1, f x.2) := by
  rw [List.zip_map_right, List.find?_map]; rfl

theorem instLevel_param_map (ps : List Name) (vs : List Level) (f : Level → Level) (p : Name) :
    Pure.instLevel ps (vs.map f) (.param p) =
      match (ps.zip vs).find? (·.1 == p) with
      | some (_, u) => f u
      | none => .param p := by
  simp only [Pure.instLevel, zip_map_find?]
  cases (ps.zip vs).find? (·.1 == p) <;> rfl

/-- `Level.isNeverZero` is stable under universe instantiation. -/
theorem isNeverZero_instLevel {ps : List Name} {vs : List Level} :
    ∀ {u : Level}, u.isNeverZero = true → (Pure.instLevel ps vs u).isNeverZero = true
  | .succ _, _ => rfl
  | .max a b, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true, Pure.instLevel] at h ⊢
    exact h.imp isNeverZero_instLevel isNeverZero_instLevel
  | .imax _ b, h => by
    simp only [Level.isNeverZero, Pure.instLevel] at h ⊢
    exact isNeverZero_instLevel (u := b) h
  | .zero, h | .param _, h | .mvar _, h => by cases h

/-- Instantiating the arguments of a universe instantiation keeps `Level.isNeverZero`. -/
theorem isNeverZero_instLevel_map {ps : List Name} {vs : List Level} {f : Level → Level}
    (hf : ∀ v, v.isNeverZero = true → (f v).isNeverZero = true) :
    ∀ {u : Level}, (Pure.instLevel ps vs u).isNeverZero = true →
      (Pure.instLevel ps (vs.map f) u).isNeverZero = true
  | .succ _, _ => rfl
  | .max a b, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true, Pure.instLevel] at h ⊢
    exact h.imp (isNeverZero_instLevel_map hf) (isNeverZero_instLevel_map hf)
  | .imax _ b, h => by
    simp only [Level.isNeverZero, Pure.instLevel] at h ⊢
    exact isNeverZero_instLevel_map hf (u := b) h
  | .param p, h => by
    rw [instLevel_param_map]
    simp only [Pure.instLevel] at h
    revert h
    cases (ps.zip vs).find? (·.1 == p) with
    | none => intro h; cases h
    | some x => exact hf _
  | .zero, h | .mvar _, h => by cases h

/-- Composition of universe instantiations on a level whose parameters are among `ps`. -/
theorem instLevel_comp {lps' : List Name} {us0 : List Level} {ps : List Name} {vs : List Level}
    (hl : vs.length = ps.length) :
    ∀ {u : Level} {l : Metalean.Level ps.length}, TrLevel ps u = some l →
      Pure.instLevel lps' us0 (Pure.instLevel ps vs u) =
        Pure.instLevel ps (vs.map (Pure.instLevel lps' us0)) u
  | .zero, _, _ => rfl
  | .succ u, _, h => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨_, h, -⟩ := h
    simp only [Pure.instLevel, instLevel_comp hl h]
  | .max a b, _, h => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, ha, _, hb, -⟩ := h
    simp only [Pure.instLevel, instLevel_comp hl ha, instLevel_comp hl hb]
  | .imax a b, _, h => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, ha, _, hb, -⟩ := h
    simp only [Pure.instLevel, instLevel_comp hl ha, instLevel_comp hl hb]
  | .param n, _, h => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, -⟩ := h
    rw [instLevel_param_map]
    simp only [Pure.instLevel, find_zip_of_finIdxOf hl hp]
  | .mvar _, _, h => by cases h

/-! ## Terms -/

/-- Every level of `e` translates at `ps` (its parameters are among `ps`). -/
def LevelsTr (ps : List Name) : Expr → Prop
  | .sort u => (TrLevel ps u).isSome
  | .const _ us => ∀ u ∈ us, (TrLevel ps u).isSome
  | .app f a => LevelsTr ps f ∧ LevelsTr ps a
  | .lam _ t b _ | .forallE _ t b _ => LevelsTr ps t ∧ LevelsTr ps b
  | .letE _ t v b _ => LevelsTr ps t ∧ LevelsTr ps v ∧ LevelsTr ps b
  | .mdata _ e | .proj _ _ e => LevelsTr ps e
  | _ => True

/-- Composition of universe instantiations on a term whose levels translate at `ps`. -/
theorem instLevels_comp {lps' : List Name} {us0 : List Level} {ps : List Name} {vs : List Level}
    (hl : vs.length = ps.length) : ∀ {x : Expr}, LevelsTr ps x →
      Pure.instLevels lps' us0 (Pure.instLevels ps vs x) =
        Pure.instLevels ps (vs.map (Pure.instLevel lps' us0)) x
  | .sort u, h => by
    obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.1 h
    simp only [Pure.instLevels, instLevel_comp hl hl']
  | .const c us, h => by
    simp only [Pure.instLevels, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.1 (h u hu)
    exact instLevel_comp hl hl'
  | .app f a, h => by
    simp only [Pure.instLevels, instLevels_comp hl (x := f) h.1, instLevels_comp hl (x := a) h.2]
  | .lam _ t b _, h | .forallE _ t b _, h => by
    simp only [Pure.instLevels, instLevels_comp hl (x := t) h.1, instLevels_comp hl (x := b) h.2]
  | .letE _ t v b _, h => by
    simp only [Pure.instLevels, instLevels_comp hl (x := t) h.1, instLevels_comp hl (x := v) h.2.1,
      instLevels_comp hl (x := b) h.2.2]
  | .mdata _ e, h | .proj _ _ e, h => by
    simp only [Pure.instLevels, instLevels_comp hl (x := e) h]
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl

theorem LevelsTr_foldl {ps : List Name} : ∀ {f : Expr} {as : List Expr},
    LevelsTr ps (as.foldl .app f) ↔ LevelsTr ps f ∧ ∀ a ∈ as, LevelsTr ps a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, LevelsTr_foldl]
    simp only [LevelsTr, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem TrLevels_mem {lps : List Name} {us : List Level} {k : Nat}
    {ls : Fin k → Metalean.Level lps.length} (h : TrLevels lps us k = some ls) :
    ∀ u ∈ us, (TrLevel lps u).isSome := by
  obtain ⟨hk, hget⟩ := TrLevels_get h
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  rw [hget ⟨i, by omega⟩]; rfl

theorem mapM_mem {lps : List Name} {us : List Level} {ls : List (Metalean.Level lps.length)}
    (h : us.mapM (TrLevel lps) = some ls) : ∀ u ∈ us, (TrLevel lps u).isSome := by
  obtain ⟨_, hget⟩ := mapM_option_get h
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  rw [hget i hi]; rfl

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}

/-- The levels of a saturating spine translate. -/
theorem SatTr.levelsTr {lps : List Name} {n : Nat} {b : MBinding ζ} {us : List Level}
    {args : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us args t) : ∀ u ∈ us, (TrLevel lps u).isSome := by
  cases h with
  | indSat _ _ _ hls | indEta hls | ctorSat _ _ _ _ _ hls | ctorEta hls => exact TrLevels_mem hls
  | recrSat _ _ _ _ hRL hls | recrEta _ hRL hls =>
    rcases hRL with ⟨-, u, rfl, hu⟩ | ⟨-, rfl, -⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [hu]; rfl
      · exact TrLevels_mem hls v hv
    · exact TrLevels_mem hls
  | quotType hu | quotMk hu | quotLift hu | quotInd hu | quotEta hu => exact mapM_mem hu

/-- The levels of a translated term translate. -/
theorem TrM.levelsTr {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ e t) : LevelsTr lps e := by
  induction h with
  | sort hl => show (TrLevel _ _).isSome; rw [hl]; rfl
  | const _ hls => exact TrLevels_mem hls
  | special _ _ hlen _ hsat ih =>
    rw [mkAppN_toArray]
    refine LevelsTr_foldl.2 ⟨SatTr.levelsTr hsat, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
  | app _ _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | letE _ _ _ ih₁ ih₂ ih₃ => exact ⟨ih₁, ih₂, ih₃⟩
  | mdata _ ih => exact ih
  | projStruct _ _ _ _ _ ih => exact ih
  | projProof _ _ _ _ _ _ _ _ _ ih => exact ih
  | _ => trivial

/-- What `ProgEnv` says about the levels of a declaration of the program: its type's levels
translate at its level parameters; a constructor is bound to a Metalean constructor of a block
with as many levels as the constructor's level parameters; a definition is bound to a Metalean
definition with as many levels. -/
theorem ProgEnv.levelsInfo {P : List ConstantInfo} (h : ProgEnv P ζ E B) {c : Name}
    {ci : ConstantInfo} (hc : findDecl P c = some ci) :
    LevelsTr ci.levelParams ci.type ∧
    (∀ cv, ci = .ctorInfo cv → ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι))
      (s : Fin ι.nsorts) (k : Fin (ι.nctors s)) (o : List Nat),
      B c = some (.ctor η s k o) ∧ ι.nlevels = cv.levelParams.length) ∧
    (∀ d, ci = .defnInfo d →
      ∃ η : Metalean.Head ζ (.const .def d.levelParams.length), B c = some (.const η)) := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ htr ih | @thm _ _ _ _ v _ _ _ _ _ _ htr _ ih
  | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ htr _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
      exact ⟨TrM.levelsTr htr, fun _ h => (by cases h), fun _ h => (by cases h)⟩
    · obtain ⟨h1, h2, h3⟩ := ih hc
      refine ⟨h1, fun cv hcv => ?_, fun d hd => ?_⟩
      · obtain ⟨ι, η, s, k, o, hB, hl⟩ := h2 cv hcv
        exact ⟨ι, η.there, s, k, o, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, hl⟩
      · obtain ⟨η, hB⟩ := h3 d hd
        exact ⟨η.there, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl⟩
  | @defn _ _ _ _ v _ _ _ _ _ _ _ htr _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      refine ⟨TrM.levelsTr htr, fun _ h => (by cases h), fun d hd => ?_⟩
      cases hd
      have hn' : c = v.name := hn.symm
      exact ⟨.here, by simp [Binds.set, hn']⟩
    · obtain ⟨h1, h2, h3⟩ := ih hc
      refine ⟨h1, fun cv hcv => ?_, fun d hd => ?_⟩
      · obtain ⟨ι, η, s, k, o, hB, hl⟩ := h2 cv hcv
        exact ⟨ι, η.there, s, k, o, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, hl⟩
      · obtain ⟨η, hB⟩ := h3 d hd
        exact ⟨η.there, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ _ _ _ _ hext hblk hct ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci' =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      obtain ⟨T, t₀, hT, -, -⟩ := hct _ hm
      refine ⟨TrM.levelsTr hT, fun cv hcv => ?_, fun d hdf => ?_⟩
      · subst hcv
        rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
        obtain ⟨hB, hlps, -⟩ := hblk.ctor s k
        exact ⟨ι, .here, s, k, _, (show (Cs s k).name = c from hn) ▸ hB,
          by rw [hlps, hblk.levels]⟩
      · subst hdf
        rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨h1, h2, h3⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      refine ⟨h1, fun cv hcv => ?_, fun d hdf => ?_⟩
      · obtain ⟨ι', η, s, k, o, hB, hl⟩ := h2 cv hcv
        exact ⟨ι', η.there, s, k, o, by rw [hext c hnot, Binds.wk, hB]; rfl, hl⟩
      · obtain ⟨η, hB⟩ := h3 d hdf
        exact ⟨η.there, by rw [hext c hnot, Binds.wk, hB]; rfl⟩
  | @quot _ _ _ _ _ qs _ _ _ _ _ _ hext hq ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci' =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp only [List.mem_map, List.mem_reverse] at hm
      obtain ⟨q, hq', rfl⟩ := hm
      obtain ⟨T, t₀, hT, -, -⟩ := (hq q hq').2.1
      exact ⟨TrM.levelsTr hT, fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨h1, h2, h3⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      refine ⟨h1, fun cv hcv => ?_, fun d hdf => ?_⟩
      · obtain ⟨ι', η, s, k, o, hB, hl⟩ := h2 cv hcv
        exact ⟨ι', η.there, s, k, o, by rw [hext c hnot, Binds.wk, hB]; rfl, hl⟩
      · obtain ⟨η, hB⟩ := h3 d hdf
        exact ⟨η.there, by rw [hext c hnot, Binds.wk, hB]; rfl⟩

end

/-! ## Universe instantiation commutes with the term operations of the η-expansion -/

section
variable (ps : List Name) (us : List Level)

theorem instLevels_lift : ∀ (e : Expr) (s d : Nat),
    Pure.instLevels ps us (e.liftLooseBVars' s d) = (Pure.instLevels ps us e).liftLooseBVars' s d
  | .bvar _, _, _ => rfl
  | .app f a, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift f, instLevels_lift a]
  | .lam _ t b _, s, d | .forallE _ t b _, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift t, instLevels_lift b]
  | .letE _ t v b _, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift t, instLevels_lift v,
      instLevels_lift b]
  | .mdata _ e, s, d | .proj _ _ e, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift e]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl

theorem instLevels_instantiate1' (a : Expr) : ∀ (e : Expr) (d : Nat),
    Pure.instLevels ps us (e.instantiate1' a d) =
      (Pure.instLevels ps us e).instantiate1' (Pure.instLevels ps us a) d
  | .bvar i, d => by
    show Pure.instLevels ps us (Expr.instantiate1' (.bvar i) a d) =
      Expr.instantiate1' (.bvar i) (Pure.instLevels ps us a) d
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · exact instLevels_lift ps us a 0 d
      · rfl
  | .app f b, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a f,
      instLevels_instantiate1' a b]
  | .lam _ t b _, d | .forallE _ t b _, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a t,
      instLevels_instantiate1' a b]
  | .letE _ t v b _, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a t,
      instLevels_instantiate1' a v, instLevels_instantiate1' a b]
  | .mdata _ e, d | .proj _ _ e, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a e]
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl

theorem piInst_instLevels : ∀ {as : List Expr} {ty ty' : Expr}, piInst as ty = some ty' →
    piInst (as.map (Pure.instLevels ps us)) (Pure.instLevels ps us ty) =
      some (Pure.instLevels ps us ty')
  | [], _, _, h => by cases h; rfl
  | a :: as, .forallE _ _ b _, _, h => by
    simp only [piInst] at h
    simp only [List.map_cons, Pure.instLevels, piInst]
    rw [← instLevels_instantiate1']
    exact piInst_instLevels h
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _, _, h | _ :: _, .mvar _, _, h
  | _ :: _, .sort _, _, h | _ :: _, .const .., _, h | _ :: _, .app .., _, h
  | _ :: _, .lam .., _, h | _ :: _, .letE .., _, h | _ :: _, .lit _, _, h
  | _ :: _, .mdata .., _, h | _ :: _, .proj .., _, h => by cases h

theorem lamsOf_instLevels : ∀ {k : Nat} {ty body e : Expr}, lamsOf k ty body = some e →
    lamsOf k (Pure.instLevels ps us ty) (Pure.instLevels ps us body) =
      some (Pure.instLevels ps us e)
  | 0, _, _, _, h => by cases h; rfl
  | k + 1, .forallE _ d b _, body, e, h => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    simp only [Pure.instLevels, lamsOf, lamsOf_instLevels h', Option.map_some]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _, _, _, h | _ + 1, .mvar _, _, _, h
  | _ + 1, .sort _, _, _, h | _ + 1, .const .., _, _, h | _ + 1, .app .., _, _, h
  | _ + 1, .lam .., _, _, h | _ + 1, .letE .., _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .mdata .., _, _, h | _ + 1, .proj .., _, _, h => by cases h

theorem instLevels_mkAppN (f : Expr) (as : List Expr) :
    Pure.instLevels ps us (mkAppN f as.toArray) =
      mkAppN (Pure.instLevels ps us f) (as.map (Pure.instLevels ps us)).toArray := by
  rw [mkAppN_toArray, instLevels_foldl, ← mkAppN_toArray]

end

/-! ## Level arguments of special spines -/

/-- The constants of `e` outside binder types that are constructors or definitions of `σ` have
as many level arguments as level parameters. -/
def LvlOK (σ : EvalEnv) : Expr → Prop
  | .const c us => ∀ ci, findDecl σ.decls c = some ci →
      ((∃ cv, ci = .ctorInfo cv) ∨ (∃ d, ci = .defnInfo d) ∨ (∃ q, ci = .quotInfo q) ∨
        ∃ r, ci = .recInfo r) →
      us.length = ci.levelParams.length
  | .app f a => LvlOK σ f ∧ LvlOK σ a
  | .lam _ _ b _ => LvlOK σ b
  | .letE _ _ v b _ => LvlOK σ v ∧ LvlOK σ b
  | .mdata _ e | .proj _ _ e => LvlOK σ e
  | _ => True

theorem LvlOK_foldl {σ : EvalEnv} : ∀ {f : Expr} {as : List Expr},
    LvlOK σ (as.foldl .app f) ↔ LvlOK σ f ∧ ∀ a ∈ as, LvlOK σ a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, LvlOK_foldl]
    simp only [LvlOK, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem LvlOK_mkAppN {σ : EvalEnv} {f : Expr} {as : List Expr} :
    LvlOK σ (mkAppN f as.toArray) ↔ LvlOK σ f ∧ ∀ a ∈ as, LvlOK σ a := by
  rw [mkAppN_toArray, LvlOK_foldl]

theorem LvlOK_lift {σ : EvalEnv} : ∀ {e : Expr} {s d : Nat}, LvlOK σ e →
    LvlOK σ (e.liftLooseBVars' s d)
  | .bvar _, _, _, _ => trivial
  | .app f a, _, _, h => ⟨LvlOK_lift (e := f) h.1, LvlOK_lift (e := a) h.2⟩
  | .lam _ _ b _, _, _, h => LvlOK_lift (e := b) h
  | .letE _ _ v b _, _, _, h => ⟨LvlOK_lift (e := v) h.1, LvlOK_lift (e := b) h.2⟩
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => LvlOK_lift (e := e) h
  | .forallE .., _, _, _ | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _
  | .lit _, _, _, _ => trivial
  | .const .., _, _, h => h

theorem LvlOK_lamsOf {σ : EvalEnv} : ∀ {k : Nat} {ty body e : Expr}, lamsOf k ty body = some e →
    LvlOK σ body → LvlOK σ e
  | 0, _, _, _, h, hb => by cases h; exact hb
  | k + 1, .forallE _ d b _, body, e, h, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    exact (LvlOK_lamsOf (k := k) h' hb : LvlOK σ e')
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _, _, _, h, _ | _ + 1, .mvar _, _, _, h, _
  | _ + 1, .sort _, _, _, h, _ | _ + 1, .const .., _, _, h, _ | _ + 1, .app .., _, _, h, _
  | _ + 1, .lam .., _, _, h, _ | _ + 1, .letE .., _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .mdata .., _, _, h, _ | _ + 1, .proj .., _, _, h, _ => by cases h

/-- The η-expansion of a spine with `LvlOK` is `LvlOK`. -/
theorem LvlOK_etaSpine {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') (hok : LvlOK σ (mkAppN (.const c us) as.toArray)) :
    LvlOK σ e' := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · split at h
    · obtain ⟨ty, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hc, has⟩ := LvlOK_mkAppN.1 hok
      refine LvlOK_lamsOf h (LvlOK_mkAppN.2 ⟨hc, fun x hx => ?_⟩)
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact LvlOK_lift (has y hy)
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        trivial
    · cases h
  · cases h

/-- The η-expansion commutes with universe instantiation when the spine has as many level
arguments as the declaration has level parameters, and the declaration's type has its levels
among them. -/
theorem etaSpine?_instLevels {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr}
    {e' : Expr} {lps' : List Name} {us0 : List Level} (h : σ.etaSpine? c us as = some e')
    (hlen : ∀ ci, findDecl σ.decls c = some ci → us.length = ci.levelParams.length)
    (hty : ∀ ci, findDecl σ.decls c = some ci → LevelsTr ci.levelParams ci.type) :
    σ.etaSpine? c (us.map (Pure.instLevel lps' us0)) (as.map (Pure.instLevels lps' us0)) =
      some (Pure.instLevels lps' us0 e') := by
  unfold EvalEnv.etaSpine? at h ⊢
  split at h
  next ci ar hci har =>
    split at h
    next hlt =>
      simp only [List.length_map, hlt, ↓reduceIte]
      obtain ⟨ty, hpi, h⟩ := Option.bind_eq_some_iff.1 h
      rw [← instLevels_comp (hlen ci hci) (hty ci hci), piInst_instLevels _ _ hpi]
      refine Option.bind_eq_some_iff.2 ⟨_, rfl, ?_⟩
      have := lamsOf_instLevels lps' us0 h
      rw [instLevels_mkAppN, List.map_append, List.map_map, List.map_map] at this
      convert this using 3
      simp only [Pure.instLevels]
      congr 2
      · rw [List.map_map]
        refine List.map_congr_left fun a _ => ?_
        exact (instLevels_lift lps' us0 a 0 _).symm
    next => cases h
  next => cases h

/-- `¬ CasesReduced` survives instantiating the levels of the `casesOn`. -/
theorem not_casesReduced_map {iv : InductiveVal} {us : List Level} {lps' : List Name}
    {us0 : List Level} (h : ¬ CasesReduced iv us) :
    ¬ CasesReduced iv (us.map (Pure.instLevel lps' us0)) := by
  rintro ⟨h1, l, hl, hz⟩
  refine h ⟨h1, ?_⟩
  unfold casesSortLevel at hl ⊢
  revert hl
  cases arityShape iv.type with
  | none => intro hl; cases hl
  | some p =>
    intro hl
    obtain ⟨_, u⟩ := p
    simp only [Option.map_some, Option.some.injEq, List.length_map, ← List.map_drop] at hl
    refine ⟨_, rfl, ?_⟩
    cases h' : (Pure.instLevel iv.levelParams (us.drop (us.length - iv.levelParams.length)) u).isNeverZero
    · rfl
    · rw [← hl, isNeverZero_instLevel_map (fun _ => isNeverZero_instLevel) h'] at hz
      cases hz

/-- A recursor's fixpoint survives instantiating the levels of the recursor: the case-free form is
used when the major's sort may be zero, which instantiation does not change into never zero. -/
theorem RecFixOf.instL {σ : EvalEnv} {rv : RecursorVal} {us : List Level} {minors : List RecMinor}
    {F : LBTerm} {lps' : List Name} {us0 : List Level} (h : RecFixOf E B σ rv us minors F) :
    RecFixOf E B σ rv (us.map (Pure.instLevel lps' us0)) minors F := by
  obtain ⟨ivs, cvs, motives, members, T, ivT, j, direct, hb, hs, hl, hm, hT, hiv, hj, h1, h2, h3,
    hF, hc, hx⟩ := h
  refine ⟨ivs, cvs, motives, members, T, ivT, j, direct, hb, hs, hl, hm, hT, hiv, hj,
    fun hd => ?_, h2, h3, hF, hc, hx⟩
  obtain ⟨l, hl', hnz⟩ := h1 hd
  unfold casesSortLevel at hl' ⊢
  revert hl'
  cases arityShape ivT.type with
  | none => intro hl'; cases hl'
  | some p =>
    intro hl'
    obtain ⟨_, u⟩ := p
    simp only [Option.map_some, Option.some.injEq, List.length_map, ← List.map_drop] at hl' ⊢
    refine ⟨_, rfl, ?_⟩
    rw [← hl'] at hnz
    exact isNeverZero_instLevel_map (fun _ => isNeverZero_instLevel) hnz

/-- Constructor, recognized `casesOn`, quotient and recursor heads are constructors, definitions,
quotient constants or recursors. -/
theorem etaSpine?_kind {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') {ci : ConstantInfo} (hci : findDecl σ.decls c = some ci) :
    (∃ cv, ci = .ctorInfo cv) ∨ (∃ d, ci = .defnInfo d) ∨ (∃ q, ci = .quotInfo q) ∨
      ∃ r, ci = .recInfo r := by
  unfold EvalEnv.etaSpine? at h
  split at h
  next ci' ar hci' har =>
    unfold specialArity at har
    split at har
    next cv hcv => rw [hci] at hcv; cases hcv; exact .inl ⟨_, rfl⟩
    next qv hqv => rw [hci] at hqv; cases hqv; exact .inr (.inr (.inl ⟨_, rfl⟩))
    next rv hrv => rw [hci] at hrv; cases hrv; exact .inr (.inr (.inr ⟨_, rfl⟩))
    next =>
      obtain ⟨iv, hiv, -⟩ := Option.map_eq_some_iff.1 har
      obtain ⟨d, -, -, -, -, -, -, -, hd, -⟩ := casesOn_shape hiv
      rw [hci] at hd; cases hd; exact .inr (.inl ⟨_, rfl⟩)
  next => cases h

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}
  {P : List ConstantInfo}

/-- A recursor spine's image reads as many levels as the recursor has universe parameters: the
image of the recursor at its own parameters (`ConstTyped`) reads its levels by the same
`RecrLevels`. -/
theorem SatTr.recr_levels_length (henv : ProgEnv P ζ E B) (hE : Metalean.EnvWF E) {c : Name}
    {rv : RecursorVal} (hc : findDecl P c = some (.recInfo rv)) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {os : List (List (List Nat))}
    (hB : B c = some (.recr η s os)) {lps : List Name} {n : Nat} {us : List Level}
    {args : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (hsat : SatTr E lps (.recr η s os) us args t) : us.length = rv.levelParams.length := by
  obtain ⟨l, us', ls, hRL, hls⟩ : ∃ l us' ls, RecrLevels (E.get η).block lps us l us' ∧
      TrLevels lps us' ι.nlevels = some ls := by
    cases hsat with
    | recrSat _ _ _ _ hRL hls => exact ⟨_, _, _, hRL, hls⟩
    | recrEta _ hRL hls => exact ⟨_, _, _, hRL, hls⟩
  have hname : rv.name = c := (findDecl_eq_some hc).2
  obtain ⟨-, -, Tc, tc, -, htc, -⟩ := henv.lookup hE hc
  have htc' : TrM E B rv.levelParams .nil [] (mkAppN (.const c (rv.levelParams.map .param))
      ([] : List Expr).toArray) tc := by rw [← hname]; exact htc
  obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv hB rfl htc'
  obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
  obtain ⟨l₁, us₁, ls₁, -, -, hRL₁, hls₁, -, -, -⟩ :=
    satTr_recrEta_inv hsat₁ (by simp [Metalean.IndSig.recrEnd])
  obtain ⟨ls', hus⟩ := recr_spine_levels hRL hls hRL₁ hls₁
  exact (TrLevels_get hus).1

/-- A translated term is `LvlOK`: `TrM` translates a constructor's or a definition's level list
at the Metalean declaration's number of levels, which `ProgEnv` makes the number of the Lean
declaration's level parameters, and a recursor's as the recursor's own image
(`SatTr.recr_levels_length`). -/
theorem TrM.lvlOK (henv : ProgEnv P ζ E B) (hE : Metalean.EnvWF E) (hsub : SubEnv σ.decls P)
    {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) : LvlOK σ e := by
  induction h with
  | const hB hls =>
    intro ci hci hk
    obtain ⟨-, hctor, hdefn⟩ := ProgEnv.levelsInfo henv (Extend.findDecl_sub hsub hci)
    rcases hk with ⟨cv, rfl⟩ | ⟨d, rfl⟩ | ⟨q, rfl⟩ | ⟨r, rfl⟩
    · obtain ⟨ι, η, s, k, o, hB', -⟩ := hctor cv rfl
      rw [hB] at hB'; cases hB'
    · obtain ⟨η', hB'⟩ := hdefn d rfl
      rw [hB] at hB'; cases hB'
      exact (TrLevels_get hls).1
    · obtain ⟨η', hB'⟩ := henv.lookup_quot (Extend.findDecl_sub hsub hci)
      rw [hB] at hB'; cases hB'
    · obtain ⟨ι, η', s, os, hB', -⟩ := henv.lookup_recr (Extend.findDecl_sub hsub hci)
      rw [hB] at hB'; cases hB'
  | special hB hs hlen _ hsat ih =>
    rw [mkAppN_toArray]
    refine LvlOK_foldl.2 ⟨?_, fun a ha => ?_⟩
    · intro ci hci hk
      obtain ⟨-, hctor, hdefn⟩ := ProgEnv.levelsInfo henv (Extend.findDecl_sub hsub hci)
      rcases hk with ⟨cv, rfl⟩ | ⟨d, rfl⟩ | ⟨q, rfl⟩ | ⟨r, rfl⟩
      · obtain ⟨ι, η, s, k, o, hB', hl⟩ := hctor cv rfl
        rw [hB] at hB'; cases hB'
        cases hsat with
        | ctorSat _ _ _ _ _ hls => exact (TrLevels_get hls).1.trans hl
        | ctorEta hls => exact (TrLevels_get hls).1.trans hl
      · obtain ⟨η', hB'⟩ := hdefn d rfl
        rw [hB] at hB'; cases hB'; cases hs
      · obtain ⟨η', hB'⟩ := henv.lookup_quot (Extend.findDecl_sub hsub hci)
        rw [hB] at hB'; cases hB'
        exact hsat.quot_levels.trans (henv.quot_levels (Extend.findDecl_sub hsub hci)).symm
      · obtain ⟨ι, η', s, os, hB', -⟩ := henv.lookup_recr (Extend.findDecl_sub hsub hci)
        rw [hB] at hB'; cases hB'
        exact SatTr.recr_levels_length henv hE (Extend.findDecl_sub hsub hci) hB hsat
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact ih i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
  | app _ _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ _ ih₂ => exact ih₂
  | letE _ _ _ _ ih₂ ih₃ => exact ⟨ih₂, ih₃⟩
  | mdata _ ih => exact ih
  | projStruct _ _ _ _ _ ih => exact ih
  | projProof _ _ _ _ _ _ _ _ _ ih => exact ih
  | _ => trivial

/-- Universe instantiation of an erasure under binders and locals, for terms that are `LvlOK`. -/
theorem Erases.instL_gen (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {lps lps' : List Name} {us : List Level} {ls : Fin lps'.length → Metalean.Level lps.length}
    (hus : TrLevels lps us lps'.length = some ls) {n : Nat} {Γ : Metalean.Ctx ζ lps'.length 0 n}
    {Δ : MLCtx ζ lps'.length n} {e : Expr} {tb : LBTerm} (h : Erases E B lps' σ Γ Δ e tb)
    (hok : LvlOK σ e) :
    Erases E B lps σ (Γ{ls}) (Δ.instL ls) (Pure.instLevels lps' us e) tb := by
  have hty : ∀ c ci, findDecl σ.decls c = some ci → LevelsTr ci.levelParams ci.type :=
    fun _ _ hci => (ProgEnv.levelsInfo henv (Extend.findDecl_sub hsub hci)).1
  have mem : ∀ {l : List Expr} {i : Nat} {x : Expr}, l[i]? = some x → x ∈ l :=
    fun h => List.mem_of_getElem? h
  have gmap : ∀ {l : List Expr} {i : Nat} {x : Expr},
      (l.map (Pure.instLevels lps' us))[i]? = some x →
        ∃ x₀, l[i]? = some x₀ ∧ Pure.instLevels lps' us x₀ = x := fun h => by
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  refine Erases.rec
    (motive_1 := fun Γ Δ e tb _ => LvlOK σ e →
      Erases E B lps σ (Γ{ls}) (Δ.instL ls) (Pure.instLevels lps' us e) tb)
    (motive_2 := fun Γ Δ k e br _ => LvlOK σ e →
      ErasesAlt E B lps σ (Γ{ls}) (Δ.instL ls) k (Pure.instLevels lps' us e) br)
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro h hok
  case bvar => intros; exact .bvar
  case fvar => intros; exact .fvar
  case lam =>
    intro _ _ _ _ _ _ _ _ _ hA hAt _ ih hok
    have := ih hok
    rw [MLCtx.instL_pushLam] at this
    exact .lam (hA.instL hus) (let ⟨_, h⟩ := hAt; ⟨_, by simpa using h.instLevel ls⟩) this
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv ⟨_, hvt⟩ _ _ ihv ihb hok
    exact .letE (hv.instL hus) ⟨_, by simpa using hvt.instLevel ls⟩ (ihv hok.1) (ihb hok.2)
  case app =>
    intro f _ _ _ _ _ _ hns _ _ ihf iha hok
    refine .app (fun ⟨c, vs, hc, hs⟩ => hns ?_) (ihf hok.1) (iha hok.2)
    rw [instLevels_getAppFn] at hc
    obtain ⟨vs', hvs'⟩ := instLevels_eq_const hc
    exact ⟨c, vs', hvs', hs⟩
  case const => intro _ _ _ _ _ hat hsa hnr _; exact .const hat hsa hnr
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN]
    refine .ctor hcv hnp hid (by simpa using hle) (by simpa using hlen) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ih i a₀ a' ha₀ ha' (has a₀ (mem ha₀))
  case cases =>
    intro c iv _ _ _ _ _ maj _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .cases hco (not_casesReduced_map hnr) hss hid (by simpa using hpre)
      (by simpa using halts) (ihm (has maj (by simp))) (by simpa using hbrs) hcf
      (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex) (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap h2
      exact iha i cn a₀ br k h1 ha₀ h3 h4 (has a₀ (by simp [mem ha₀]))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihe i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ maj pre extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .casesReduced hco hfe hcs hcv hidx (by simpa using hpre) (iha (has alt (by simp)))
      (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case eta =>
    intro c _ _ _ _ _ _ _ heta _ ih hok
    rw [instLevels_mkAppN]
    exact .eta (etaSpine?_instLevels heta
      (fun ci hci => (LvlOK_mkAppN.1 hok).1 ci hci (etaSpine?_kind heta hci)) (hty c))
      (ih (LvlOK_etaSpine heta hok))
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih hok
    exact .proj hss hid hS hsort (ih hok)
  case litZero => intro _ _ _ _ hid _; exact .litZero hid
  case litSucc => intro _ _ _ _ _ _ hid _ ih _; exact .litSucc hid (ih trivial)
  case quotMk =>
    intros; rename_i hcq hk _ hlex _ iha ihe hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotMk hcq hk (iha (has _ (by simp))) (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case quotLift =>
    intros; rename_i hcq hk _ _ hlex _ ihf ihq ihe hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotLift hcq hk (ihf (has _ (by simp))) (ihq (has _ (by simp))) (by simpa using hlex)
      fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case recLet =>
    intro c rv uc minors F _ _ _ maj maj' ps ms mins is extra mins' is' extra' hcr hF hps hms hmins
      his hlm _ hli _ _ hle _ ihmin ihis ihmaj ihext hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN, show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (Pure.instLevels lps' us) =
      ps.map (Pure.instLevels lps' us) ++ ms.map (Pure.instLevels lps' us) ++
        mins.map (Pure.instLevels lps' us) ++ is.map (Pure.instLevels lps' us) ++
          [Pure.instLevels lps' us maj] ++ extra.map (Pure.instLevels lps' us) by simp]
    refine .recLet hcr (RecFixOf.instL hF) (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm) (fun i a a' ha ha' => ?_) (by simpa using hli)
      (fun i a a' ha ha' => ?_) (ihmaj (has maj (by simp))) (by simpa using hle)
      (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihmin i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihis i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihext i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case recFix =>
    intro c rv uc minors F _ _ _ maj maj' ps ms mins is extra ws is' extra' hcr hF hps hms hmins
      his hlw _ hws hli _ _ hle _ ihmin ihis ihmaj ihext hok
    have has := (LvlOK_mkAppN.1 hok).2
    rw [instLevels_mkAppN, show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (Pure.instLevels lps' us) =
      ps.map (Pure.instLevels lps' us) ++ ms.map (Pure.instLevels lps' us) ++
        mins.map (Pure.instLevels lps' us) ++ is.map (Pure.instLevels lps' us) ++
          [Pure.instLevels lps' us maj] ++ extra.map (Pure.instLevels lps' us) by simp]
    refine .recFix hcr (RecFixOf.instL hF) (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw) (fun i a a' ha ha' => ?_) hws (by simpa using hli)
      (fun i a a' ha ha' => ?_) (ihmaj (has maj (by simp))) (by simpa using hle)
      (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihmin i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihis i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihext i a₀ a' ha₀ ha' (has a₀ (by simp [mem ha₀]))
  case mdata => intro _ _ _ _ _ _ _ ih hok; exact .mdata (ih hok)
  case box =>
    intro _ _ _ _ hb _
    obtain ⟨t, ht, hie⟩ := hb
    exact .box ⟨_, ht.instL hus, IsErasable.instL_ctx ls hie⟩
  case done => intro _ _ _ _ _ _ ih hok; exact .done (ih hok)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih hok
    have := ih hok
    rw [MLCtx.instL_pushLam] at this
    exact .lam (hA.instL hus) (let ⟨_, h⟩ := hAt; ⟨_, by simpa using h.instLevel ls⟩) this
  case intro =>
    intro _ _ _ e _ _ _ _ _ _ _ he hty' _ ih hok
    have := ih ⟨LvlOK_lift hok, trivial⟩
    rw [MLCtx.instL_pushLam,
      show Pure.instLevels lps' us (.app (e.liftLooseBVars' 0 1) (.bvar 0)) =
        .app ((Pure.instLevels lps' us e).liftLooseBVars' 0 1) (.bvar 0) by
          rw [← instLevels_lift]; rfl] at this
    exact .intro (he.instL hus) (by simpa using hty'.instLevel ls) this

end

end RelLevels

/-- Universe instantiation of closed terms: an erasure at universe parameters `lps'` of a term that
translates is an erasure of its instantiation at `lps`. Reference: `erases_subst_instance`
(`MR E/ErasureProperties.v:383`), whose premises `wf_ext_wk Σ` and `Σ ;;; Γ |- t : T` are here
`ProgEnv` and the translation `TrM`. -/
theorem Erases.instLevels {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}
    {P : List ConstantInfo} {lps lps' : List Name} {us : List Level}
    {ls : Fin lps'.length → Metalean.Level lps.length} {e : Expr}
    {t : Metalean.Expr ζ lps'.length 0} {tb : LBTerm} (henv : ProgEnv P ζ E B)
    (hE : Metalean.EnvWF E) (hsub : SubEnv σ.decls P) (hus : TrLevels lps us lps'.length = some ls)
    (he : TrM E B lps' .nil [] e t) (h : Erases E B lps' σ .nil [] e tb) :
    Erases E B lps σ .nil [] (Pure.instLevels lps' us e) tb := by
  simpa [MLCtx.instL] using
    RelLevels.Erases.instL_gen henv hsub hus h (RelLevels.TrM.lvlOK henv hE hsub he)

end EraseProof
