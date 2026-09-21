import LeanToLambdaBox.Lower
import LeanToLambdaBox.FixUnfold
import LeanToLambdaBox.Erases

/-!
# `LowerFix` — the block closure of `Lower`

The eraser turns a recursive block into one `.fix` node: each sibling constant `kns[j]`
becomes a fresh fvar `ids[j]`, and `mkDef`'s `toBvar` chain closes the result. At run time
`WcbvEval.fix_guarded` substitutes the block back for those binders. This module carries
what `Lower` alone cannot say about that round trip:

* `LowerFix` — the declaration-level form of `LowerBlock`, lowered bodies and fixvars
  existential.
* `ErasesLBFix` — the composite `Erases ⨟ Lower ⨟ ConstToFVar`, the motive a sub-run
  inside the block branch concludes.
* `Lower.constToFix` — the transport: substituting the block's own `.fix` nodes for its
  fixvars in a `ConstToFVar` image lands back inside `Lower`.
* `Lower.fixUnfold` — a member's unfolded definition is a λ still related to its body,
  off `LowerBlock.hfl` and with no premise of its own.
* `LowerFixFixture` — a two-member mutual block exhibiting all of it, including one
  application step that fires `WcbvEval.fix_guarded` through the block.

`ConstToFVar` and `CloseConstAt` are `Lower.lean`'s (`LowerBlock.hcl` needs them), and so
are the λ-headedness transports `LowerBlock.targetLambda_of_fixLambda` and
`LowerBlock.lambda_of_fixLambda`, which the inversion kit there consumes.

One statement of `doc/rework/01-DESIGN.md` §4.5 is **false as written** and is repaired
here with the missing premise named in its docstring;
`LowerFixFixture.constToFix_needs_freshness` is the machine-checked refutation of the
unrepaired form.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId Expr)
open Lean4Lean (VEnv VLCtx)

/-! ## The two block-level definitions -/

/-- Declaration-level block lowering: `defs` is a `Lower` image of the specification
bodies `bs` under the names `kns`. Tolerates an unused fix binder — nothing here mirrors
the eraser's source-side recursiveness test. -/
def LowerFix (Γ : GlobalDeclarations) (kns : List Kername) (bs : List LBTerm)
    (defs : List (@FixDef LBTerm)) : Prop :=
  ∃ bs' ids, LowerBlock Γ kns bs bs' ids defs

/-- The block-body motive: erasure, lowering, and the block's const-to-fixvar rewriting
composed. Inside a block the eraser emits `.fvar ids[j]` at a source `.const kns[j]`, a
pair neither `Erases` nor `Lower` relates on its own. -/
def ErasesLBFix (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations)
    (kns : List Kername) (ids : List FVarId) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀ t₁, Erases env Us Δ e t₀ ∧ Lower Γ t₀ t₁ ∧ ConstToFVar kns ids t₁ t

/-! ## Small list plumbing

Two moves the indexed-list premises need and `Lower.lean` does not already carry: a
`getElem!`-flavoured extensionality, and the finite choice that turns an index-wise
existential into one list. Both are `Prop`-level and choice-free. -/

/-- Two lists of equal length agreeing at every `getElem!` are equal. -/
theorem list_eq_of_getElem! {α : Type} [Inhabited α] {l l' : List α}
    (hlen : l.length = l'.length) (h : ∀ i, i < l.length → l[i]! = l'[i]!) : l = l' :=
  List.ext_getElem hlen fun i h₁ h₂ => by
    rw [← getElem!_pos l i h₁, ← getElem!_pos l' i h₂]; exact h i h₁

/-- Finite choice over an index range: an index-wise existential yields one list. The
existentials are eliminated one at a time, so no choice principle is used. -/
theorem exists_list_of_index {β : Type} [Inhabited β] :
    ∀ (n : Nat) (R : Nat → β → Prop), (∀ i, i < n → ∃ b, R i b) →
      ∃ l : List β, l.length = n ∧ ∀ i, i < n → R i l[i]! := by
  intro n
  induction n with
  | zero => exact fun _ _ => ⟨[], rfl, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
      intro R h
      obtain ⟨b₀, hb₀⟩ := h 0 (by omega)
      obtain ⟨l, hl, hpt⟩ := ih (fun i => R (i + 1)) (fun i hi => h (i + 1) (by omega))
      refine ⟨b₀ :: l, by simp [hl], ?_⟩
      intro i hi
      match i with
      | 0 => simpa using hb₀
      | k + 1 =>
          have hk : k < n := by omega
          rw [getElem!_pos (b₀ :: l) (k + 1) (by simp [hl]; omega), List.getElem_cons_succ,
            ← getElem!_pos l k (by omega)]
          exact hpt k hk

/-! ## `hasFVar` through the spine, telescope and shift operators -/

/-- A free variable of an application spine is one of the head or of an argument. -/
theorem hasFVar_mkApps (x : FVarId) : ∀ (l : List LBTerm) (f : LBTerm),
    hasFVar x (LBTerm.mkApps f l) ↔ hasFVar x f ∨ ∃ a ∈ l, hasFVar x a := by
  intro l
  induction l with
  | nil => intro f; simp [LBTerm.mkApps]
  | cons a as ih =>
      intro f
      rw [show LBTerm.mkApps f (a :: as) = LBTerm.mkApps (.app f a) as from rfl, ih]
      simp only [hasFVar_app, List.mem_cons]
      constructor
      · rintro ((hf | ha) | ⟨y, hy, hxy⟩)
        · exact .inl hf
        · exact .inr ⟨a, .inl rfl, ha⟩
        · exact .inr ⟨y, .inr hy, hxy⟩
      · rintro (hf | ⟨y, rfl | hy, hxy⟩)
        · exact .inl (.inl hf)
        · exact .inl (.inr hxy)
        · exact .inr ⟨y, hy, hxy⟩

/-- A lambda telescope adds no free variable. -/
theorem hasFVar_mkLambdas (x : FVarId) : ∀ (ns : List BinderName) (b : LBTerm),
    hasFVar x (mkLambdas ns b) ↔ hasFVar x b := by
  intro ns
  induction ns with
  | nil => intro b; exact Iff.rfl
  | cons n ns ih => intro b; rw [show mkLambdas (n :: ns) b = .lambda n (mkLambdas ns b) from rfl,
      hasFVar_lambda, ih]

/-- `shift` renumbers de Bruijn indices only: the free variables are untouched. -/
theorem hasFVar_shift (x : FVarId) : ∀ (t : LBTerm) (d c : Nat),
    hasFVar x (LBTerm.shift d c t) ↔ hasFVar x t := by
  intro t
  induction t using LBTerm.recData with
  | hbox | hfvar | hconst | hprim => intro d c; exact Iff.rfl
  | hbvar i => intro d c; rw [LBTerm.shift_bvar]; split <;> exact Iff.rfl
  | hlam n b ih => intro d c; simpa [LBTerm.shift] using ih d (c + 1)
  | hletIn n v b ihv ihb =>
      intro d c; simp only [LBTerm.shift, hasFVar_letIn, ihv d c, ihb d (c + 1)]
  | happ f a ihf iha => intro d c; simp only [LBTerm.shift, hasFVar_app, ihf d c, iha d c]
  | hproj p e ih => intro d c; simpa [LBTerm.shift] using ih d c
  | hconstruct iid k args ih =>
      intro d c
      simp only [LBTerm.shift, hasFVar_construct, LBTerm.shiftArgs_eq_map, hasFVarArgs_iff,
        List.mem_map]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩; exact ⟨a, ha, (ih a ha d c).mp hx⟩
      · rintro ⟨a, ha, hx⟩; exact ⟨_, ⟨a, ha, rfl⟩, (ih a ha d c).mpr hx⟩
  | hcase info discr alts ihd iha =>
      intro d c
      simp only [LBTerm.shift, hasFVar_case, LBTerm.shiftAlts_eq_map, hasFVarAlts_iff,
        List.mem_map, ihd d c]
      constructor
      · rintro (h | ⟨_, ⟨a, ha, rfl⟩, hx⟩)
        · exact .inl h
        · exact .inr ⟨a, ha, (iha a ha d (c + a.1.length)).mp hx⟩
      · rintro (h | ⟨a, ha, hx⟩)
        · exact .inl h
        · exact .inr ⟨_, ⟨a, ha, rfl⟩, (iha a ha d (c + a.1.length)).mpr hx⟩
  | hfix defs i ih =>
      intro d c
      simp only [LBTerm.shift, hasFVar_fix, LBTerm.shiftDefs_eq_map, hasFVarDefs_iff,
        List.mem_map]
      constructor
      · rintro ⟨_, ⟨fd, hfd, rfl⟩, hx⟩; exact ⟨fd, hfd, (ih fd hfd d (c + defs.length)).mp hx⟩
      · rintro ⟨fd, hfd, hx⟩
        exact ⟨_, ⟨fd, hfd, rfl⟩, (ih fd hfd d (c + defs.length)).mpr hx⟩

/-! ## What `closeFix` removes

`not_hasFVar_closeFix` (`FixUnfold.lean`) closes a term whose free variables *all* lie in `ids`.
The block needs the complementary half: whatever else survives, the `ids` do not. -/

/-- The closing fold creates no free variable. -/
theorem hasFVar_of_closeFixFold : ∀ (pairs : List (FVarId × Nat)) (t : LBTerm) (x : FVarId),
    hasFVar x (closeFixFold pairs t) → hasFVar x t := by
  intro pairs
  induction pairs with
  | nil => intro t x h; exact h
  | cons p rest ih =>
      obtain ⟨y, lvl⟩ := p
      intro t x h
      rw [closeFixFold_cons] at h
      exact (hasFVar_toBvar x y t lvl (ih _ x h)).2

/-- Every scheduled variable is gone: the fold deletes its own variable and creates none. -/
theorem not_hasFVar_closeFixFold_of_mem :
    ∀ (pairs : List (FVarId × Nat)) (t : LBTerm) (x : FVarId), x ∈ pairs.map Prod.fst →
      ¬ hasFVar x (closeFixFold pairs t) := by
  intro pairs
  induction pairs with
  | nil => intro t x hx; simp at hx
  | cons p rest ih =>
      obtain ⟨y, lvl⟩ := p
      intro t x hx h
      rw [closeFixFold_cons] at h
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact (hasFVar_toBvar x y t lvl (hasFVar_of_closeFixFold rest _ x h)).1 hxy
      · exact ih (toBvar y lvl t) x hx h

/-- The block-level form: `closeFix ids` removes exactly the `ids`. -/
theorem not_hasFVar_closeFix_of_mem {ids : List FVarId} {x : FVarId} (hx : x ∈ ids)
    (base : Nat) (t : LBTerm) : ¬ hasFVar x (closeFix ids base t) := by
  refine not_hasFVar_closeFixFold_of_mem (ids.reverse.zipIdx base) t x ?_
  rw [List.zipIdx_map_fst, List.mem_reverse]; exact hx

/-! ## Two facts a `LowerBlock` carries about its own `.fix` node -/

/-- The stored block mentions none of its fixvars: every definition body is a
`closeFix ids` image, and closing removes exactly the `ids`. This is the freshness clause
`closeFix_substList_fixSubst` and `substFix_fvar_getElem` (`FixUnfold.lean`) ask for. -/
theorem LowerBlock.not_hasFVar_fix {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hblk : LowerBlock Γ kns bs bs' ids defs) :
    ∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j) := by
  intro x hx j hf
  rw [hasFVar_fix, hasFVarDefs_iff] at hf
  obtain ⟨fd, hfd, hxb⟩ := hf
  obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hfd
  obtain ⟨u, _, heq⟩ := hblk.hcl i (hblk.hd ▸ hi)
  rw [heq] at hxb
  exact not_hasFVar_closeFix_of_mem hx 0 u hxb

/-- The stored block is closed, given closed specification bodies. `LowerBlock` carries no
closedness field of its own, so this is where `ClosedBodies` enters. -/
theorem LowerBlock.lbClosed_fix {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hΓ : ClosedBodies Γ) (hblk : LowerBlock Γ kns bs bs' ids defs) :
    ∀ j, LBClosed (LBTerm.fix defs j) 0 := fun _ =>
  lbClosed_fix_of_block hblk.hd hblk.hilen hblk.hcl
    (fun i hi => (Lower.closed hΓ (hblk.hlow i hi)) 0 (hΓ _ _ (hblk.hdecl i hi))) 0

/-- **The block's dynamic unfolding inverts its static closure**, with
`closeFix_substList_fixSubst`'s three hypotheses read off `LowerBlock`: `hilen`/`hd` give
the length, `LowerBlock.lbClosed_fix` the closedness, `LowerBlock.not_hasFVar_fix` the
freshness. Only the closedness needs anything beyond the structure. -/
theorem LowerBlock.substList_fixSubst {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hΓ : ClosedBodies Γ) (hblk : LowerBlock Γ kns bs bs' ids defs)
    {t : LBTerm} (hcl : LBClosed t 0) :
    LBTerm.substList (LBTerm.fixSubst defs) (closeFix ids 0 t) = substFix ids defs t :=
  closeFix_substList_fixSubst (hblk.hilen.trans hblk.hd.symm) (hblk.lbClosed_fix hΓ)
    hblk.not_hasFVar_fix hcl


/-! ## `ConstToFVar` inversion

`Lower.constToFix` is an induction over `Lower`, so at every arm the `ConstToFVar` premise
has to be read backwards through the shape that arm's target has: a spine, a telescope, a
telescope argument under a `shift`. -/

/-- Inversion through an application spine. -/
theorem ConstToFVar.mkApps_inv {kns : List Kername} {ids : List FVarId} :
    ∀ (l : List LBTerm) (f w : LBTerm), ConstToFVar kns ids (LBTerm.mkApps f l) w →
      ∃ f' l', ConstToFVar kns ids f f' ∧ l'.length = l.length ∧
        (∀ i, i < l.length → ConstToFVar kns ids l[i]! l'[i]!) ∧ w = LBTerm.mkApps f' l' := by
  intro l
  induction l with
  | nil => exact fun f w h => ⟨w, [], h, rfl, fun i hi => absurd hi (by simp), rfl⟩
  | cons a as ih =>
      intro f w h
      obtain ⟨g, as', hg, hlen, hpt, rfl⟩ := ih (.app f a) w h
      cases hg with
      | @app _ f' _ a' hf ha =>
          refine ⟨f', a' :: as', hf, by simp [hlen], ?_, rfl⟩
          intro i hi
          match i with
          | 0 => simpa using ha
          | k + 1 =>
              have hk : k < as.length := by simpa using hi
              rw [getElem!_pos (a :: as) (k + 1) (by simp; omega),
                getElem!_pos (a' :: as') (k + 1) (by simp [hlen]; omega),
                List.getElem_cons_succ, List.getElem_cons_succ,
                ← getElem!_pos as k hk, ← getElem!_pos as' k (by omega)]
              exact hpt k hk

/-- Inversion through a lambda telescope: only the binder names are free. -/
theorem ConstToFVar.mkLambdas_inv {kns : List Kername} {ids : List FVarId} :
    ∀ (ns : List BinderName) (b w : LBTerm), ConstToFVar kns ids (mkLambdas ns b) w →
      ∃ ns' b', ns'.length = ns.length ∧ ConstToFVar kns ids b b' ∧ w = mkLambdas ns' b' := by
  intro ns
  induction ns with
  | nil => exact fun b w h => ⟨[], w, rfl, h, rfl⟩
  | cons n ns ih =>
      intro b w h
      rw [show mkLambdas (n :: ns) b = .lambda n (mkLambdas ns b) from rfl] at h
      cases h with
      | @lambda _ n₂ _ w₀ h₀ =>
          obtain ⟨ns', b', hl, hb, rfl⟩ := ih b w₀ h₀
          exact ⟨n₂ :: ns', b', by simp [hl], hb, rfl⟩

/-- A de Bruijn index relates only to itself. -/
theorem ConstToFVar.bvar_target {kns : List Kername} {ids : List FVarId} {m : Nat}
    {u : LBTerm} (h : ConstToFVar kns ids (.bvar m) u) : u = .bvar m := by cases h; rfl

/-- Inversion through a `shift`: the rewriting reads no de Bruijn index, so a related image
of a shifted term is the shift of a related image. -/
theorem ConstToFVar.of_shift {kns : List Kername} {ids : List FVarId} :
    ∀ (t : LBTerm) (d c : Nat) (w : LBTerm), ConstToFVar kns ids (LBTerm.shift d c t) w →
      ∃ u, ConstToFVar kns ids t u ∧ w = LBTerm.shift d c u := by
  intro t
  induction t using LBTerm.recData with
  | hbox => intro d c w h; cases h; exact ⟨.box, .box, rfl⟩
  | hbvar i =>
      intro d c w h
      refine ⟨.bvar i, ConstToFVar.bvar i, ?_⟩
      rw [LBTerm.shift_bvar] at h ⊢
      by_cases hi : i ≥ c
      · rw [if_pos hi] at h ⊢; cases h; rfl
      · rw [if_neg hi] at h ⊢; cases h; rfl
  | hfvar x => intro d c w h; cases h; exact ⟨.fvar x, ConstToFVar.fvar x, rfl⟩
  | hprim p => intro d c w h; cases h; exact ⟨.prim p, ConstToFVar.prim p, rfl⟩
  | hconst kn =>
      intro d c w h
      cases h with
      | hit hkn hx => exact ⟨.fvar _, .hit hkn hx, rfl⟩
      | miss hkn => exact ⟨.const kn, .miss hkn, rfl⟩
  | hlam n b ih =>
      intro d c w h
      simp only [LBTerm.shift] at h
      cases h with
      | @lambda _ n₂ _ b₂ h₀ =>
          obtain ⟨u, hu, rfl⟩ := ih d (c + 1) b₂ h₀
          exact ⟨.lambda n₂ u, .lambda hu, rfl⟩
  | hletIn n v b ihv ihb =>
      intro d c w h
      simp only [LBTerm.shift] at h
      cases h with
      | @letIn _ n₂ _ v₂ _ b₂ hv hb =>
          obtain ⟨uv, huv, rfl⟩ := ihv d c v₂ hv
          obtain ⟨ub, hub, rfl⟩ := ihb d (c + 1) b₂ hb
          exact ⟨.letIn n₂ uv ub, .letIn huv hub, rfl⟩
  | happ f a ihf iha =>
      intro d c w h
      simp only [LBTerm.shift] at h
      cases h with
      | @app _ f₂ _ a₂ hf ha =>
          obtain ⟨uf, huf, rfl⟩ := ihf d c f₂ hf
          obtain ⟨ua, hua, rfl⟩ := iha d c a₂ ha
          exact ⟨.app uf ua, .app huf hua, rfl⟩
  | hproj p e ih =>
      intro d c w h
      simp only [LBTerm.shift] at h
      cases h with
      | @proj _ _ e₂ h₀ =>
          obtain ⟨u, hu, rfl⟩ := ih d c e₂ h₀
          exact ⟨.proj p u, .proj hu, rfl⟩
  | hfix defs i _ =>
      intro d c w h
      simp only [LBTerm.shift] at h
      cases h
      exact ⟨.fix defs i, .fix defs i, rfl⟩
  | hconstruct iid k args ih =>
      intro d c w h
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map] at h
      cases h with
      | @construct _ _ _ A' hlen hpt =>
          rw [List.length_map] at hlen hpt
          obtain ⟨us, hus, hpts⟩ := exists_list_of_index args.length
            (fun i u => ConstToFVar kns ids args[i]! u ∧ A'[i]! = LBTerm.shift d c u)
            (fun i hi => by
              have := hpt i hi
              rw [Lower.getElem!_map (LBTerm.shift d c) args i hi] at this
              exact ih args[i]! (Lower.getElem!_mem hi) d c _ this)
          refine ⟨.construct iid k us, .construct hus (fun i hi => (hpts i hi).1), ?_⟩
          simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
          congr 1
          refine list_eq_of_getElem! (by simp [hlen, hus]) (fun i hi => ?_)
          rw [Lower.getElem!_map (LBTerm.shift d c) us i (by omega)]
          exact (hpts i (by omega)).2
  | hcase info discr alts ihd iha =>
      intro d c w h
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map] at h
      cases h with
      | @«case» _ _ dd' _ A' hd hlen hn hb =>
          obtain ⟨ud, hud, rfl⟩ := ihd d c dd' hd
          rw [List.length_map] at hlen hn hb
          obtain ⟨us, hus, hpts⟩ := exists_list_of_index alts.length
            (fun (i : Nat) (p : List BinderName × LBTerm) => p.1 = (A'[i]!).1 ∧
              ConstToFVar kns ids (alts[i]!).2 p.2 ∧
              (A'[i]!).2 = LBTerm.shift d (c + (alts[i]!).1.length) p.2)
            (fun i hi => by
              have hbi := hb i hi
              rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi] at hbi
              obtain ⟨u, hu, heq⟩ := iha alts[i]! (Lower.getElem!_mem hi) d
                (c + (alts[i]!).1.length) _ hbi
              exact ⟨((A'[i]!).1, u), rfl, hu, heq⟩)
          have hn' : ∀ i, i < alts.length → (us[i]!).1.length = (alts[i]!).1.length := by
            intro i hi
            rw [(hpts i hi).1]
            have := hn i hi
            rwa [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi] at this
          refine ⟨.case info ud us, .case hud hus hn' (fun i hi => (hpts i hi).2.1), ?_⟩
          simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map]
          congr 1
          refine (list_eq_of_getElem! (by simp [hlen, hus]) (fun i hi => ?_)).symm
          rw [List.length_map] at hi
          rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
            (a.1, LBTerm.shift d (c + a.1.length) a.2)) us i (by omega)]
          have hi' : i < alts.length := by omega
          refine Prod.ext (hpts i hi').1 ?_
          show LBTerm.shift d (c + (us[i]!).1.length) (us[i]!).2 = (A'[i]!).2
          rw [hn' i hi', (hpts i hi').2.2]

/-- Inversion of a pointwise `ConstToFVar` list through an append: the image splits at the
same place. -/
theorem ConstToFVar.list_append_inv {kns : List Kername} {ids : List FVarId}
    {l₁ l₂ L : List LBTerm} (hlen : L.length = (l₁ ++ l₂).length)
    (h : ∀ i, i < (l₁ ++ l₂).length → ConstToFVar kns ids (l₁ ++ l₂)[i]! L[i]!) :
    ∃ L₁ L₂, L = L₁ ++ L₂ ∧ L₁.length = l₁.length ∧ L₂.length = l₂.length ∧
      (∀ i, i < l₁.length → ConstToFVar kns ids l₁[i]! L₁[i]!) ∧
      (∀ i, i < l₂.length → ConstToFVar kns ids l₂[i]! L₂[i]!) := by
  rw [List.length_append] at hlen
  refine ⟨L.take l₁.length, L.drop l₁.length, (List.take_append_drop _ _).symm,
    by simp; omega, by simp; omega, ?_, ?_⟩
  · intro i hi
    have h1 : (l₁ ++ l₂)[i]! = l₁[i]! := by
      rw [getElem!_pos (l₁ ++ l₂) i (by simp; omega), getElem!_pos l₁ i hi,
        List.getElem_append_left hi]
    have h2 : (L.take l₁.length)[i]! = L[i]! := by
      rw [getElem!_pos (L.take l₁.length) i (by simp; omega), getElem!_pos L i (by omega),
        List.getElem_take]
    rw [h2, ← h1]
    exact h i (by simp; omega)
  · intro i hi
    have h1 : (l₁ ++ l₂)[l₁.length + i]! = l₂[i]! := by
      rw [getElem!_pos (l₁ ++ l₂) (l₁.length + i) (by simp; omega), getElem!_pos l₂ i hi,
        List.getElem_append_right (by omega)]
      simp
    have h2 : (L.drop l₁.length)[i]! = L[l₁.length + i]! := by
      rw [getElem!_pos (L.drop l₁.length) i (by simp; omega),
        getElem!_pos L (l₁.length + i) (by omega), List.getElem_drop]
    rw [h2, ← h1]
    exact h (l₁.length + i) (by simp; omega)


/-! ## `substFix` through the spine, telescope and shift operators

`FixUnfold.lean` carries the per-node push-through equations for `substFVarList`. The
`Lower` arms need three more shapes: an application spine, a lambda telescope, and a
`shift` — the last one commutes because every substituted term is a closed `.fix` node. -/

/-- Replacing an fvar by a closed term commutes with `shift`. -/
theorem substFVar_shift_comm {x : FVarId} {s : LBTerm} (hs : LBClosed s 0) :
    ∀ (t : LBTerm) (d c : Nat),
      substFVar x s (LBTerm.shift d c t) = LBTerm.shift d c (substFVar x s t) := by
  intro t
  induction t using LBTerm.recData with
  | hbox | hconst | hprim => intro d c; rfl
  | hbvar i =>
      intro d c
      show substFVar x s (LBTerm.shift d c (LBTerm.bvar i)) = LBTerm.shift d c (LBTerm.bvar i)
      rw [LBTerm.shift_bvar]
      split <;> rfl
  | hfvar y =>
      intro d c
      simp only [LBTerm.shift, substFVar]
      by_cases h : (y == x) = true
      · rw [if_pos h]; exact (hs.shift_eq (Nat.zero_le c) d).symm
      · rw [if_neg h]; rfl
  | hlam n b ih => intro d c; simp only [LBTerm.shift, substFVar, ih d (c + 1)]
  | hletIn n v b ihv ihb =>
      intro d c; simp only [LBTerm.shift, substFVar, ihv d c, ihb d (c + 1)]
  | happ f a ihf iha => intro d c; simp only [LBTerm.shift, substFVar, ihf d c, iha d c]
  | hproj p e ih => intro d c; simp only [LBTerm.shift, substFVar, ih d c]
  | hconstruct iid k args ih =>
      intro d c
      simp only [LBTerm.shift, substFVar, LBTerm.shiftArgs_eq_map, substFVarArgs_eq_map,
        List.map_map]
      congr 1
      refine List.map_congr_left (fun a ha => ?_)
      simp only [Function.comp]; exact ih a ha d c
  | hcase info discr alts ihd iha =>
      intro d c
      simp only [LBTerm.shift, substFVar, LBTerm.shiftAlts_eq_map, substFVarAlts_eq_map,
        List.map_map, ihd d c]
      congr 1
      refine List.map_congr_left (fun a ha => ?_)
      simp only [Function.comp]
      exact Prod.ext rfl (iha a ha d (c + a.1.length))
  | hfix defs i ih =>
      intro d c
      simp only [LBTerm.shift, substFVar, LBTerm.shiftDefs_eq_map, substFVarDefs_eq_map,
        List.map_map, List.length_map]
      congr 1
      refine List.map_congr_left (fun fd hfd => ?_)
      simp only [Function.comp]
      exact congrArg (fun b => ({ fd with body := b } : @FixDef LBTerm))
        (ih fd hfd d (c + defs.length))

/-- The simultaneous form of `substFVar_shift_comm`. -/
theorem substFVarList_shift_comm : ∀ (L : List (FVarId × LBTerm)), (∀ p ∈ L, LBClosed p.2 0) →
    ∀ (t : LBTerm) (d c : Nat),
      substFVarList L (LBTerm.shift d c t) = LBTerm.shift d c (substFVarList L t) := by
  intro L
  induction L with
  | nil => intro _ _ _ _; rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      intro hcl t d c
      show substFVar y u (substFVarList rest (LBTerm.shift d c t)) = _
      rw [ih (fun q hq => hcl q (List.mem_cons_of_mem _ hq)) t d c,
        substFVar_shift_comm (hcl (y, u) (List.mem_cons_self ..)) _ d c]
      rfl

/-- `substFix` commutes with `shift`: the block it installs is closed. -/
theorem substFix_shift_comm {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hdcl : ∀ j, LBClosed (LBTerm.fix defs j) 0) (t : LBTerm) (d c : Nat) :
    substFix ids defs (LBTerm.shift d c t) = LBTerm.shift d c (substFix ids defs t) :=
  substFVarList_shift_comm _ (fun p hp => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact hdcl q.2) t d c

/-- `substFVarList` distributes over an application spine. -/
theorem substFVarList_mkApps (L : List (FVarId × LBTerm)) :
    ∀ (l : List LBTerm) (f : LBTerm), substFVarList L (LBTerm.mkApps f l)
      = LBTerm.mkApps (substFVarList L f) (l.map (substFVarList L)) := by
  intro l
  induction l with
  | nil => intro f; rfl
  | cons a as ih => intro f; simpa [LBTerm.mkApps] using ih (.app f a)

/-- `substFVarList` pushes into a lambda telescope, binder names untouched. -/
theorem substFVarList_mkLambdas (L : List (FVarId × LBTerm)) :
    ∀ (ns : List BinderName) (b : LBTerm),
      substFVarList L (mkLambdas ns b) = mkLambdas ns (substFVarList L b) := by
  intro ns
  induction ns with
  | nil => intro b; rfl
  | cons n ns ih => intro b; simp only [mkLambdas, substFVarList_lambda, ih]

/-- A telescope's own arguments are de Bruijn indices, which no fvar substitution moves. -/
theorem substFVarList_bvarsDesc (L : List (FVarId × LBTerm)) (n : Nat) :
    (bvarsDesc n).map (substFVarList L) = bvarsDesc n := by
  refine (List.map_congr_left fun t ht => ?_).trans (List.map_id _)
  obtain ⟨i, _, rfl⟩ := bvarsDesc_mem ht
  simp


/-! ### `substFix` per node

The nine `substFVarList_*` equations of `FixUnfold.lean`, read at `substFix` (which is
`substFVarList` at the block's own list), plus the `.prim` clause, the spine and the telescope. -/

section SubstFixNodes
variable {ids : List FVarId} {defs : List (@FixDef LBTerm)}

/-- The `.prim` clause missing from `FixUnfold.lean`'s per-node family. -/
@[simp] theorem substFVarList_prim (L : List (FVarId × LBTerm)) (p : PrimVal) :
    substFVarList L (.prim p) = .prim p := by
  induction L with
  | nil => rfl
  | cons q rest ih => obtain ⟨y, u⟩ := q; simp only [substFVarList, ih]; rfl

@[simp] theorem substFix_box : substFix ids defs .box = .box := substFVarList_box _
@[simp] theorem substFix_bvar (i : Nat) : substFix ids defs (.bvar i) = .bvar i :=
  substFVarList_bvar _ i
@[simp] theorem substFix_prim (p : PrimVal) : substFix ids defs (.prim p) = .prim p :=
  substFVarList_prim _ p
@[simp] theorem substFix_const (kn : Kername) : substFix ids defs (.const kn) = .const kn :=
  substFVarList_const _ kn
@[simp] theorem substFix_lambda (n : BinderName) (b : LBTerm) :
    substFix ids defs (.lambda n b) = .lambda n (substFix ids defs b) :=
  substFVarList_lambda _ n b
@[simp] theorem substFix_letIn (n : BinderName) (v b : LBTerm) :
    substFix ids defs (.letIn n v b) = .letIn n (substFix ids defs v) (substFix ids defs b) :=
  substFVarList_letIn _ n v b
@[simp] theorem substFix_app (f a : LBTerm) :
    substFix ids defs (.app f a) = .app (substFix ids defs f) (substFix ids defs a) :=
  substFVarList_app _ f a
@[simp] theorem substFix_proj (pinfo : ProjectionInfo) (e : LBTerm) :
    substFix ids defs (.proj pinfo e) = .proj pinfo (substFix ids defs e) :=
  substFVarList_proj _ pinfo e
theorem substFix_construct (iid : InductiveId) (k : Nat) (args : List LBTerm) :
    substFix ids defs (.construct iid k args)
      = .construct iid k (args.map (substFix ids defs)) :=
  substFVarList_construct _ iid k args
theorem substFix_case (info : InductiveId × Nat) (discr : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    substFix ids defs (.case info discr alts)
      = .case info (substFix ids defs discr)
          (alts.map (fun a => (a.1, substFix ids defs a.2))) :=
  substFVarList_case _ info discr alts
theorem substFix_mkApps (f : LBTerm) (l : List LBTerm) :
    substFix ids defs (LBTerm.mkApps f l)
      = LBTerm.mkApps (substFix ids defs f) (l.map (substFix ids defs)) :=
  substFVarList_mkApps _ l f
theorem substFix_mkLambdas (ns : List BinderName) (b : LBTerm) :
    substFix ids defs (mkLambdas ns b) = mkLambdas ns (substFix ids defs b) :=
  substFVarList_mkLambdas _ ns b
theorem substFix_bvarsDesc (n : Nat) :
    (bvarsDesc n).map (substFix ids defs) = bvarsDesc n := substFVarList_bvarsDesc _ n

end SubstFixNodes


/-! ## The transport -/

/-- **The transport that makes the fix arms usable.** A fix unfolding
(`WcbvEval.fix_guarded`'s substitution, which `closeFix_substList_fixSubst` rewrites to
`substFix ids defs`) puts `.fix defs j` where the lowered body carries the sibling
`.const kns[j]`, and the result is still `Lower`-related to the same specification term.
`hfv` replaces the design's inert `LBClosed t 0`, and is free at the call site — `t` is a
lowered body and `hfv` is `LowerBlock.hfresh`;
`LowerFixFixture.constToFix_needs_freshness` refutes the statement without it. `hΓ` closes
the installed block, which the `elimApp` alternatives and `fixBody` need. -/
theorem Lower.constToFix {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {s t t' : LBTerm}
    (hΓ : ClosedBodies Γ) (hblk : LowerBlock Γ kns bs bs' ids defs)
    (hfv : ∀ x ∈ ids, ¬ hasFVar x t) (h : Lower Γ s t)
    (hct : ConstToFVar kns ids t t') :
    Lower Γ s (substFix ids defs t') := by
  have hdcl : ∀ j, LBClosed (LBTerm.fix defs j) 0 := hblk.lbClosed_fix hΓ
  have hself : ∀ u : LBTerm, (∀ x ∈ ids, ¬ hasFVar x u) → substFix ids defs u = u := by
    intro u hu
    refine substFVarList_eq_self_of_not_hasFVar _ u (fun q hq => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hu r.1 (List.fst_mem_of_mem_zipIdx hr)
  have hhit : ∀ (j : Nat) (x : FVarId), ids[j]? = some x →
      substFix ids defs (.fvar x) = .fix defs j := by
    intro j x hx
    obtain ⟨hj, hxe⟩ := Lower.getElem!_of_getElem? hx
    have hix : ids[j]'hj = x := by rw [← getElem!_pos ids j hj]; exact hxe
    rw [← hix]
    exact substFix_fvar_getElem hblk.hids hblk.not_hasFVar_fix j hj
  have main : ∀ (p q : LBTerm), Lower Γ p q → (∀ x ∈ ids, ¬ hasFVar x q) →
      ∀ q', ConstToFVar kns ids q q' → Lower Γ p (substFix ids defs q') := by
    intro p q hpq
    induction hpq using Lower.rec
      (motive_2 := fun nf m alt _ => (∀ x ∈ ids, ¬ hasFVar x alt.2) →
        ∀ (ns₂ : List BinderName) (a₂ : LBTerm), ns₂.length = alt.1.length →
        ConstToFVar kns ids alt.2 a₂ → LowerAlt Γ nf m (ns₂, substFix ids defs a₂)) with
    | box => intro _ q' hcw; cases hcw; rw [substFix_box]; exact .box
    | bvar i => intro _ q' hcw; cases hcw; rw [substFix_bvar]; exact .bvar i
    | fvar x => intro hnf q' hcw; cases hcw; rw [hself _ hnf]; exact .fvar x
    | prim pr => intro _ q' hcw; cases hcw; rw [substFix_prim]; exact .prim pr
    | @const kn hk =>
        intro _ q' hcw
        cases hcw with
        | @hit j _ x hkn hx => rw [hhit j x hx]; exact Lower.fixConst' hblk hk hkn
        | miss _ => rw [substFix_const]; exact .const hk
    | @lambda n n' b b' _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @lambda _ n₂ _ b₂ h₀ =>
            rw [substFix_lambda]
            exact .lambda (ih (fun x hx => by simpa using hnf x hx) b₂ h₀)
    | @letIn n n' v v' b b' _ _ ihv ihb =>
        intro hnf q' hcw
        cases hcw with
        | @letIn _ n₂ _ v₂ _ b₂ hv₂ hb₂ =>
            rw [substFix_letIn]
            refine .letIn (ihv (fun x hx hc => hnf x hx (.inl hc)) v₂ hv₂)
              (ihb (fun x hx hc => hnf x hx (.inr hc)) b₂ hb₂)
    | @app f f' a a' _ _ ihf iha =>
        intro hnf q' hcw
        cases hcw with
        | @app _ f₂ _ a₂ hf₂ ha₂ =>
            rw [substFix_app]
            exact .app (ihf (fun x hx hc => hnf x hx (.inl hc)) f₂ hf₂)
              (iha (fun x hx hc => hnf x hx (.inr hc)) a₂ ha₂)
    | @proj pinfo e e' _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @proj _ _ e₂ h₀ =>
            rw [substFix_proj]
            exact .proj (ih (fun x hx => by simpa using hnf x hx) e₂ h₀)
    | @construct iid k args args' hlen _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @construct _ _ _ A₂ hlen₂ hpt₂ =>
            rw [substFix_construct]
            refine .construct (by simp [hlen₂, hlen]) (fun i hi => ?_)
            rw [Lower.getElem!_map (substFix ids defs) A₂ i (by omega)]
            refine ih i hi (fun x hx hc => hnf x hx ?_) A₂[i]! (hpt₂ i (by omega))
            rw [hasFVar_construct, hasFVarArgs_iff]
            exact ⟨_, Lower.getElem!_mem (by omega), hc⟩
    | @«case» ip d d' alts alts' _ hlen hn _ ihd ihb =>
        intro hnf q' hcw
        cases hcw with
        | @«case» _ _ D₂ _ A₂ hd₂ hlen₂ hn₂ hb₂ =>
            rw [substFix_case]
            refine .case (ihd (fun x hx hc => hnf x hx (.inl hc)) D₂ hd₂)
              (by simp [hlen₂, hlen]) (fun i hi => ?_) (fun i hi => ?_)
            · rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, substFix ids defs a.2)) A₂ i (by omega)]
              exact (hn₂ i (by omega)).trans (hn i hi)
            · rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, substFix ids defs a.2)) A₂ i (by omega)]
              refine ihb i hi (fun x hx hc => hnf x hx ?_) (A₂[i]!).2 (hb₂ i (by omega))
              rw [hasFVar_case, hasFVarAlts_iff]
              exact .inr ⟨_, Lower.getElem!_mem (by omega), hc⟩
    | @elimApp knE iid np dp nfs pre disc disc' minors alts extra extra'
        hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
        intro hnf q' hcw
        obtain ⟨f₂, L₂, hf₂, hlen₂, hpt₂, rfl⟩ :=
          ConstToFVar.mkApps_inv extra' (.case (iid, np) disc' alts) q' hcw
        cases hf₂ with
        | @«case» _ _ D₂ _ A₂ hd₂ hAlen hAn hAb =>
            have hdiscfv : ∀ x ∈ ids, ¬ hasFVar x disc' := by
              intro x hx hcc
              exact hnf x hx ((hasFVar_mkApps x extra' _).mpr (.inl (.inl hcc)))
            rw [substFix_mkApps, substFix_case]
            refine .elimApp hh hlen hmlen (by simp [hAlen, halen]) (fun i hi => ?_)
              (ihd hdiscfv D₂ hd₂) (by simp [hlen₂, hxlen]) (fun i hi => ?_)
            · rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, substFix ids defs a.2)) A₂ i (by omega)]
              refine ihmin i hi (fun x hx hcc => hnf x hx ?_) (A₂[i]!).1 (A₂[i]!).2 ?_
                (hAb i (by omega))
              · refine (hasFVar_mkApps x extra' _).mpr (.inl (.inr ?_))
                rw [hasFVarAlts_iff]
                exact ⟨_, Lower.getElem!_mem (by omega), hcc⟩
              · exact (hAn i (by omega))
            · rw [Lower.getElem!_map (substFix ids defs) L₂ i (by omega)]
              refine ihx i hi (fun x hx hcc => hnf x hx ?_) L₂[i]! (hpt₂ i (by omega))
              exact (hasFVar_mkApps x extra' _).mpr (.inr ⟨_, Lower.getElem!_mem (by omega), hcc⟩)
    | @fixConst kn kns₀ bs₀ bs₀' ids₀ defs₀ j hb hb' hd₀ hnd hids hilen hfresh hrarg
        hdecl hfl hlow hcl hnk hj _ =>
        intro hnf q' hcw
        cases hcw
        rw [hself _ hnf]
        exact .fixConst hb hb' hd₀ hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hnk hj
    | @fixBody b kns₀ bs₀ bs₀' ids₀ defs₀ j hb hb' hd₀ hnd hids hilen hfresh hrarg
        hdecl hfl hlow hcl hj hjl _ =>
        intro hnf q' hcw
        cases hcw
        rw [hself _ hnf]
        exact .fixBody hb hb' hd₀ hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
    -- The η-wrapper is a λ over an application, so `ConstToFVar` walks into it and may
    -- rename the binder; the arm's binder name is free for exactly this reason.
    | @fixEta b nm kns₀ bs₀ bs₀' ids₀ defs₀ j hb hb' hd₀ hnd hids hilen hfresh hrarg
        hdecl hfl hlow hcl hj hjl _ =>
        intro hnf q' hcw
        cases hcw with
        | @lambda _ nm' _ b' hlam =>
            cases hlam with
            | @app _ f' _ a' hf ha =>
                cases hf
                cases ha
                rw [hself _ (fun x hx hcc => hnf x hx (by
                  simpa only [hasFVar_lambda, hasFVar_app, hasFVar_bvar, or_false] using hcc))]
                exact .fixEta hb hb' hd₀ hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
    | @done m b _ ih =>
        rename_i hnf ns₂ a₂ hnl hca
        have : ns₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hnl)
        subst this
        exact .done (ih hnf a₂ hca)
    | @lam nf n n' m alt _ ih =>
        rename_i hnf ns₂ a₂ hnl hca
        match ns₂, hnl with
        | n₂ :: rest, hnl =>
            exact .lam (alt := (rest, substFix ids defs a₂))
              (ih hnf rest a₂ (by simpa using hnl) hca)
  exact main s t h hfv t' hct


/-! ## The two eliminator shapes, and the fix unfolding

`Lower.fixUnfold` is what the target does where the source δ-steps into a recursive body.
Its λ-headedness input is `LowerBlock.hfl`, read off the block; the transports that turn
that field into a fact about the specification bodies are in `Lower.lean`, beside
`LowerBlock` itself. -/

/-- Neither eliminator body is a lambda whose binder carries a source name: `mkElimBody`'s
telescope is `.anon` throughout and `mkElimBodyRec` is a `.fix`. -/
theorem not_elimBody_lambda_named {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    {nm : String} {b : LBTerm} : ¬ ElimBody iid np dp nfs (.lambda (.named nm) b) := by
  have shape : ∀ (h : LBTerm), ElimBody iid np dp nfs h →
      h = mkElimBody iid np dp nfs ∨ h = mkElimBodyRec iid np dp nfs := by
    intro h hb; cases hb with
    | cases => exact .inl rfl
    | recur => exact .inr rfl
  intro hb
  rcases shape _ hb with he | he
  · rw [mkElimBody, show dp + 1 + nfs.length = (dp + nfs.length) + 1 by omega,
      List.replicate_succ] at he
    injection he with h₁ _
    exact BinderName.noConfusion h₁
  · rw [mkElimBodyRec] at he
    exact LBTerm.noConfusion he

/-- **A block member's unfolded definition is a λ, still related to the member's
specification body.** The emitted `.fix` fires (`hrarg` pins the principal argument to
`0`), `LowerBlock.hfl` gives the unfolded body its λ head, and `Lower.constToFix` carries
the relation across the substitution. The transport the β and δ arms of the simulation
spend is `Lower.appReady` (`ErasesCorrect/Steps.lean`), which takes a derivation rather
than a block; `hfl` is what gives its two block sub-cases a λ to β-step into. -/
theorem Lower.fixUnfold {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblock : LowerBlock Γ kns bs bs' ids defs) (hjl : j < defs.length) :
    ∃ n b, LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body = .lambda n b ∧
      Lower Γ bs[j]! (.lambda n b) := by
  have hjk : j < kns.length := by rw [← hblock.hd]; exact hjl
  obtain ⟨u, hct, heq⟩ := hblock.hcl j hjk
  have hbs' : LBClosed bs'[j]! 0 :=
    Lower.closed hΓ (hblock.hlow j hjk) 0 (hΓ _ _ (hblock.hdecl j hjk))
  have hu : LBClosed u 0 := hct.closed hbs'
  have hsub : LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body = substFix ids defs u := by
    rw [heq]; exact hblock.substList_fixSubst hΓ hu
  have hlam : isLambda (LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body) = true :=
    isLambda_substList _ (hblock.hfl j hjl)
  obtain ⟨n, b, hnb⟩ := isLambda_eq_true hlam
  refine ⟨n, b, hnb, ?_⟩
  have hlow : Lower Γ bs[j]! (substFix ids defs u) :=
    Lower.constToFix hΓ hblock (fun x hx => hblock.hfresh x hx j hjk) (hblock.hlow j hjk) hct
  rw [← hsub, hnb] at hlow
  exact hlow

/-! ## The fixture `lowerfix_nv`

A two-member mutual block, hand-built, carrying the whole wall: a `LowerBlock` with shared
`ids` and `hrarg`, the value-side fix arm, the target environment's δ step to the block,
one application step that fires `fix_guarded` **through** the block (member 1 calls member
0), the λ-headedness transport, and the `ErasesLBFix` stateability witness. -/

namespace LowerFixFixture

/-- Member 0's source name. -/
def name₀ : Lean.Name := .mkSimple "lfA"
/-- Member 1's source name. -/
def name₁ : Lean.Name := .mkSimple "lfB"
/-- Member 0's kername, the value `toKername` gives its source name. -/
def kn₀ : Kername := { mp := .MPfile [], id := "lfA" }
/-- Member 1's kername. -/
def kn₁ : Kername := { mp := .MPfile [], id := "lfB" }
/-- The block's names. -/
def kns : List Kername := [kn₀, kn₁]
/-- The block's fixvars — one list for the whole block, as `visitMutual` mints it. -/
def ids : List FVarId := [⟨.mkSimple "lfV0"⟩, ⟨.mkSimple "lfV1"⟩]
/-- Member 0's specification body: `λ x. □`. -/
def b₀ : LBTerm := .lambda (.named "x") .box
/-- Member 1's specification body: `λ x. lfA x` — the call into member 0. -/
def b₁ : LBTerm := .lambda (.named "x") (.app (.const kn₀) (.bvar 0))
/-- The specification bodies. -/
def bs : List LBTerm := [b₀, b₁]
/-- The emitted block: member 1's call site is the fix binder `.bvar 2`. -/
def defs : List (@FixDef LBTerm) :=
  [ { name := .named "lf0", body := .lambda (.named "x") .box },
    { name := .named "lf1", body := .lambda (.named "x") (.app (.bvar 2) (.bvar 0)) } ]
/-- The specification environment: the members hold their plain bodies. -/
def specEnv : GlobalDeclarations :=
  [(kn₀, .constantDecl ⟨some b₀⟩), (kn₁, .constantDecl ⟨some b₁⟩)]
/-- The emitted environment: the members hold the block. -/
def targetEnv : GlobalDeclarations :=
  [(kn₀, .constantDecl ⟨some (.fix defs 0)⟩), (kn₁, .constantDecl ⟨some (.fix defs 1)⟩)]

/-- The kernames are the ones `toKername` produces for the source names. -/
theorem toKername_name₀ : toKername name₀ = kn₀ := rfl

/-- The two members are distinct. -/
theorem kn₀_ne_kn₁ : kn₀ ≠ kn₁ := fun h =>
  absurd (congrArg Kername.id h) (by decide)

/-- Member 0 is declared. -/
theorem decl₀ : DefnDecl specEnv kn₀ b₀ := rfl

/-- Member 1 is declared. -/
theorem decl₁ : DefnDecl specEnv kn₁ b₁ := rfl

/-- Two declarations of one constant carry the same body. -/
theorem body_inj {b b' : LBTerm}
    (h : (some (.constantDecl ⟨some b⟩) : Option GlobalDecl) = some (.constantDecl ⟨some b'⟩)) :
    b = b' := by
  injection h with h; injection h with h; injection h with h; exact Option.some.inj h

/-- Only the two members are declared. -/
theorem specEnv_body_eq {kn : Kername} {b : LBTerm} (h : DefnDecl specEnv kn b) :
    b = b₀ ∨ b = b₁ := by
  rw [DefnDecl, specEnv, LBTerm.envLookup] at h
  split at h
  · exact .inl (body_inj h).symm
  · rw [LBTerm.envLookup] at h
    split at h
    · exact .inr (body_inj h).symm
    · exact absurd h (by simp [LBTerm.envLookup])

/-- Both member bodies are λs with a source binder name. -/
theorem specEnv_body {kn : Kername} {b : LBTerm} (h : DefnDecl specEnv kn b) :
    ∃ (nm : String) (u : LBTerm), b = .lambda (.named nm) u := by
  rcases specEnv_body_eq h with rfl | rfl
  · exact ⟨"x", .box, rfl⟩
  · exact ⟨"x", _, rfl⟩

/-- Neither member is a runtime key: a λ with a source binder name is neither eliminator
shape. -/
theorem not_runtimeKey {kn : Kername} {b : LBTerm} (h : DefnDecl specEnv kn b) :
    ¬ RuntimeKey specEnv kn := by
  obtain ⟨nm, u, rfl⟩ := specEnv_body h
  rw [DefnDecl] at h
  rintro ⟨iid, np, dp, nfs, ⟨body, hd, hbody⟩, -⟩
  rw [← body_inj (h.symm.trans hd)] at hbody
  exact not_elimBody_lambda_named hbody

/-- The lowering is the identity on the specification bodies: nothing in them is a
constructor or eliminator key. -/
theorem lower_bs : ∀ i, i < kns.length → Lower specEnv bs[i]! bs[i]! := by
  intro i hi
  match i, hi with
  | 0, _ => exact .lambda .box
  | 1, _ => exact .lambda (.app (.const (not_runtimeKey decl₀)) (.bvar 0))

/-- (iii) The emitted definitions are λ-headed, from the fixture's own `defs`. -/
theorem lowerfix_fixLambda : ∀ j, j < defs.length → isLambda (defs[j]!).body = true := by
  intro j hj
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl

/-- **The fixture.** A two-member mutual block as a `LowerBlock`, at the block-shared
`ids` and with `hrarg` (`principalArgIdx = 0`, which is what makes one application step
consume exactly one argument). -/
theorem lowerfix_nv : LowerBlock specEnv kns bs bs ids defs where
  hb := rfl
  hb' := rfl
  hd := rfl
  hnd :=
    List.Pairwise.cons
      (fun a ha => by cases ha with
        | head => exact kn₀_ne_kn₁
        | tail _ h => nomatch h)
      (List.Pairwise.cons (fun a ha => nomatch ha) .nil)
  hids :=
    List.Pairwise.cons
      (fun a ha => by cases ha with
        | head => exact fun he => absurd (congrArg Lean.FVarId.name he) (by decide)
        | tail _ h => nomatch h)
      (List.Pairwise.cons (fun a ha => nomatch ha) .nil)
  hilen := rfl
  hfresh := by
    intro x _ i hi
    match i, hi with
    | 0, _ => exact fun hc => hc
    | 1, _ => rintro (hc | hc) <;> exact hc
  hrarg := by
    intro d hd
    cases hd with
    | head => rfl
    | tail _ hd =>
        cases hd with
        | head => rfl
        | tail _ hd => nomatch hd
  hdecl := by
    intro i hi
    match i, hi with
    | 0, _ => exact decl₀
    | 1, _ => exact decl₁
  hfl := lowerfix_fixLambda
  hlow := lower_bs
  hcl := by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨b₀, .lambda .box, rfl⟩
    | 1, _ =>
        exact ⟨.lambda (.named "x") (.app (.fvar ids[0]!) (.bvar 0)),
          .lambda (.app (.hit (j := 0) rfl rfl) (.bvar 0)), rfl⟩

/-! ### The four obligations, on the fixture -/

/-- The specification environment's bodies are closed. -/
theorem closedBodies_specEnv : ClosedBodies specEnv := by
  intro kn b h
  rcases specEnv_body_eq h with rfl | rfl
  · exact trivial
  · exact ⟨trivial, Nat.zero_lt_one⟩

/-- (ii) The value-side fix arm: member 1's specification body relates to the block. -/
theorem lowerfix_fixBody : Lower specEnv bs[1]! (.fix defs 1) :=
  Lower.fixBody' lowerfix_nv rfl (Nat.lt_succ_self 1)

/-- **The η arm fires on the same block**, at the same member and the same premises: the
body relates to the wrapper `Erasure.visitMutual` registers, not only to the bare node.
Non-vacuity for `Lower.fixEta`. -/
theorem lowerfix_fixEta : Lower specEnv bs[1]! (LBTerm.etaFix defs 1) :=
  Lower.fixEta' lowerfix_nv rfl (Nat.lt_succ_self 1)

/-- **Why `Lower.fixEta`'s binder name is free.** `ConstToFVar.lambda` renames the binder, so
`Lower.constToFix` transports a wrapper to a renamed one; with the arm pinned to `.anon` this
target would have no derivation at all. -/
theorem lowerfix_fixEta_renamed :
    Lower specEnv bs[0]! (.lambda (.named "z") (.app (.fix defs 0) (.bvar 0))) :=
  .fixEta lowerfix_nv.hb lowerfix_nv.hb' lowerfix_nv.hd lowerfix_nv.hnd lowerfix_nv.hids
    lowerfix_nv.hilen lowerfix_nv.hfresh lowerfix_nv.hrarg lowerfix_nv.hdecl lowerfix_nv.hfl
    lowerfix_nv.hlow lowerfix_nv.hcl rfl (by decide)

/-- And the `lambda` congruence arm does not reach it: member 0's body is `λx. □`, and `□`
lowers to `□` alone. So a pinned arm leaves `Lower.constToFix` false at this very pair. -/
theorem lowerfix_fixEta_not_by_lambda :
    ¬ Lower specEnv .box (.app (.fix defs 0) (.bvar 0)) :=
  fun h => LBTerm.noConfusion (Lower.source_box h rfl)

/-- (ii) Member 1's fix unfolding, through `LowerBlock.substList_fixSubst`: the block
substitution undoes `mkDef`'s closing and installs member 0's node at the call site. -/
theorem lowerfix_unfold₁ :
    LBTerm.substList (LBTerm.fixSubst defs)
        (closeFix ids 0 (.lambda (.named "x") (.app (.fvar ids[0]!) (.bvar 0))))
      = .lambda (.named "x") (.app (.fix defs 0) (.bvar 0)) := by
  have hcl : LBClosed (LBTerm.lambda (.named "x") (.app (.fvar ids[0]!) (.bvar 0))) 0 :=
    ⟨trivial, Nat.zero_lt_one⟩
  rw [lowerfix_nv.substList_fixSubst closedBodies_specEnv hcl]
  rfl

/-- (ii) The emitted environment's δ step reaches the block. -/
theorem lowerfix_delta : WcbvEval targetEnv eraseFlags (.const kn₁) (.fix defs 1) :=
  .delta rfl (.fix_atom defs 1)

/-- (ii) The source side of one application step: `bs[1] □ ⇓ □`, through member 0. -/
theorem lowerfix_source_step : WcbvEval specEnv eraseFlags (.app bs[1]! .box) .box := by
  refine .beta (.lam (.named "x") _) .box ?_
  show WcbvEval specEnv eraseFlags (.app (.const kn₀) .box) .box
  exact .beta (.delta rfl (.lam (.named "x") .box)) .box .box

/-- (ii) The target side: two `fix_guarded` links — member 1's unfolding installs member
0's node, which unfolds in turn. -/
theorem lowerfix_target_step :
    WcbvEval targetEnv eraseFlags (.app (.fix defs 1) .box) .box := by
  refine .fix_guarded (argsv := []) rfl (.fix_atom defs 1) .box rfl rfl ?_
  show WcbvEval targetEnv eraseFlags
    (.app (.lambda (.named "x") (.app (.fix defs 0) (.bvar 0))) .box) .box
  refine .beta (.lam (.named "x") _) .box ?_
  show WcbvEval targetEnv eraseFlags (.app (.fix defs 0) .box) .box
  refine .fix_guarded (argsv := []) rfl (.fix_atom defs 0) .box rfl rfl ?_
  show WcbvEval targetEnv eraseFlags (.app (.lambda (.named "x") .box) .box) .box
  exact .beta (.lam (.named "x") .box) .box .box

/-- (ii) **One application step through the block**, in the shape of the pass-correctness
statement: whatever the source application evaluates to, the target application evaluates
to a `Lower`-image of it. -/
theorem lowerfix_app_step {v : LBTerm}
    (hev : WcbvEval specEnv eraseFlags (.app bs[1]! .box) v) :
    ∃ v', Lower specEnv v v' ∧ WcbvEval targetEnv eraseFlags (.app (.fix defs 1) .box) v' := by
  rw [eval_deterministic hev lowerfix_source_step]
  exact ⟨.box, .box, lowerfix_target_step⟩

/-- (iii) `isLambda bs[1]! = true`, discharged through `LowerBlock.lambda_of_fixLambda`. -/
theorem lowerfix_isLambda : isLambda bs[1]! = true :=
  lowerfix_nv.lambda_of_fixLambda 1 (Nat.lt_succ_self 1)

/-- The source environment behind the stateability witness: one constant, `name₀`. -/
def srcEnv : VEnv where
  constants n := if n = name₀ then some ⟨0, .sort .zero⟩ else none
  defeqs _ := False
  pats _ _ := False

/-- (iv) **Stateability.** `ErasesLBFix` is inhabited on the fixture, at exactly the pair
no factor of `Erases ⨟ Lower` relates: the source constant `lfA` against the fixvar
`ids[0]` the eraser emits for it inside the block. -/
theorem lowerfix_erasesLBFix (Us : List Name) (us : List Lean.Level) :
    ErasesLBFix srcEnv Us specEnv kns ids [] (.const name₀ us) (.fvar ids[0]!) :=
  ⟨.const kn₀, .const kn₀,
    .const (ci := ⟨0, .sort .zero⟩) rfl
      (ConstOrigin.of_axiom (A := .sort .zero) ⟨.succ .zero, VEnv.HasType.sort trivial⟩ rfl),
    .const (not_runtimeKey decl₀), .hit (j := 0) rfl rfl⟩

/-- **`fixConst` fires under its new guard.** The fixture's first member is a definition,
so it is not a runtime key, and its constant relates to the block's `.fix` node. -/
theorem lowerfix_fixConst_fires : Lower specEnv (.const kn₀) (.fix defs 0) :=
  Lower.fixConst' lowerfix_nv (not_runtimeKey decl₀) (by rfl)

/-! ### The refutation

The design's `Lower.constToFix` is false as written; this is the counterexample, on the
`LowerBlock` built here. -/

/-- **`Lower.constToFix` is false without `hfv`.** At `t = t' = s = .fvar ids[0]` every
premise of the design's statement holds — including `LBClosed t 0`, which says nothing
about free variables, and `ClosedBodies Γ` — while the conclusion asks for
`Lower Γ (.fvar ids[0]) (.fix defs 0)`, which no arm derives: the only value-side fix arm
demands a declared specification body, and no body in `specEnv` is a free variable. -/
theorem constToFix_needs_freshness :
    ¬ (∀ (Γ : GlobalDeclarations) (kns : List Kername) (bs bs' : List LBTerm)
         (ids : List FVarId) (defs : List (@FixDef LBTerm)) (s t t' : LBTerm),
        ClosedBodies Γ → LowerBlock Γ kns bs bs' ids defs → LBClosed t 0 →
        Lower Γ s t → ConstToFVar kns ids t t' → Lower Γ s (substFix ids defs t')) := by
  intro hall
  have h := hall specEnv kns bs bs ids defs (.fvar ids[0]!) (.fvar ids[0]!) (.fvar ids[0]!)
    closedBodies_specEnv lowerfix_nv trivial (.fvar _) (.fvar _)
  rw [show substFix ids defs (.fvar ids[0]!) = .fix defs 0 from rfl] at h
  obtain ⟨kns₂, bs₂, bs₂', ids₂, hblk₂, hcase⟩ := Lower.target_fix h rfl
  rcases hcase with ⟨kn, hkn, _⟩ | ⟨hj, _⟩
  · exact LBTerm.noConfusion hkn
  · obtain ⟨hj0, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have hd := hblk₂.hdecl 0 (by rw [← hblk₂.hb]; exact hj0)
    rw [hjeq] at hd
    obtain ⟨nm, u, he⟩ := specEnv_body hd
    exact LBTerm.noConfusion he

end LowerFixFixture

/-- The naive transport of box-freedom along `Lower` is false: `Lower.fixConst` relates
the box-free `.const kn` to the block's `.fix`, whose definitions carry the boxes of the
members' bodies. Any transport needs a premise excluding a `.fix` in the target. It lives
here rather than beside `NoBox` in `Lower.lean` because its witness is the fixture above. -/
theorem noBox_lower_needs_noFix :
    ¬ (∀ (Γ : GlobalDeclarations) (s t : LBTerm), Lower Γ s t → NoBox s → NoBox t) := by
  intro H
  exact H LowerFixFixture.specEnv (.const LowerFixFixture.kn₀)
    (.fix LowerFixFixture.defs 0)
    (Lower.fixConst' LowerFixFixture.lowerfix_nv
      (LowerFixFixture.not_runtimeKey LowerFixFixture.decl₀) (by rfl)) trivial |>.1

end LeanToLambdaBox
