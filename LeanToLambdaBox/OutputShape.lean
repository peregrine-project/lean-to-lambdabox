import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract

/-!
# Output-shape metatheory for λ□ terms

The two shape predicates the erasure's output is described by, and how the
binder-closing operation `toBvar` acts on them.

* `NoFix t` — `t` carries no `.fix` node. The shipping `visitExpr` never emits one; only
  the environment-level `visitMutual` does.
* `NoBlock t` — `t` carries no *nonempty* `.construct` node, i.e. every constructor
  application is in applied (spine) form rather than block form.

Both are defined by the same mutual recursion as `LBClosed`, with the per-list traversals
factored into helpers (`NoFixAlts`, `NoBlockAlts`, `NoBlockDefs`) because the nested-list
occurrence defeats the structural-recursion checker in `∀ a ∈ alts, NoFix a.2` form;
`NoFix_case`/`NoFixAlts_iff` and their `NoBlock` counterparts expose exactly that form.

The binder-closing lemmas follow: `toBvar` preserves both predicates, and it takes a body
closed at level `k` to one closed at `k + 1` (`Closed.lean`). Every binder case of an
induction over the erasure family's results goes through `Erasure.mkLambda`/`mkLetIn`/
`mkAlt`/`mkDef`, i.e. through `toBvar`, so the fold forms for the multi-binder closings
(`mkAlt` over an alternative's fields, `mkDef` over a mutual block's fixpoint variables,
which apply `toBvar` at levels `0, 1, 2, …` in turn) are here too.

Pure `LBTerm` facts throughout — no lean4lean, and no dependence on `ErasureRun`.
-/

namespace LeanToLambdaBox

open Lean

/-! ## The shape predicates -/

/-! ### `NoFix`

`.construct` is opaque (`True`): applied-form constructor spines carry their arguments
through `.app`, so `NoFix` reaches them by the `.app` recursion rather than through the
(always-empty) `.construct` node. `.case` and `.proj` are **not** opaque: a `.fix` hidden
under either would satisfy the predicate and then take a fix-unfolding step. -/
mutual
/-- `t` contains no `.fix` node in relevant (spine) position. -/
def NoFix : LBTerm → Prop
  | .lambda _ b => NoFix b
  | .letIn _ v b => NoFix v ∧ NoFix b
  | .app f a => NoFix f ∧ NoFix a
  | .case _ d alts => NoFix d ∧ NoFixAlts alts
  | .fix _ _ => False
  | .box => True
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .construct _ _ _ => True
  | .proj _ e => NoFix e
  | .prim _ => True

/-- `NoFix` over `case` alternatives (each branch body is `NoFix`). -/
def NoFixAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoFix b ∧ NoFixAlts rest
end

/-- `NoFixAlts` in the natural per-element form. -/
theorem NoFixAlts_iff (l : List (List BinderName × LBTerm)) :
    NoFixAlts l ↔ ∀ a ∈ l, NoFix a.2 := by
  induction l with
  | nil => simp [NoFixAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoFixAlts, ih]

@[simp] theorem NoFix_box : NoFix .box := trivial
@[simp] theorem NoFix_bvar (i : Nat) : NoFix (.bvar i) := trivial
@[simp] theorem NoFix_fvar (x : FVarId) : NoFix (.fvar x) := trivial
@[simp] theorem NoFix_const (kn : Kername) : NoFix (.const kn) := trivial
@[simp] theorem NoFix_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    NoFix (.construct iid c args) := trivial
@[simp] theorem NoFix_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoFix (.fix defs i) ↔ False := Iff.rfl
@[simp] theorem NoFix_lambda (n : BinderName) (b : LBTerm) :
    NoFix (.lambda n b) ↔ NoFix b := Iff.rfl
@[simp] theorem NoFix_letIn (n : BinderName) (v b : LBTerm) :
    NoFix (.letIn n v b) ↔ NoFix v ∧ NoFix b := Iff.rfl
@[simp] theorem NoFix_app (f a : LBTerm) :
    NoFix (.app f a) ↔ NoFix f ∧ NoFix a := Iff.rfl
@[simp] theorem NoFix_case (info : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoFix (.case info d alts) ↔ NoFix d ∧ ∀ a ∈ alts, NoFix a.2 := by
  show NoFix d ∧ NoFixAlts alts ↔ _
  rw [NoFixAlts_iff]
@[simp] theorem NoFix_proj (p : ProjectionInfo) (e : LBTerm) :
    NoFix (.proj p e) ↔ NoFix e := Iff.rfl
@[simp] theorem NoFix_prim (p : PrimVal) : NoFix (.prim p) := trivial

/-! ### `NoBlock`

`.fix` is **not** opaque — an unfolding substitutes the block's own `.fix` nodes into the
body, so carrying `NoBlock` through an unfolding needs the bodies' clause. -/
mutual
/-- `t` contains no *nonempty* block-constructor node: every constructor application is in
applied (spine) form. -/
def NoBlock : LBTerm → Prop
  | .lambda _ b => NoBlock b
  | .letIn _ v b => NoBlock v ∧ NoBlock b
  | .app f a => NoBlock f ∧ NoBlock a
  | .case _ d alts => NoBlock d ∧ NoBlockAlts alts
  | .fix defs _ => NoBlockDefs defs
  | .construct _ _ [] => True
  | .construct _ _ (_ :: _) => False
  | .box => True
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .proj _ e => NoBlock e
  | .prim _ => True

/-- `NoBlock` over `case` alternatives (each branch body is `NoBlock`). -/
def NoBlockAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoBlock b ∧ NoBlockAlts rest

/-- `NoBlock` over `fix` definitions (each definition body is `NoBlock`). -/
def NoBlockDefs : List (@FixDef LBTerm) → Prop
  | [] => True
  | fd :: rest => NoBlock fd.body ∧ NoBlockDefs rest
end

/-- `NoBlockAlts` in the natural per-element form. -/
theorem NoBlockAlts_iff (l : List (List BinderName × LBTerm)) :
    NoBlockAlts l ↔ ∀ a ∈ l, NoBlock a.2 := by
  induction l with
  | nil => simp [NoBlockAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoBlockAlts, ih]

/-- `NoBlockDefs` in the natural per-element form. -/
theorem NoBlockDefs_iff (l : List (@FixDef LBTerm)) :
    NoBlockDefs l ↔ ∀ d ∈ l, NoBlock d.body := by
  induction l with
  | nil => simp [NoBlockDefs]
  | cons fd rest ih => simp [NoBlockDefs, ih]

@[simp] theorem NoBlock_box : NoBlock .box := trivial
@[simp] theorem NoBlock_bvar (i : Nat) : NoBlock (.bvar i) := trivial
@[simp] theorem NoBlock_fvar (x : FVarId) : NoBlock (.fvar x) := trivial
@[simp] theorem NoBlock_const (kn : Kername) : NoBlock (.const kn) := trivial
@[simp] theorem NoBlock_construct_nil (iid : InductiveId) (c : Nat) :
    NoBlock (.construct iid c []) := trivial
@[simp] theorem NoBlock_lambda (n : BinderName) (b : LBTerm) :
    NoBlock (.lambda n b) ↔ NoBlock b := Iff.rfl
@[simp] theorem NoBlock_letIn (n : BinderName) (v b : LBTerm) :
    NoBlock (.letIn n v b) ↔ NoBlock v ∧ NoBlock b := Iff.rfl
@[simp] theorem NoBlock_app (f a : LBTerm) :
    NoBlock (.app f a) ↔ NoBlock f ∧ NoBlock a := Iff.rfl
@[simp] theorem NoBlock_case (info : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoBlock (.case info d alts) ↔ NoBlock d ∧ ∀ a ∈ alts, NoBlock a.2 := by
  show NoBlock d ∧ NoBlockAlts alts ↔ _
  rw [NoBlockAlts_iff]
@[simp] theorem NoBlock_proj (p : ProjectionInfo) (e : LBTerm) :
    NoBlock (.proj p e) ↔ NoBlock e := Iff.rfl
@[simp] theorem NoBlock_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoBlock (.fix defs i) ↔ ∀ d ∈ defs, NoBlock d.body := by
  show NoBlockDefs defs ↔ _
  rw [NoBlockDefs_iff]
@[simp] theorem NoBlock_prim (p : PrimVal) : NoBlock (.prim p) := trivial

/-! ### The panic fall-through's output

Every destructuring helper and every `unreachable!` arm of the erasure family `panic!`s,
and a panic *succeeds* at `EraseM`, returning `default : LBTerm`
(`Erasure.run_panicWithPosWithDecl`). `default` is `.box`, which is fix-free and closed at
every level, so the shape induction's panic arms are **discharged**, not refuted — the
honest reading of code whose "impossible" branches are reachable in the model. -/

@[simp] theorem noFix_default : NoFix (default : LBTerm) := trivial

@[simp] theorem lbClosed_default (k : Nat) : LBClosed (default : LBTerm) k := trivial

/-- `default = .box`, and boxing is invisible to `NoBlock` — the predicate forbids exactly
one node, a `.construct` with a non-empty argument list. So the panic arms are discharged
for the third output conjunct too. -/
@[simp] theorem noBlock_default : NoBlock (default : LBTerm) := trivial

theorem noFix_toBvar {t : LBTerm} (x : FVarId) :
    ∀ (lvl : Nat), NoFix t → NoFix (toBvar x lvl t) := by
  induction t using LBTerm.recData with
  | hbox => intro lvl _; simp [toBvar]
  | hbvar i => intro lvl _; simp [toBvar]
  | hfvar y => intro lvl _; simp [toBvar]; split <;> simp
  | hconst kn => intro lvl _; simp [toBvar]
  | hprim p => intro lvl _; simp [toBvar]
  | hlam nm b ih => intro lvl h; simpa [toBvar] using ih (lvl + 1) h
  | hletIn nm v b ihv ihb =>
    intro lvl h
    obtain ⟨hv, hb⟩ := h
    exact ⟨ihv lvl hv, ihb (lvl + 1) hb⟩
  | happ f a ihf iha =>
    intro lvl h
    obtain ⟨hf, ha⟩ := h
    exact ⟨ihf lvl hf, iha lvl ha⟩
  | hconstruct iid k args ih => intro lvl _; simp [toBvar]
  | hcase info discr alts ihd iha =>
    intro lvl h
    obtain ⟨hd, ha⟩ := h
    rw [NoFixAlts_iff] at ha
    refine ⟨ihd lvl hd, ?_⟩
    rw [toBvarAlts_eq_map, NoFixAlts_iff]
    intro a hmem
    simp only [List.mem_map] at hmem
    obtain ⟨a', hmem', rfl⟩ := hmem
    exact iha a' hmem' (lvl + a'.1.length) (ha a' hmem')
  | hproj p e ih => intro lvl h; simpa [toBvar] using ih lvl h
  | hfix defs i ih => intro lvl h; exact absurd h (by simp)

/-- **`toBvar` preserves applied form.** The `NoBlock` counterpart of `noFix_toBvar`.

Routine, and for a structural reason: `toBvar` maps `.construct iid n args` to
`.construct iid n (toBvarArgs x lvl args)`, and `toBvarArgs` preserves list emptiness —
so the one node `NoBlock` forbids is neither created nor destroyed. -/
theorem noBlock_toBvar {t : LBTerm} (x : FVarId) :
    ∀ (lvl : Nat), NoBlock t → NoBlock (toBvar x lvl t) := by
  induction t using LBTerm.recData with
  | hbvar i => intro lvl _; simp [toBvar]
  | hfvar y => intro lvl _; simp only [toBvar]; split <;> trivial
  | hlam nm b ih => intro lvl h; exact ih (lvl + 1) h
  | hletIn nm v b ihv ihb => intro lvl h; exact ⟨ihv lvl h.1, ihb (lvl + 1) h.2⟩
  | happ f a ihf iha => intro lvl h; exact ⟨ihf lvl h.1, iha lvl h.2⟩
  | hconstruct iid c args ih =>
    intro lvl h
    cases args with
    | nil => simp only [toBvar, toBvarArgs]; trivial
    | cons a as => exact absurd h (by simp [NoBlock])
  | hcase info discr alts ihd iha =>
    intro lvl h
    rw [NoBlock_case] at h
    obtain ⟨iid, np⟩ := info
    simp only [toBvar, NoBlock_case, toBvarAlts_eq_map]
    refine ⟨ihd lvl h.1, fun a ha => ?_⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact iha b hb (lvl + b.1.length) (h.2 b hb)
  | hproj p e ih => intro lvl h; exact ih lvl h
  | hfix defs i ih =>
    intro lvl h
    rw [NoBlock_fix] at h
    simp only [toBvar, NoBlock_fix, toBvarDefs_eq_map]
    intro fd hfd
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfd
    exact ih d hd (lvl + defs.length) (h d hd)
  | _ => intro lvl _; trivial

/-! ### The binder-closing folds

`Erasure.mkAlt` and `Erasure.mkDef` close a body over several free variables at once, by
folding `toBvar` at successive levels (`for (x, i) in xs.reverse.zipIdx do body :=
toBvar x i body`). These are the fold forms of the two lemmas above. -/

theorem noFix_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm}, NoFix t →
      NoFix (L.foldl (fun b p => toBvar p.1 p.2 b) t)
  | [], _, h => h
  | p :: rest, _, h => noFix_foldl_toBvar rest (noFix_toBvar p.1 p.2 h)

theorem noBlock_foldl_toBvar :
    ∀ (L : List (FVarId × Nat)) {t : LBTerm}, NoBlock t →
      NoBlock (L.foldl (fun b p => toBvar p.1 p.2 b) t)
  | [], _, h => h
  | p :: rest, _, h => noBlock_foldl_toBvar rest (noBlock_toBvar p.1 p.2 h)

/-- The `mkDef` instance for applied form: the block-closing fold indexes its binders by
*name* through the reader's fixvar map, exactly as `lbClosed_foldl_zipIdx_map` does. There
is no arithmetic to do here — `NoBlock` carries no level — so the statement is the fold of
`noBlock_toBvar` and nothing else. -/
theorem noBlock_foldl_zipIdx_map {α : Type} {t : LBTerm} (fv : α → FVarId) (xs : List α)
    (h : NoBlock t) :
    NoBlock (xs.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) := by
  have hmap : xs.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t
      = (xs.reverse.zipIdx.map (fun p => (fv p.1, p.2))).foldl
          (fun b q => toBvar q.1 q.2 b) t := by
    rw [List.foldl_map]
  rw [hmap]
  exact noBlock_foldl_toBvar _ h

end LeanToLambdaBox
