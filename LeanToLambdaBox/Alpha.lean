import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.Output
import LeanToLambdaBox.Semantics.Compute
import LeanToLambdaBox.Erases
import LeanToLambdaBox.Witness.SourceTable
import LeanToLambdaBox.SourceEval

/-!
# α-equivalence of λ□ terms, and the transports along it

`LBTerm` carries binder names (`.lambda`, `.letIn`, a `.case` alternative's field binders and
a `.fix` definition's own name). Nothing in the λ□ semantics reads one, and they are not
predictable — a name the frontend's generator mints carries the erasing module and a hygiene
counter — so a hand-transcribed program is pinned to an actual run's output only up to them.

`LBTerm.AlphaEq` is that relation: structural equality with every binder name free. It is
decidable (`LBTerm.alphaBEq`), an equivalence and a congruence, with one introduction and one
inversion lemma per node.

Two things are invariant under it: box-freedom (`NoBox.alpha`) and the constants a term names
(`constRefs.alpha`, hence `ReachableFrom.alpha`). `Lower` is **not**, and `Lower.not_alpha` is
the counterexample: its two `fix` arms read a specification body out of `Γ` by equality.

On the source side, `Expr.AlphaEq` transports through translation (`TrExprS.alpha`, which needs
no renaming of the image — `VExpr` has no binder names), through evaluation (`SEval.alpha`) and
through erasure (`Erases.alpha`), the last landing in a *target* renaming because the `lam` and
`letE` rules copy the source binder name. `Erases.no_anon_lambda` is why the image's own
names admit no transport.
-/
open Lean (FVarId)

deriving instance DecidableEq for ProjectionInfo

namespace LBTerm

/-! ## The decision procedure -/

/-- Structural equality of primitive values. The one `PrimTag` has a `BitVec` model, so this
is that comparison. -/
def primBEq : PrimVal → PrimVal → Bool
  | ⟨.primInt, v⟩, ⟨.primInt, v'⟩ => v == v'

theorem primBEq_iff {p q : PrimVal} : primBEq p q = true ↔ p = q := by
  obtain ⟨tp, vp⟩ := p; obtain ⟨tq, vq⟩ := q
  cases tp; cases tq
  simp [primBEq]

/-! `alphaBEq` and its three list traversals: structural equality of two terms with every
binder name ignored. Hand-rolled list helpers rather than `List.all₂`, for the same reason
`shift` has them — the structural-recursion checker does not see through a combinator for
the nested `List` occurrences of `LBTerm`. -/
mutual
/-- Structural equality up to binder names. -/
def alphaBEq (t u : LBTerm) : Bool :=
  match t, u with
  | .box, .box => true
  | .bvar i, .bvar j => i == j
  | .fvar x, .fvar y => x.name == y.name
  | .lambda _ b, .lambda _ b' => alphaBEq b b'
  | .letIn _ v b, .letIn _ v' b' => alphaBEq v v' && alphaBEq b b'
  | .app f a, .app f' a' => alphaBEq f f' && alphaBEq a a'
  | .const kn, .const kn' => Kername.beq kn kn'
  | .construct iid k args, .construct iid' k' args' =>
      iid == iid' && k == k' && alphaBEqArgs args args'
  | .case ip d alts, .case ip' d' alts' =>
      ip == ip' && alphaBEq d d' && alphaBEqAlts alts alts'
  | .proj p e, .proj p' e' => p == p' && alphaBEq e e'
  | .fix defs i, .fix defs' i' => i == i' && alphaBEqDefs defs defs'
  | .prim p, .prim p' => primBEq p p'
  | _, _ => false
termination_by structural t

/-- `alphaBEq` over a block constructor's arguments. -/
def alphaBEqArgs (l l' : List LBTerm) : Bool :=
  match l, l' with
  | [], [] => true
  | t :: ts, t' :: ts' => alphaBEq t t' && alphaBEqArgs ts ts'
  | _, _ => false
termination_by structural l

/-- `alphaBEq` over `case` alternatives: the binder lists are compared by length only. -/
def alphaBEqAlts (l l' : List (List BinderName × LBTerm)) : Bool :=
  match l, l' with
  | [], [] => true
  | (ns, b) :: rest, (ns', b') :: rest' =>
      ns.length == ns'.length && alphaBEq b b' && alphaBEqAlts rest rest'
  | _, _ => false
termination_by structural l

/-- `alphaBEq` over a `fix` block's definitions: the principal argument index is compared,
the definition's own name is not. -/
def alphaBEqDefs (l l' : List (@FixDef LBTerm)) : Bool :=
  match l, l' with
  | [], [] => true
  | d :: ds, d' :: ds' =>
      d.principalArgIdx == d'.principalArgIdx && alphaBEq d.body d'.body &&
        alphaBEqDefs ds ds'
  | _, _ => false
termination_by structural l
end

/-! ## The relation -/

/-- Two λ□ terms are α-equivalent when they differ only in binder names: the names of
`.lambda` and `.letIn` nodes, of a `.case` alternative's field binders (whose *number* is
pinned, being what `iota_red` reads) and of a `.fix` definition. -/
def AlphaEq (t t' : LBTerm) : Prop := alphaBEq t t' = true

/-- α-equivalence pointwise over a list of terms. -/
def AlphaEqs (l l' : List LBTerm) : Prop := alphaBEqArgs l l' = true

/-- α-equivalence pointwise over a list of `case` alternatives. -/
def AlphaEqAlts (l l' : List (List BinderName × LBTerm)) : Prop := alphaBEqAlts l l' = true

/-- α-equivalence pointwise over a `fix` block's definitions. -/
def AlphaEqDefs (l l' : List (@FixDef LBTerm)) : Prop := alphaBEqDefs l l' = true

instance (t t' : LBTerm) : Decidable (AlphaEq t t') := by unfold AlphaEq; infer_instance
instance (l l' : List LBTerm) : Decidable (AlphaEqs l l') := by unfold AlphaEqs; infer_instance
instance (l l' : List (List BinderName × LBTerm)) : Decidable (AlphaEqAlts l l') := by
  unfold AlphaEqAlts; infer_instance
instance (l l' : List (@FixDef LBTerm)) : Decidable (AlphaEqDefs l l') := by
  unfold AlphaEqDefs; infer_instance

/-! ## Introduction: `AlphaEq` is a congruence -/

theorem AlphaEq.box : AlphaEq .box .box := rfl
theorem AlphaEq.bvar {i : Nat} : AlphaEq (.bvar i) (.bvar i) := by simp [AlphaEq, alphaBEq]
theorem AlphaEq.fvar {x : FVarId} : AlphaEq (.fvar x) (.fvar x) := by
  simp [AlphaEq, alphaBEq]
theorem AlphaEq.const {kn : Kername} : AlphaEq (.const kn) (.const kn) := by
  simp [AlphaEq, alphaBEq, LeanToLambdaBox.Kername.beq_self]
theorem AlphaEq.prim {p : PrimVal} : AlphaEq (.prim p) (.prim p) := by
  simp [AlphaEq, alphaBEq, primBEq_iff]

theorem AlphaEq.lambda {n n' : BinderName} {b b' : LBTerm} (h : AlphaEq b b') :
    AlphaEq (.lambda n b) (.lambda n' b') := by simpa [AlphaEq, alphaBEq] using h

theorem AlphaEq.letIn {n n' : BinderName} {v v' b b' : LBTerm}
    (hv : AlphaEq v v') (hb : AlphaEq b b') : AlphaEq (.letIn n v b) (.letIn n' v' b') := by
  simp [AlphaEq, alphaBEq] at hv hb ⊢; exact ⟨hv, hb⟩

theorem AlphaEq.app {f f' a a' : LBTerm} (hf : AlphaEq f f') (ha : AlphaEq a a') :
    AlphaEq (.app f a) (.app f' a') := by
  simp [AlphaEq, alphaBEq] at hf ha ⊢; exact ⟨hf, ha⟩

theorem AlphaEq.construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
    (h : AlphaEqs args args') : AlphaEq (.construct iid k args) (.construct iid k args') := by
  simp [AlphaEq, AlphaEqs, alphaBEq] at h ⊢; exact h

theorem AlphaEq.case {ip : InductiveId × Nat} {d d' : LBTerm}
    {alts alts' : List (List BinderName × LBTerm)} (hd : AlphaEq d d')
    (ha : AlphaEqAlts alts alts') : AlphaEq (.case ip d alts) (.case ip d' alts') := by
  simp [AlphaEq, AlphaEqAlts, alphaBEq] at hd ha ⊢; exact ⟨hd, ha⟩

theorem AlphaEq.proj {p : ProjectionInfo} {e e' : LBTerm} (h : AlphaEq e e') :
    AlphaEq (.proj p e) (.proj p e') := by
  simp [AlphaEq, alphaBEq] at h ⊢; exact h

theorem AlphaEq.fix {defs defs' : List (@FixDef LBTerm)} {i : Nat} (h : AlphaEqDefs defs defs') :
    AlphaEq (.fix defs i) (.fix defs' i) := by
  simp [AlphaEq, AlphaEqDefs, alphaBEq] at h ⊢; exact h

theorem AlphaEqs.nil : AlphaEqs [] [] := rfl

theorem AlphaEqs.cons {t t' : LBTerm} {l l' : List LBTerm} (h : AlphaEq t t')
    (hl : AlphaEqs l l') : AlphaEqs (t :: l) (t' :: l') := by
  simp [AlphaEqs, AlphaEq, alphaBEqArgs] at h hl ⊢; exact ⟨h, hl⟩

theorem AlphaEqAlts.nil : AlphaEqAlts [] [] := rfl

theorem AlphaEqAlts.cons {ns ns' : List BinderName} {b b' : LBTerm}
    {l l' : List (List BinderName × LBTerm)} (hn : ns.length = ns'.length) (h : AlphaEq b b')
    (hl : AlphaEqAlts l l') : AlphaEqAlts ((ns, b) :: l) ((ns', b') :: l') := by
  simp [AlphaEqAlts, AlphaEq, alphaBEqAlts] at h hl ⊢; exact ⟨⟨hn, h⟩, hl⟩

theorem AlphaEqDefs.nil : AlphaEqDefs [] [] := rfl

theorem AlphaEqDefs.cons {d d' : @FixDef LBTerm} {l l' : List (@FixDef LBTerm)}
    (hr : d.principalArgIdx = d'.principalArgIdx) (h : AlphaEq d.body d'.body)
    (hl : AlphaEqDefs l l') : AlphaEqDefs (d :: l) (d' :: l') := by
  simp [AlphaEqDefs, AlphaEq, alphaBEqDefs] at h hl ⊢; exact ⟨⟨hr, h⟩, hl⟩

/-! ## Inversion: one lemma per head -/

theorem AlphaEq.box_inv {u : LBTerm} (h : AlphaEq .box u) : u = .box := by
  cases u <;> simp [AlphaEq, alphaBEq] at h ⊢

theorem AlphaEq.bvar_inv {i : Nat} {u : LBTerm} (h : AlphaEq (.bvar i) u) : u = .bvar i := by
  cases u <;> simp [AlphaEq, alphaBEq] at h ⊢
  exact h.symm

theorem AlphaEq.fvar_inv {x : FVarId} {u : LBTerm} (h : AlphaEq (.fvar x) u) : u = .fvar x := by
  cases u <;> simp [AlphaEq, alphaBEq] at h ⊢
  exact congrArg Lean.FVarId.mk h.symm

theorem AlphaEq.const_inv {kn : Kername} {u : LBTerm} (h : AlphaEq (.const kn) u) :
    u = .const kn := by
  cases u <;> simp [AlphaEq, alphaBEq] at h ⊢
  exact (LeanToLambdaBox.Kername.beq_iff.mp h).symm

theorem AlphaEq.prim_inv {p : PrimVal} {u : LBTerm} (h : AlphaEq (.prim p) u) : u = .prim p := by
  cases u <;> simp [AlphaEq, alphaBEq] at h ⊢
  exact (primBEq_iff.mp h).symm

theorem AlphaEq.lambda_inv {n : BinderName} {b u : LBTerm} (h : AlphaEq (.lambda n b) u) :
    ∃ n' b', u = .lambda n' b' ∧ AlphaEq b b' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  exact ⟨_, _, rfl, h⟩

theorem AlphaEq.letIn_inv {n : BinderName} {v b u : LBTerm} (h : AlphaEq (.letIn n v b) u) :
    ∃ n' v' b', u = .letIn n' v' b' ∧ AlphaEq v v' ∧ AlphaEq b b' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  exact ⟨_, _, _, rfl, h.1, h.2⟩

theorem AlphaEq.app_inv {f a u : LBTerm} (h : AlphaEq (.app f a) u) :
    ∃ f' a', u = .app f' a' ∧ AlphaEq f f' ∧ AlphaEq a a' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem AlphaEq.construct_inv {iid : InductiveId} {k : Nat} {args : List LBTerm} {u : LBTerm}
    (h : AlphaEq (.construct iid k args) u) :
    ∃ args', u = .construct iid k args' ∧ AlphaEqs args args' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  obtain ⟨⟨hi, hk⟩, ha⟩ := h
  exact ⟨_, by rw [hi, hk], ha⟩

theorem AlphaEq.case_inv {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} {u : LBTerm} (h : AlphaEq (.case ip d alts) u) :
    ∃ d' alts', u = .case ip d' alts' ∧ AlphaEq d d' ∧ AlphaEqAlts alts alts' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  obtain ⟨⟨hi, hd⟩, ha⟩ := h
  exact ⟨_, _, by rw [hi], hd, ha⟩

theorem AlphaEq.proj_inv {p : ProjectionInfo} {e u : LBTerm} (h : AlphaEq (.proj p e) u) :
    ∃ e', u = .proj p e' ∧ AlphaEq e e' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  obtain ⟨hp, he⟩ := h
  exact ⟨_, by rw [hp], he⟩

theorem AlphaEq.fix_inv {defs : List (@FixDef LBTerm)} {i : Nat} {u : LBTerm}
    (h : AlphaEq (.fix defs i) u) :
    ∃ defs', u = .fix defs' i ∧ AlphaEqDefs defs defs' := by
  cases u <;> simp [AlphaEq, alphaBEq] at h
  obtain ⟨hi, hd⟩ := h
  exact ⟨_, by rw [hi], hd⟩

theorem AlphaEqs.nil_inv {l : List LBTerm} (h : AlphaEqs [] l) : l = [] := by
  cases l <;> simp [AlphaEqs, alphaBEqArgs] at h ⊢

theorem AlphaEqs.cons_inv {t : LBTerm} {l m : List LBTerm} (h : AlphaEqs (t :: l) m) :
    ∃ t' m', m = t' :: m' ∧ AlphaEq t t' ∧ AlphaEqs l m' := by
  cases m <;> simp [AlphaEqs, alphaBEqArgs] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem AlphaEqAlts.nil_inv {l : List (List BinderName × LBTerm)} (h : AlphaEqAlts [] l) :
    l = [] := by cases l <;> simp [AlphaEqAlts, alphaBEqAlts] at h ⊢

theorem AlphaEqAlts.cons_inv {ns : List BinderName} {b : LBTerm}
    {l m : List (List BinderName × LBTerm)} (h : AlphaEqAlts ((ns, b) :: l) m) :
    ∃ ns' b' m', m = (ns', b') :: m' ∧ ns.length = ns'.length ∧ AlphaEq b b' ∧
      AlphaEqAlts l m' := by
  cases m <;> simp [AlphaEqAlts, alphaBEqAlts] at h
  exact ⟨_, _, _, rfl, h.1.1, h.1.2, h.2⟩

theorem AlphaEqDefs.nil_inv {l : List (@FixDef LBTerm)} (h : AlphaEqDefs [] l) : l = [] := by
  cases l <;> simp [AlphaEqDefs, alphaBEqDefs] at h ⊢

theorem AlphaEqDefs.cons_inv {d : @FixDef LBTerm} {l m : List (@FixDef LBTerm)}
    (h : AlphaEqDefs (d :: l) m) :
    ∃ d' m', m = d' :: m' ∧ d.principalArgIdx = d'.principalArgIdx ∧
      AlphaEq d.body d'.body ∧ AlphaEqDefs l m' := by
  cases m <;> simp [AlphaEqDefs, alphaBEqDefs] at h
  exact ⟨_, _, rfl, h.1.1, h.1.2, h.2⟩

/-! ## An equivalence relation

Each of the three laws is one `LBTerm.recData` induction, whose list arms hand back
membership induction hypotheses; the `_aux` lemmas are those arms.
-/

theorem AlphaEqs.of_mem : ∀ {l : List LBTerm}, (∀ x ∈ l, AlphaEq x x) → AlphaEqs l l
  | [], _ => AlphaEqs.nil
  | _ :: ts, h =>
    AlphaEqs.cons (h _ (List.mem_cons_self ..))
      (AlphaEqs.of_mem (l := ts) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem AlphaEqAlts.of_mem : ∀ {l : List (List BinderName × LBTerm)},
    (∀ a ∈ l, AlphaEq a.2 a.2) → AlphaEqAlts l l
  | [], _ => AlphaEqAlts.nil
  | (_, _) :: rest, h =>
    AlphaEqAlts.cons rfl (h _ (List.mem_cons_self ..))
      (AlphaEqAlts.of_mem (l := rest) fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem AlphaEqDefs.of_mem : ∀ {l : List (@FixDef LBTerm)},
    (∀ d ∈ l, AlphaEq d.body d.body) → AlphaEqDefs l l
  | [], _ => AlphaEqDefs.nil
  | _ :: rest, h =>
    AlphaEqDefs.cons rfl (h _ (List.mem_cons_self ..))
      (AlphaEqDefs.of_mem (l := rest) fun d hd => h d (List.mem_cons_of_mem _ hd))

@[refl] theorem AlphaEq.refl (t : LBTerm) : AlphaEq t t := by
  induction t using LBTerm.recData with
  | hbox => exact AlphaEq.box
  | hbvar => exact AlphaEq.bvar
  | hfvar => exact AlphaEq.fvar
  | hconst => exact AlphaEq.const
  | hprim => exact AlphaEq.prim
  | hlam _ _ ih => exact AlphaEq.lambda ih
  | hletIn _ _ _ ihv ihb => exact AlphaEq.letIn ihv ihb
  | happ _ _ ihf iha => exact AlphaEq.app ihf iha
  | hproj _ _ ih => exact AlphaEq.proj ih
  | hconstruct _ _ _ ih => exact AlphaEq.construct (AlphaEqs.of_mem ih)
  | hcase _ _ _ ihd iha => exact AlphaEq.case ihd (AlphaEqAlts.of_mem iha)
  | hfix _ _ ih => exact AlphaEq.fix (AlphaEqDefs.of_mem ih)

theorem AlphaEqs.refl (l : List LBTerm) : AlphaEqs l l :=
  AlphaEqs.of_mem fun x _ => AlphaEq.refl x

theorem AlphaEqs.symm_aux : ∀ {l m : List LBTerm},
    (∀ x ∈ l, ∀ u, AlphaEq x u → AlphaEq u x) → AlphaEqs l m → AlphaEqs m l
  | [], _, _, h => by rw [AlphaEqs.nil_inv h]; exact AlphaEqs.nil
  | _ :: ts, _, ih, h => by
    obtain ⟨_, _, rfl, ht, hts⟩ := AlphaEqs.cons_inv h
    exact AlphaEqs.cons (ih _ (List.mem_cons_self ..) _ ht)
      (AlphaEqs.symm_aux (l := ts) (fun x hx => ih x (List.mem_cons_of_mem _ hx)) hts)

theorem AlphaEqAlts.symm_aux : ∀ {l m : List (List BinderName × LBTerm)},
    (∀ a ∈ l, ∀ u, AlphaEq a.2 u → AlphaEq u a.2) → AlphaEqAlts l m → AlphaEqAlts m l
  | [], _, _, h => by rw [AlphaEqAlts.nil_inv h]; exact AlphaEqAlts.nil
  | (_, _) :: rest, _, ih, h => by
    obtain ⟨_, _, _, rfl, hn, hb, hr⟩ := AlphaEqAlts.cons_inv h
    exact AlphaEqAlts.cons hn.symm (ih _ (List.mem_cons_self ..) _ hb)
      (AlphaEqAlts.symm_aux (l := rest) (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hr)

theorem AlphaEqDefs.symm_aux : ∀ {l m : List (@FixDef LBTerm)},
    (∀ d ∈ l, ∀ u, AlphaEq d.body u → AlphaEq u d.body) → AlphaEqDefs l m → AlphaEqDefs m l
  | [], _, _, h => by rw [AlphaEqDefs.nil_inv h]; exact AlphaEqDefs.nil
  | _ :: rest, _, ih, h => by
    obtain ⟨_, _, rfl, hr, hb, hd⟩ := AlphaEqDefs.cons_inv h
    exact AlphaEqDefs.cons hr.symm (ih _ (List.mem_cons_self ..) _ hb)
      (AlphaEqDefs.symm_aux (l := rest) (fun d hd' => ih d (List.mem_cons_of_mem _ hd')) hd)


theorem AlphaEq.symm {t u : LBTerm} (h : AlphaEq t u) : AlphaEq u t := by
  revert u
  induction t using LBTerm.recData with
  | hbox => intro u h; rw [AlphaEq.box_inv h]
  | hbvar => intro u h; rw [AlphaEq.bvar_inv h]
  | hfvar => intro u h; rw [AlphaEq.fvar_inv h]
  | hconst => intro u h; rw [AlphaEq.const_inv h]
  | hprim => intro u h; rw [AlphaEq.prim_inv h]
  | hlam _ _ ih =>
    intro u h; obtain ⟨_, _, rfl, hb⟩ := AlphaEq.lambda_inv h; exact AlphaEq.lambda (ih hb)
  | hletIn _ _ _ ihv ihb =>
    intro u h; obtain ⟨_, _, _, rfl, hv, hb⟩ := AlphaEq.letIn_inv h
    exact AlphaEq.letIn (ihv hv) (ihb hb)
  | happ _ _ ihf iha =>
    intro u h; obtain ⟨_, _, rfl, hf, ha⟩ := AlphaEq.app_inv h
    exact AlphaEq.app (ihf hf) (iha ha)
  | hproj _ _ ih =>
    intro u h; obtain ⟨_, rfl, he⟩ := AlphaEq.proj_inv h; exact AlphaEq.proj (ih he)
  | hconstruct _ _ _ ih =>
    intro u h; obtain ⟨_, rfl, ha⟩ := AlphaEq.construct_inv h
    exact AlphaEq.construct (AlphaEqs.symm_aux (fun x hx _ hu => ih x hx hu) ha)
  | hcase _ _ _ ihd iha =>
    intro u h; obtain ⟨_, _, rfl, hd, ha⟩ := AlphaEq.case_inv h
    exact AlphaEq.case (ihd hd) (AlphaEqAlts.symm_aux (fun x hx _ hu => iha x hx hu) ha)
  | hfix _ _ ih =>
    intro u h; obtain ⟨_, rfl, hd⟩ := AlphaEq.fix_inv h
    exact AlphaEq.fix (AlphaEqDefs.symm_aux (fun x hx _ hu => ih x hx hu) hd)

theorem AlphaEqs.symm {l m : List LBTerm} (h : AlphaEqs l m) : AlphaEqs m l :=
  AlphaEqs.symm_aux (fun _ _ _ hu => AlphaEq.symm hu) h

theorem AlphaEqAlts.symm {l m : List (List BinderName × LBTerm)} (h : AlphaEqAlts l m) :
    AlphaEqAlts m l := AlphaEqAlts.symm_aux (fun _ _ _ hu => AlphaEq.symm hu) h

theorem AlphaEqDefs.symm {l m : List (@FixDef LBTerm)} (h : AlphaEqDefs l m) :
    AlphaEqDefs m l := AlphaEqDefs.symm_aux (fun _ _ _ hu => AlphaEq.symm hu) h

theorem AlphaEqs.trans_aux : ∀ {l m n : List LBTerm},
    (∀ x ∈ l, ∀ u v, AlphaEq x u → AlphaEq u v → AlphaEq x v) →
    AlphaEqs l m → AlphaEqs m n → AlphaEqs l n
  | [], _, _, _, h1, h2 => by
    subst_vars; rw [AlphaEqs.nil_inv h1] at h2; rw [AlphaEqs.nil_inv h2]; exact AlphaEqs.nil
  | _ :: ts, _, _, ih, h1, h2 => by
    obtain ⟨_, _, rfl, ht, hts⟩ := AlphaEqs.cons_inv h1
    obtain ⟨_, _, rfl, ht', hts'⟩ := AlphaEqs.cons_inv h2
    exact AlphaEqs.cons (ih _ (List.mem_cons_self ..) _ _ ht ht')
      (AlphaEqs.trans_aux (l := ts) (fun x hx => ih x (List.mem_cons_of_mem _ hx)) hts hts')

theorem AlphaEqAlts.trans_aux : ∀ {l m n : List (List BinderName × LBTerm)},
    (∀ a ∈ l, ∀ u v, AlphaEq a.2 u → AlphaEq u v → AlphaEq a.2 v) →
    AlphaEqAlts l m → AlphaEqAlts m n → AlphaEqAlts l n
  | [], _, _, _, h1, h2 => by
    subst_vars; rw [AlphaEqAlts.nil_inv h1] at h2; rw [AlphaEqAlts.nil_inv h2]
    exact AlphaEqAlts.nil
  | (_, _) :: rest, _, _, ih, h1, h2 => by
    obtain ⟨_, _, _, rfl, hn, hb, hr⟩ := AlphaEqAlts.cons_inv h1
    obtain ⟨_, _, _, rfl, hn', hb', hr'⟩ := AlphaEqAlts.cons_inv h2
    exact AlphaEqAlts.cons (hn.trans hn') (ih _ (List.mem_cons_self ..) _ _ hb hb')
      (AlphaEqAlts.trans_aux (l := rest) (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hr hr')

theorem AlphaEqDefs.trans_aux : ∀ {l m n : List (@FixDef LBTerm)},
    (∀ d ∈ l, ∀ u v, AlphaEq d.body u → AlphaEq u v → AlphaEq d.body v) →
    AlphaEqDefs l m → AlphaEqDefs m n → AlphaEqDefs l n
  | [], _, _, _, h1, h2 => by
    subst_vars; rw [AlphaEqDefs.nil_inv h1] at h2; rw [AlphaEqDefs.nil_inv h2]
    exact AlphaEqDefs.nil
  | _ :: rest, _, _, ih, h1, h2 => by
    obtain ⟨_, _, rfl, hr, hb, hd⟩ := AlphaEqDefs.cons_inv h1
    obtain ⟨_, _, rfl, hr', hb', hd'⟩ := AlphaEqDefs.cons_inv h2
    exact AlphaEqDefs.cons (hr.trans hr') (ih _ (List.mem_cons_self ..) _ _ hb hb')
      (AlphaEqDefs.trans_aux (l := rest) (fun d hd'' => ih d (List.mem_cons_of_mem _ hd'')) hd hd')

theorem AlphaEq.trans {t u v : LBTerm} (h1 : AlphaEq t u) (h2 : AlphaEq u v) : AlphaEq t v := by
  revert u v
  induction t using LBTerm.recData with
  | hbox => intro u v h1 h2; rw [AlphaEq.box_inv h1] at h2; rw [AlphaEq.box_inv h2]
  | hbvar => intro u v h1 h2; rw [AlphaEq.bvar_inv h1] at h2; rw [AlphaEq.bvar_inv h2]
  | hfvar => intro u v h1 h2; rw [AlphaEq.fvar_inv h1] at h2; rw [AlphaEq.fvar_inv h2]
  | hconst => intro u v h1 h2; rw [AlphaEq.const_inv h1] at h2; rw [AlphaEq.const_inv h2]
  | hprim => intro u v h1 h2; rw [AlphaEq.prim_inv h1] at h2; rw [AlphaEq.prim_inv h2]
  | hlam _ _ ih =>
    intro u v h1 h2
    obtain ⟨_, _, rfl, hb⟩ := AlphaEq.lambda_inv h1
    obtain ⟨_, _, rfl, hb'⟩ := AlphaEq.lambda_inv h2
    exact AlphaEq.lambda (ih hb hb')
  | hletIn _ _ _ ihv ihb =>
    intro u v h1 h2
    obtain ⟨_, _, _, rfl, hv, hb⟩ := AlphaEq.letIn_inv h1
    obtain ⟨_, _, _, rfl, hv', hb'⟩ := AlphaEq.letIn_inv h2
    exact AlphaEq.letIn (ihv hv hv') (ihb hb hb')
  | happ _ _ ihf iha =>
    intro u v h1 h2
    obtain ⟨_, _, rfl, hf, ha⟩ := AlphaEq.app_inv h1
    obtain ⟨_, _, rfl, hf', ha'⟩ := AlphaEq.app_inv h2
    exact AlphaEq.app (ihf hf hf') (iha ha ha')
  | hproj _ _ ih =>
    intro u v h1 h2
    obtain ⟨_, rfl, he⟩ := AlphaEq.proj_inv h1
    obtain ⟨_, rfl, he'⟩ := AlphaEq.proj_inv h2
    exact AlphaEq.proj (ih he he')
  | hconstruct _ _ _ ih =>
    intro u v h1 h2
    obtain ⟨_, rfl, ha⟩ := AlphaEq.construct_inv h1
    obtain ⟨_, rfl, ha'⟩ := AlphaEq.construct_inv h2
    exact AlphaEq.construct (AlphaEqs.trans_aux (fun x hx _ _ p q => ih x hx p q) ha ha')
  | hcase _ _ _ ihd iha =>
    intro u v h1 h2
    obtain ⟨_, _, rfl, hd, ha⟩ := AlphaEq.case_inv h1
    obtain ⟨_, _, rfl, hd', ha'⟩ := AlphaEq.case_inv h2
    exact AlphaEq.case (ihd hd hd')
      (AlphaEqAlts.trans_aux (fun x hx _ _ p q => iha x hx p q) ha ha')
  | hfix _ _ ih =>
    intro u v h1 h2
    obtain ⟨_, rfl, hd⟩ := AlphaEq.fix_inv h1
    obtain ⟨_, rfl, hd'⟩ := AlphaEq.fix_inv h2
    exact AlphaEq.fix (AlphaEqDefs.trans_aux (fun x hx _ _ p q => ih x hx p q) hd hd')

theorem AlphaEqs.trans {l m n : List LBTerm} (h1 : AlphaEqs l m) (h2 : AlphaEqs m n) :
    AlphaEqs l n := AlphaEqs.trans_aux (fun _ _ _ _ p q => AlphaEq.trans p q) h1 h2

/-! ## The list relations in indexed form

`Lower` and `WcbvEval` state their list premises by index, so the pointwise readings of
`AlphaEqs` are what a transport consumes.
-/

theorem AlphaEqs.length : ∀ {l m : List LBTerm}, AlphaEqs l m → l.length = m.length
  | [], _, h => by rw [AlphaEqs.nil_inv h]
  | _ :: ts, _, h => by
    obtain ⟨_, _, rfl, _, hts⟩ := AlphaEqs.cons_inv h
    simp [AlphaEqs.length (l := ts) hts]

theorem AlphaEqs.getElem! : ∀ {l m : List LBTerm}, AlphaEqs l m → ∀ i, i < l.length →
    AlphaEq l[i]! m[i]!
  | [], _, _, _, hi => absurd hi (by simp)
  | _ :: ts, _, h, i, hi => by
    obtain ⟨_, _, rfl, ht, hts⟩ := AlphaEqs.cons_inv h
    match i with
    | 0 => simpa using ht
    | i + 1 =>
      have : i < ts.length := by simpa using hi
      simpa using AlphaEqs.getElem! (l := ts) hts i this

theorem AlphaEqs.of_getElem! : ∀ {l m : List LBTerm}, l.length = m.length →
    (∀ i, i < l.length → AlphaEq l[i]! m[i]!) → AlphaEqs l m
  | [], [], _, _ => AlphaEqs.nil
  | t :: ts, u :: us, hl, h =>
    AlphaEqs.cons (by simpa using h 0 (by simp))
      (AlphaEqs.of_getElem! (l := ts) (by simpa using hl)
        (fun i hi => by simpa using h (i + 1) (by simpa using hi)))

theorem AlphaEqAlts.length : ∀ {l m : List (List BinderName × LBTerm)},
    AlphaEqAlts l m → l.length = m.length
  | [], _, h => by rw [AlphaEqAlts.nil_inv h]
  | (_, _) :: rest, _, h => by
    obtain ⟨_, _, _, rfl, _, _, hr⟩ := AlphaEqAlts.cons_inv h
    simp [AlphaEqAlts.length (l := rest) hr]

theorem AlphaEqDefs.length : ∀ {l m : List (@FixDef LBTerm)},
    AlphaEqDefs l m → l.length = m.length
  | [], _, h => by rw [AlphaEqDefs.nil_inv h]
  | _ :: rest, _, h => by
    obtain ⟨_, _, rfl, _, _, hd⟩ := AlphaEqDefs.cons_inv h
    simp [AlphaEqDefs.length (l := rest) hd]

end LBTerm

open LBTerm

namespace LeanToLambdaBox

open Lean Lean4Lean Witness

/-! ## What is invariant under α

Nothing in the λ□ output boundary reads a binder name: box-freedom and the constants a term
names are literally the same on two α-equivalent terms.
-/

theorem NoBoxArgs.alpha_aux : ∀ {l m : List LBTerm},
    (∀ x ∈ l, ∀ u, AlphaEq x u → NoBox x → NoBox u) → AlphaEqs l m → NoBoxArgs l → NoBoxArgs m
  | [], _, _, h, _ => by rw [AlphaEqs.nil_inv h]; trivial
  | _ :: ts, _, ih, h, hb => by
    obtain ⟨_, _, rfl, ht, hts⟩ := AlphaEqs.cons_inv h
    exact ⟨ih _ (List.mem_cons_self ..) _ ht hb.1,
      NoBoxArgs.alpha_aux (l := ts) (fun x hx => ih x (List.mem_cons_of_mem _ hx)) hts hb.2⟩

theorem NoBoxAlts.alpha_aux : ∀ {l m : List (List BinderName × LBTerm)},
    (∀ a ∈ l, ∀ u, AlphaEq a.2 u → NoBox a.2 → NoBox u) → AlphaEqAlts l m →
    NoBoxAlts l → NoBoxAlts m
  | [], _, _, h, _ => by rw [AlphaEqAlts.nil_inv h]; trivial
  | (_, _) :: rest, _, ih, h, hb => by
    obtain ⟨_, _, _, rfl, _, hbb, hr⟩ := AlphaEqAlts.cons_inv h
    exact ⟨ih _ (List.mem_cons_self ..) _ hbb hb.1,
      NoBoxAlts.alpha_aux (l := rest) (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hr hb.2⟩

theorem NoBoxDefs.alpha_aux : ∀ {l m : List (@FixDef LBTerm)},
    (∀ d ∈ l, ∀ u, AlphaEq d.body u → NoBox d.body → NoBox u) → AlphaEqDefs l m →
    NoBoxDefs l → NoBoxDefs m
  | [], _, _, h, _ => by rw [AlphaEqDefs.nil_inv h]; trivial
  | _ :: rest, _, ih, h, hb => by
    obtain ⟨_, _, rfl, _, hbb, hd⟩ := AlphaEqDefs.cons_inv h
    exact ⟨ih _ (List.mem_cons_self ..) _ hbb hb.1,
      NoBoxDefs.alpha_aux (l := rest) (fun d hd' => ih d (List.mem_cons_of_mem _ hd')) hd hb.2⟩

/-- Box-freedom is invariant under α: `NoBox` reads constructors, never names. -/
theorem NoBox.alpha {t t' : LBTerm} (hα : AlphaEq t t') (h : NoBox t) : NoBox t' := by
  revert h t'
  induction t using LBTerm.recData with
  | hbox => intro t' hα hb; exact absurd hb (by simp)
  | hbvar => intro t' hα; rw [AlphaEq.bvar_inv hα]; exact fun _ => trivial
  | hfvar => intro t' hα; rw [AlphaEq.fvar_inv hα]; exact fun _ => trivial
  | hconst => intro t' hα; rw [AlphaEq.const_inv hα]; exact fun _ => trivial
  | hprim => intro t' hα; rw [AlphaEq.prim_inv hα]; exact fun _ => trivial
  | hlam _ _ ih =>
    intro t' hα hb; obtain ⟨_, _, rfl, hbb⟩ := AlphaEq.lambda_inv hα
    rw [NoBox_lambda]; exact ih hbb hb
  | hletIn _ _ _ ihv ihb =>
    intro t' hα hb; obtain ⟨_, _, _, rfl, hv, hbb⟩ := AlphaEq.letIn_inv hα
    exact ⟨ihv hv hb.1, ihb hbb hb.2⟩
  | happ _ _ ihf iha =>
    intro t' hα hb; obtain ⟨_, _, rfl, hf, ha⟩ := AlphaEq.app_inv hα
    exact ⟨ihf hf hb.1, iha ha hb.2⟩
  | hproj _ _ ih =>
    intro t' hα hb; obtain ⟨_, rfl, he⟩ := AlphaEq.proj_inv hα
    rw [NoBox_proj]; exact ih he hb
  | hconstruct _ _ _ ih =>
    intro t' hα hb; obtain ⟨_, rfl, ha⟩ := AlphaEq.construct_inv hα
    exact NoBoxArgs.alpha_aux (fun x hx _ p q => ih x hx p q) ha hb
  | hcase _ _ _ ihd iha =>
    intro t' hα hb; obtain ⟨_, _, rfl, hd, ha⟩ := AlphaEq.case_inv hα
    exact ⟨ihd hd hb.1, NoBoxAlts.alpha_aux (fun x hx _ p q => iha x hx p q) ha hb.2⟩
  | hfix _ _ ih =>
    intro t' hα hb; obtain ⟨_, rfl, hd⟩ := AlphaEq.fix_inv hα
    exact NoBoxDefs.alpha_aux (fun x hx _ p q => ih x hx p q) hd hb

/-- Box-freedom transports both ways. -/
theorem NoBox.alpha_iff {t t' : LBTerm} (hα : AlphaEq t t') : NoBox t ↔ NoBox t' :=
  ⟨NoBox.alpha hα, NoBox.alpha hα.symm⟩

theorem constRefsArgs.alpha_aux : ∀ {l m : List LBTerm},
    (∀ x ∈ l, ∀ u, AlphaEq x u → constRefs x = constRefs u) → AlphaEqs l m →
    constRefsArgs l = constRefsArgs m
  | [], _, _, h => by rw [AlphaEqs.nil_inv h]
  | _ :: ts, _, ih, h => by
    obtain ⟨_, _, rfl, ht, hts⟩ := AlphaEqs.cons_inv h
    rw [constRefsArgs, constRefsArgs, ih _ (List.mem_cons_self ..) _ ht,
      constRefsArgs.alpha_aux (l := ts) (fun x hx => ih x (List.mem_cons_of_mem _ hx)) hts]

theorem constRefsAlts.alpha_aux : ∀ {l m : List (List BinderName × LBTerm)},
    (∀ a ∈ l, ∀ u, AlphaEq a.2 u → constRefs a.2 = constRefs u) → AlphaEqAlts l m →
    constRefsAlts l = constRefsAlts m
  | [], _, _, h => by rw [AlphaEqAlts.nil_inv h]
  | (_, _) :: rest, _, ih, h => by
    obtain ⟨_, _, _, rfl, _, hb, hr⟩ := AlphaEqAlts.cons_inv h
    rw [constRefsAlts, constRefsAlts, ih _ (List.mem_cons_self ..) _ hb,
      constRefsAlts.alpha_aux (l := rest) (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hr]

theorem constRefsDefs.alpha_aux : ∀ {l m : List (@FixDef LBTerm)},
    (∀ d ∈ l, ∀ u, AlphaEq d.body u → constRefs d.body = constRefs u) → AlphaEqDefs l m →
    constRefsDefs l = constRefsDefs m
  | [], _, _, h => by rw [AlphaEqDefs.nil_inv h]
  | _ :: rest, _, ih, h => by
    obtain ⟨_, _, rfl, _, hb, hd⟩ := AlphaEqDefs.cons_inv h
    rw [constRefsDefs, constRefsDefs, ih _ (List.mem_cons_self ..) _ hb,
      constRefsDefs.alpha_aux (l := rest) (fun d hd' => ih d (List.mem_cons_of_mem _ hd')) hd]

/-- The constants a term names are the same on two α-equivalent terms — not merely a
permutation: `constRefs` recurses in the same order and reads no name. -/
theorem constRefs.alpha {t t' : LBTerm} (hα : AlphaEq t t') : constRefs t = constRefs t' := by
  revert t'
  induction t using LBTerm.recData with
  | hbox => intro t' hα; rw [AlphaEq.box_inv hα]
  | hbvar => intro t' hα; rw [AlphaEq.bvar_inv hα]
  | hfvar => intro t' hα; rw [AlphaEq.fvar_inv hα]
  | hconst => intro t' hα; rw [AlphaEq.const_inv hα]
  | hprim => intro t' hα; rw [AlphaEq.prim_inv hα]
  | hlam _ _ ih =>
    intro t' hα; obtain ⟨_, _, rfl, hb⟩ := AlphaEq.lambda_inv hα
    rw [constRefs, constRefs]; exact ih hb
  | hletIn _ _ _ ihv ihb =>
    intro t' hα; obtain ⟨_, _, _, rfl, hv, hb⟩ := AlphaEq.letIn_inv hα
    rw [constRefs, constRefs, ihv hv, ihb hb]
  | happ _ _ ihf iha =>
    intro t' hα; obtain ⟨_, _, rfl, hf, ha⟩ := AlphaEq.app_inv hα
    rw [constRefs, constRefs, ihf hf, iha ha]
  | hproj _ _ ih =>
    intro t' hα; obtain ⟨_, rfl, he⟩ := AlphaEq.proj_inv hα
    rw [constRefs, constRefs, ih he]
  | hconstruct _ _ _ ih =>
    intro t' hα; obtain ⟨_, rfl, ha⟩ := AlphaEq.construct_inv hα
    rw [constRefs, constRefs,
      constRefsArgs.alpha_aux (fun x hx _ p => ih x hx p) ha]
  | hcase _ _ _ ihd iha =>
    intro t' hα; obtain ⟨_, _, rfl, hd, ha⟩ := AlphaEq.case_inv hα
    rw [constRefs, constRefs, ihd hd,
      constRefsAlts.alpha_aux (fun x hx _ p => iha x hx p) ha]
  | hfix _ _ ih =>
    intro t' hα; obtain ⟨_, rfl, hd⟩ := AlphaEq.fix_inv hα
    rw [constRefs, constRefs, constRefsDefs.alpha_aux (fun x hx _ p => ih x hx p) hd]

/-- Reachability through the constant bodies of `Γ` is invariant under α: it is computed
from `constRefs`, and that is. -/
theorem ReachableFrom.alpha {Γ : GlobalDeclarations} {t t' : LBTerm} {kn : Kername}
    (hα : AlphaEq t t') : ReachableFrom Γ t kn ↔ ReachableFrom Γ t' kn := by
  rw [ReachableFrom, ReachableFrom, reachRefs, reachRefs, constRefs.alpha hα]

/-! ## The source side

A tabled body is pinned to the value the code generator reads only up to `Expr.AlphaEq`
(`ReifiedDecl.Prepared`), so a consumer of a tabled body owes an α-transport. Translation
absorbs the renaming — `VExpr` carries no binder name — and erasure carries it across:
the `lam` and `letE` rules copy the *source* name into the emitted node, so the image moves
only up to `LBTerm.AlphaEq`.
-/

/-- `Expr.AlphaEq` is reflexive. -/
theorem Witness.Expr.AlphaEq.refl : ∀ e : Expr, Expr.AlphaEq e e
  | .bvar _ => .bvar
  | .fvar _ => .fvar
  | .mvar _ => .mvar
  | .sort _ => .sort
  | .const _ _ => .const
  | .lit _ => .lit
  | .app f a => .app (Expr.AlphaEq.refl f) (Expr.AlphaEq.refl a)
  | .lam _ ty b _ => .lam (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl b)
  | .forallE _ ty b _ => .forallE (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl b)
  | .letE _ ty v b _ => .letE (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl v) (Expr.AlphaEq.refl b)
  | .proj _ _ e => .proj (Expr.AlphaEq.refl e)
  | .mdata _ e => .mdata (Expr.AlphaEq.refl e)

/-- Translation to `VExpr` is α-blind: `VExpr` has no binder names, so an α-variant of the
source translates to the **same** target, in the same local context. -/
theorem TrExprS.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {ve : VExpr}
    (h : TrExprS env Us Δ e ve) (hα : Expr.AlphaEq e e') : TrExprS env Us Δ e' ve := by
  induction h generalizing e' with
  | bvar hf => cases hα; exact .bvar hf
  | fvar hf => cases hα; exact .fvar hf
  | sort hu => cases hα; exact .sort hu
  | const hc hus hlen => cases hα; exact .const hc hus hlen
  | app hf' ha' _ _ ihf iha =>
    cases hα with | app h1 h2 => exact .app hf' ha' (ihf h1) (iha h2)
  | lam hty' _ _ ihty ihb =>
    cases hα with | lam h1 h2 => exact .lam hty' (ihty h1) (ihb h2)
  | forallE hty' hb' _ _ ihty ihb =>
    cases hα with | forallE h1 h2 => exact .forallE hty' hb' (ihty h1) (ihb h2)
  | letE hval' _ _ _ ihty ihv ihb =>
    cases hα with | letE h1 h2 h3 => exact .letE hval' (ihty h1) (ihv h2) (ihb h3)
  | lit hcl _ ih => cases hα; exact .lit hcl (ih (Expr.AlphaEq.refl _))
  | mdata _ ih => cases hα with | mdata h1 => exact .mdata (ih h1)
  | proj _ hpr ih => cases hα with | proj h1 => exact .proj (ih h1) hpr

/-- Erasure transports a source renaming into a **target** renaming: the `lam` and `letE`
rules copy the source binder name, so the image of an α-variant is an α-variant of the
image. -/
theorem Erases.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) (hα : Expr.AlphaEq e e') :
    ∃ t', LBTerm.AlphaEq t t' ∧ Erases env Us Δ e' t' := by
  induction h generalizing e' with
  | box htr her => exact ⟨.box, AlphaEq.box, .box (TrExprS.alpha htr hα) her⟩
  | bvar hf => cases hα; exact ⟨_, AlphaEq.bvar, .bvar hf⟩
  | fvar hf => cases hα; exact ⟨_, AlphaEq.fvar, .fvar hf⟩
  | ctor hc hi => cases hα; exact ⟨_, AlphaEq.refl _, .ctor hc hi⟩
  | const hc ho => cases hα; exact ⟨_, AlphaEq.const, .const hc ho⟩
  | app _ _ ihf iha =>
    cases hα with
    | app h1 h2 =>
      obtain ⟨f'', hf, hef⟩ := ihf h1
      obtain ⟨a'', ha, hea⟩ := iha h2
      exact ⟨.app f'' a'', AlphaEq.app hf ha, .app hef hea⟩
  | lam hty _ ihb =>
    cases hα with
    | lam h1 h2 =>
      obtain ⟨b'', hb, heb⟩ := ihb h2
      exact ⟨_, AlphaEq.lambda hb, .lam (TrExprS.alpha hty h1) heb⟩
  | letE hty hval _ _ ihv ihb =>
    cases hα with
    | letE h1 h2 h3 =>
      obtain ⟨v'', hv, hev⟩ := ihv h2
      obtain ⟨b'', hb, heb⟩ := ihb h3
      exact ⟨_, AlphaEq.letIn hv hb,
        .letE (TrExprS.alpha hty h1) (TrExprS.alpha hval h2) hev heb⟩
  | proj hs hinf hi _ ih =>
    cases hα with
    | proj h1 =>
      obtain ⟨d'', hd, hed⟩ := ih h1
      exact ⟨_, AlphaEq.proj hd, .proj hs hinf hi hed⟩
  | lit hcl _ ih =>
    cases hα
    obtain ⟨t'', ht, het⟩ := ih (Expr.AlphaEq.refl _)
    exact ⟨t'', ht, .lit hcl het⟩
  | mdata _ ih =>
    cases hα with
    | mdata h1 => obtain ⟨t'', ht, het⟩ := ih h1; exact ⟨t'', ht, .mdata het⟩

/-! ### Why there is no transport in the other direction

A λ□ `.lambda`'s binder name is a function of the source's, so the erasure relation is not
closed under a renaming of its **image**: no premise of any rule can absorb one.
-/

/-- Every `.lambda` an erasure produces carries a source binder name. -/
theorem Erases.target_lambda_name {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {n : BinderName} {b : LBTerm} (h : Erases env Us Δ e (.lambda n b)) :
    ∃ m : Name, n = .named m.toString := by
  generalize ht : LBTerm.lambda n b = t at h
  induction h generalizing n b with
  | lam => cases ht; exact ⟨_, rfl⟩
  | lit _ _ ih => exact ih ht
  | mdata _ ih => exact ih ht
  | _ => cases ht

/-- The image of an erasure is rigid in its binder names: `.lambda .anon b` is α-equivalent
to every `.lambda n b` the relation produces (`LBTerm.AlphaEq.lambda`) and is itself never
produced. So `Erases.alpha` moves a *source* renaming, and a renaming of the image has no
transport. -/
theorem Erases.no_anon_lambda {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {b : LBTerm} : ¬ Erases env Us Δ e (.lambda .anon b) := by
  intro h
  obtain ⟨m, hm⟩ := Erases.target_lambda_name h
  exact BinderName.noConfusion hm

namespace Witness

/-! ### The source-side α kit

`Expr.AlphaEq` pointwise over an argument list, and its compatibility with the two
operations the source semantics performs on terms: de Bruijn instantiation and the
application spine.
-/

/-- α-equivalence pointwise over a list of source terms. -/
abbrev Expr.AlphaEqs : List Expr → List Expr → Prop := List.Forall₂ Expr.AlphaEq

theorem Expr.AlphaEqs.refl : ∀ l : List Expr, Expr.AlphaEqs l l
  | [] => .nil
  | a :: as => .cons (Expr.AlphaEq.refl a) (Expr.AlphaEqs.refl as)

theorem Expr.AlphaEqs.getElem! : ∀ {l m : List Expr}, Expr.AlphaEqs l m → ∀ i, i < l.length →
    Expr.AlphaEq l[i]! m[i]!
  | [], _, _, _, hi => absurd hi (by simp)
  | _ :: ts, _, .cons ht hts, i, hi => by
    match i with
    | 0 => simpa using ht
    | i + 1 => have : i < ts.length := by simpa using hi
               simpa using Expr.AlphaEqs.getElem! hts i this

theorem Expr.AlphaEqs.of_getElem! : ∀ {l m : List Expr}, l.length = m.length →
    (∀ i, i < l.length → Expr.AlphaEq l[i]! m[i]!) → Expr.AlphaEqs l m
  | [], [], _, _ => .nil
  | _ :: ts, _ :: us, hl, h =>
    .cons (by simpa using h 0 (by simp))
      (Expr.AlphaEqs.of_getElem! (l := ts) (by simpa using hl)
        (fun i hi => by simpa using h (i + 1) (by simpa using hi)))

theorem Expr.AlphaEqs.drop : ∀ (n : Nat) {l m : List Expr}, Expr.AlphaEqs l m →
    Expr.AlphaEqs (l.drop n) (m.drop n)
  | 0, _, _, h => h
  | _ + 1, [], _, h => by cases h; exact .nil
  | n + 1, _ :: _, _, .cons _ ht => by simpa using Expr.AlphaEqs.drop n ht

/-- Lifting loose bound variables is α-blind. -/
theorem Expr.AlphaEq.liftLooseBVars' : ∀ {e e' : Expr}, Expr.AlphaEq e e' → ∀ s d,
    Expr.AlphaEq (e.liftLooseBVars' s d) (e'.liftLooseBVars' s d)
  | _, _, .bvar, _, _ => by simp [Lean.Expr.liftLooseBVars']; split <;> exact .bvar
  | _, _, .fvar, _, _ => .fvar
  | _, _, .mvar, _, _ => .mvar
  | _, _, .sort, _, _ => .sort
  | _, _, .const, _, _ => .const
  | _, _, .lit, _, _ => .lit
  | _, _, .app h1 h2, s, d => .app (h1.liftLooseBVars' s d) (h2.liftLooseBVars' s d)
  | _, _, .lam h1 h2, s, d => .lam (h1.liftLooseBVars' s d) (h2.liftLooseBVars' (s + 1) d)
  | _, _, .forallE h1 h2, s, d =>
    .forallE (h1.liftLooseBVars' s d) (h2.liftLooseBVars' (s + 1) d)
  | _, _, .letE h1 h2 h3, s, d =>
    .letE (h1.liftLooseBVars' s d) (h2.liftLooseBVars' s d) (h3.liftLooseBVars' (s + 1) d)
  | _, _, .proj h1, s, d => .proj (h1.liftLooseBVars' s d)
  | _, _, .mdata h1, s, d => .mdata (h1.liftLooseBVars' s d)

/-- Instantiating a bound variable is α-blind in both arguments. -/
theorem Expr.AlphaEq.instantiate1' : ∀ {e e' : Expr}, Expr.AlphaEq e e' →
    ∀ {a a' : Expr}, Expr.AlphaEq a a' → ∀ d,
    Expr.AlphaEq (e.instantiate1' a d) (e'.instantiate1' a' d)
  | _, _, .bvar, _, _, ha, d => by
    simp only [Lean.Expr.instantiate1']
    split
    · exact .bvar
    · split
      · exact ha.liftLooseBVars' 0 d
      · exact .bvar
  | _, _, .fvar, _, _, _, _ => .fvar
  | _, _, .mvar, _, _, _, _ => .mvar
  | _, _, .sort, _, _, _, _ => .sort
  | _, _, .const, _, _, _, _ => .const
  | _, _, .lit, _, _, _, _ => .lit
  | _, _, .app h1 h2, _, _, ha, d => .app (h1.instantiate1' ha d) (h2.instantiate1' ha d)
  | _, _, .lam h1 h2, _, _, ha, d => .lam (h1.instantiate1' ha d) (h2.instantiate1' ha (d + 1))
  | _, _, .forallE h1 h2, _, _, ha, d =>
    .forallE (h1.instantiate1' ha d) (h2.instantiate1' ha (d + 1))
  | _, _, .letE h1 h2 h3, _, _, ha, d =>
    .letE (h1.instantiate1' ha d) (h2.instantiate1' ha d) (h3.instantiate1' ha (d + 1))
  | _, _, .proj h1, _, _, ha, d => .proj (h1.instantiate1' ha d)
  | _, _, .mdata h1, _, _, ha, d => .mdata (h1.instantiate1' ha d)

/-- An application spine is α-equivalent componentwise. -/
theorem Expr.AlphaEq.mkApps : ∀ {f f' : Expr} {as as' : List Expr}, Expr.AlphaEq f f' →
    Expr.AlphaEqs as as' →
    Expr.AlphaEq (LeanToLambdaBox.mkApps f as) (LeanToLambdaBox.mkApps f' as')
  | _, _, [], _, hf, h => by cases h; exact hf
  | _, _, _ :: _, _, hf, .cons ha has => by
    rw [LeanToLambdaBox.mkApps_cons, LeanToLambdaBox.mkApps_cons]
    exact Expr.AlphaEq.mkApps (Expr.AlphaEq.app hf ha) has

/-- Inversion at an application spine: an α-variant is a spine of the same length, with an
α-variant head and α-variant arguments. -/
theorem Expr.AlphaEq.mkApps_inv : ∀ {as : List Expr} {f e : Expr},
    Expr.AlphaEq (LeanToLambdaBox.mkApps f as) e →
    ∃ f' as', e = LeanToLambdaBox.mkApps f' as' ∧ Expr.AlphaEq f f' ∧ Expr.AlphaEqs as as'
  | [], _, _, h => ⟨_, [], rfl, h, .nil⟩
  | _ :: rest, f, e, h => by
    rw [LeanToLambdaBox.mkApps_cons] at h
    obtain ⟨g, bs, rfl, hg, hbs⟩ := Expr.AlphaEq.mkApps_inv (as := rest) h
    cases hg with
    | app h1 h2 => exact ⟨_, _ :: bs, rfl, h1, .cons h2 hbs⟩

/-- Inversion at a constant-headed spine: an α-variant is a spine of the same constant with
α-variant arguments. -/
theorem Expr.AlphaEq.mkApps_const_inv {c : Name} {us : List Level} {as : List Expr} {e : Expr}
    (h : Expr.AlphaEq (LeanToLambdaBox.mkApps (Lean.Expr.const c us) as) e) :
    ∃ bs, e = LeanToLambdaBox.mkApps (Lean.Expr.const c us) bs ∧ Expr.AlphaEqs as bs := by
  obtain ⟨f', bs, rfl, hf, hbs⟩ := Expr.AlphaEq.mkApps_inv h
  cases hf
  exact ⟨bs, rfl, hbs⟩

/-- Splitting an α-equivalence of a concatenation. -/
theorem Expr.AlphaEqs.append_inv : ∀ {l₁ l₂ m : List Expr}, Expr.AlphaEqs (l₁ ++ l₂) m →
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ Expr.AlphaEqs l₁ m₁ ∧ Expr.AlphaEqs l₂ m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hx hxs => by
    obtain ⟨m₁, m₂, rfl, h₁, h₂⟩ := Expr.AlphaEqs.append_inv hxs
    exact ⟨_ :: m₁, m₂, rfl, .cons hx h₁, h₂⟩

/-- Inversion at a cons. -/
theorem Expr.AlphaEqs.cons_inv : ∀ {a : Expr} {l m : List Expr}, Expr.AlphaEqs (a :: l) m →
    ∃ b m', m = b :: m' ∧ Expr.AlphaEq a b ∧ Expr.AlphaEqs l m'
  | _, _, _, .cons h ht => ⟨_, _, rfl, h, ht⟩

/-- α-equivalence of two concatenations, from the halves. -/
theorem Expr.AlphaEqs.append : ∀ {l₁ m₁ l₂ m₂ : List Expr}, Expr.AlphaEqs l₁ m₁ →
    Expr.AlphaEqs l₂ m₂ → Expr.AlphaEqs (l₁ ++ l₂) (m₁ ++ m₂)
  | [], _, _, _, h₁, h₂ => by cases h₁; exact h₂
  | _ :: _, _, _, _, .cons hx hxs, h₂ => .cons hx (Expr.AlphaEqs.append hxs h₂)

end Witness

/-- A definitional-equality step is α-blind: translation is (`TrExprS.alpha`), and the step
records nothing else about the two terms. -/
theorem StepDefeq.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e₁ e₂ e₁' e₂' : Expr}
    (h : StepDefeq env Us Δ e₁ e₂) (h₁ : Expr.AlphaEq e₁ e₁') (h₂ : Expr.AlphaEq e₂ e₂') :
    StepDefeq env Us Δ e₁' e₂' :=
  ⟨h.choose, h.choose_spec.choose, TrExprS.alpha h.choose_spec.choose_spec.1 h₁,
    TrExprS.alpha h.choose_spec.choose_spec.2.1 h₂, h.choose_spec.choose_spec.2.2⟩

/-- Source evaluation transports a renaming: an α-variant of a term evaluates to an
α-variant of its value. The rules read the source only through translation (α-blind by
`TrExprS.alpha`), de Bruijn instantiation and the application spine, all of which commute
with a renaming. -/
theorem SEval.alpha {env : VEnv} {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Δ : VLCtx} {e v : Expr} (h : SEval env bo Us fl Δ e v) {e' : Expr}
    (hα : Expr.AlphaEq e e') :
    ∃ v', Expr.AlphaEq v v' ∧ SEval env bo Us fl Δ e' v' := by
  induction h generalizing e' with
  | lam n ty b bi => cases hα with | lam h1 h2 => exact ⟨_, .lam h1 h2, .lam ..⟩
  | sort => cases hα; exact ⟨_, .sort, .sort⟩
  | forallE =>
    cases hα with | forallE h1 h2 => exact ⟨_, .forallE h1 h2, .forallE⟩
  | beta hfl _ _ _ ihf iha ihb =>
    cases hα with
    | app h1 h2 =>
      obtain ⟨vf, hvf, hef⟩ := ihf h1
      cases hvf with
      | lam hty hbd =>
        obtain ⟨va, hva, hea⟩ := iha h2
        obtain ⟨r', hr, her⟩ := ihb (hbd.instantiate1' hva 0)
        exact ⟨r', hr, .beta hfl hef hea her⟩
  | zeta hfl _ _ ihv ihb =>
    cases hα with
    | letE h1 h2 h3 =>
      obtain ⟨vv, hvv, hev⟩ := ihv h2
      obtain ⟨r', hr, her⟩ := ihb (h3.instantiate1' hvv 0)
      exact ⟨r', hr, .zeta hfl hev her⟩
  | @deltaC c us ups args argsv b b' _ hfl hb hnd hinst hlen hargs hdef _ ihargs ihcont =>
    obtain ⟨args₂, rfl, hargs₂⟩ := Expr.AlphaEq.mkApps_const_inv hα
    have hlen₂ : args.length = args₂.length := List.Forall₂.length_eq hargs₂
    obtain ⟨argsv₂, hlv, hpt⟩ := exists_list_of_index args.length
      (fun i a => Expr.AlphaEq argsv[i]! a ∧ SEval env bo Us fl Δ args₂[i]! a)
      (fun i hi => ihargs i hi (Expr.AlphaEqs.getElem! hargs₂ i hi))
    have hav : Expr.AlphaEqs argsv argsv₂ :=
      Expr.AlphaEqs.of_getElem! (by omega) (fun i hi => (hpt i (by omega)).1)
    obtain ⟨r', hr, her⟩ :=
      ihcont (Expr.AlphaEq.mkApps (Expr.AlphaEq.refl b') hav)
    refine ⟨r', hr, .deltaC hfl hb hnd hinst (by omega) (fun i hi => (hpt i (by omega)).2)
      (StepDefeq.alpha hdef (Expr.AlphaEq.mkApps Expr.AlphaEq.const hav)
        (Expr.AlphaEq.mkApps (Expr.AlphaEq.refl b') hav)) her⟩
  | @ctorVal cn I us iid k np nfs args argsv hc hi harity hlen hargs ihargs =>
    obtain ⟨args₂, rfl, hargs₂⟩ := Expr.AlphaEq.mkApps_const_inv hα
    have hlen₂ : args.length = args₂.length := List.Forall₂.length_eq hargs₂
    obtain ⟨argsv₂, hlv, hpt⟩ := exists_list_of_index args.length
      (fun i a => Expr.AlphaEq argsv[i]! a ∧ SEval env bo Us fl Δ args₂[i]! a)
      (fun i hi => ihargs i hi (Expr.AlphaEqs.getElem! hargs₂ i hi))
    have hav : Expr.AlphaEqs argsv argsv₂ :=
      Expr.AlphaEqs.of_getElem! (by omega) (fun i hi => (hpt i (by omega)).1)
    exact ⟨_, Expr.AlphaEq.mkApps Expr.AlphaEq.const hav,
      .ctorVal hc hi (by omega) (by omega) (fun i hi => (hpt i (by omega)).2)⟩
  | @indVal cn us iid np nfs args argsv hi hlen hargs ihargs =>
    obtain ⟨args₂, rfl, hargs₂⟩ := Expr.AlphaEq.mkApps_const_inv hα
    have hlen₂ : args.length = args₂.length := List.Forall₂.length_eq hargs₂
    obtain ⟨argsv₂, hlv, hpt⟩ := exists_list_of_index args.length
      (fun i a => Expr.AlphaEq argsv[i]! a ∧ SEval env bo Us fl Δ args₂[i]! a)
      (fun i hi => ihargs i hi (Expr.AlphaEqs.getElem! hargs₂ i hi))
    have hav : Expr.AlphaEqs argsv argsv₂ :=
      Expr.AlphaEqs.of_getElem! (by omega) (fun i hi => (hpt i (by omega)).1)
    exact ⟨_, Expr.AlphaEq.mkApps Expr.AlphaEq.const hav,
      .indVal hi (by omega) (fun i hi => (hpt i (by omega)).2)⟩
  | lit hfl _ ih =>
    cases hα
    obtain ⟨r', hr, her⟩ := ih (Expr.AlphaEq.refl _)
    exact ⟨r', hr, .lit hfl her⟩
  | @proj S ctor i discr cus cargs np nf cidx r hfl hct hnp hdiscr hlt hdef _ ihd ihc =>
    cases hα with
    | proj h1 =>
      obtain ⟨vd, hvd, hed⟩ := ihd h1
      obtain ⟨cargs₂, rfl, hcargs⟩ := Expr.AlphaEq.mkApps_const_inv hvd
      have hcl : cargs.length = cargs₂.length := List.Forall₂.length_eq hcargs
      have hfield : Expr.AlphaEq cargs[np + i]! cargs₂[np + i]! :=
        Expr.AlphaEqs.getElem! hcargs _ hlt
      obtain ⟨r', hr, her⟩ := ihc hfield
      exact ⟨r', hr, .proj hfl hct hnp hed (by omega) (StepDefeq.alpha hdef (.proj h1) hfield) her⟩
  | @iota con I ctor us cus pre prev minors minorsv extra extrav cargs disc r np cidx nfs
      hfl hsh ho hct hnp hinf hpre hpres hdiscr hmin hmins hxlen hxs hidx hdef _
      ihpres ihd ihmins ihxs ihc =>
    obtain ⟨L, rfl, hL⟩ := Expr.AlphaEq.mkApps_const_inv hα
    obtain ⟨M, extra₂, rfl, hM, hx₂⟩ := Expr.AlphaEqs.append_inv hL
    obtain ⟨pre₂, L2, rfl, hpre₂, hL2⟩ := Expr.AlphaEqs.append_inv hM
    obtain ⟨disc₂, minors₂, rfl, hdisc₂, hmin₂⟩ := Expr.AlphaEqs.cons_inv hL2
    have hlpre : pre.length = pre₂.length := List.Forall₂.length_eq hpre₂
    have hlmin : minors.length = minors₂.length := List.Forall₂.length_eq hmin₂
    have hlx : extra.length = extra₂.length := List.Forall₂.length_eq hx₂
    obtain ⟨prev₂, hlpv, hptp⟩ := exists_list_of_index pre.length
      (fun i a => Expr.AlphaEq prev[i]! a ∧ SEval env bo Us fl Δ pre₂[i]! a)
      (fun i hi => ihpres i hi (Expr.AlphaEqs.getElem! hpre₂ i hi))
    obtain ⟨minorsv₂, hlmv, hptm⟩ := exists_list_of_index minors.length
      (fun i a => Expr.AlphaEq minorsv[i]! a ∧ SEval env bo Us fl Δ minors₂[i]! a)
      (fun i hi => ihmins i hi (Expr.AlphaEqs.getElem! hmin₂ i hi))
    obtain ⟨extrav₂, hlxv, hptx⟩ := exists_list_of_index extra.length
      (fun i a => Expr.AlphaEq extrav[i]! a ∧ SEval env bo Us fl Δ extra₂[i]! a)
      (fun i hi => ihxs i hi (Expr.AlphaEqs.getElem! hx₂ i hi))
    obtain ⟨vd, hvd, hed⟩ := ihd hdisc₂
    obtain ⟨cargs₂, rfl, hcargs⟩ := Expr.AlphaEq.mkApps_const_inv hvd
    have hsel : Expr.AlphaEq minors[cidx]! minors₂[cidx]! :=
      Expr.AlphaEqs.getElem! hmin₂ cidx hidx
    have hbody : Expr.AlphaEq (mkApps minors[cidx]! (cargs.drop np ++ extra))
        (mkApps minors₂[cidx]! (cargs₂.drop np ++ extra₂)) :=
      Expr.AlphaEq.mkApps hsel
        (Expr.AlphaEqs.append (Expr.AlphaEqs.drop np hcargs) hx₂)
    obtain ⟨r', hr, her⟩ := ihc hbody
    refine ⟨r', hr, .iota hfl (hlpre ▸ hlmin ▸ hsh) ho hct hnp hinf (by omega)
      (fun i hi => (hptp i (by omega)).2)
      hed (by omega) (fun i hi => (hptm i (by omega)).2) (by omega)
      (fun i hi => (hptx i (by omega)).2) (by omega)
      (StepDefeq.alpha hdef
        (Expr.AlphaEq.mkApps Expr.AlphaEq.const
          (Expr.AlphaEqs.append (Expr.AlphaEqs.append hpre₂ (.cons hdisc₂ hmin₂)) hx₂))
        hbody) her⟩

/-! ## Where the target side stops

`Lower`'s own arms are already blind to binder names — `lambda`, `letIn` and `case` quantify
over the names on both sides, and `LowerAlt` pins only a branch's binder *count*. What is not
α-closed is the pair of `fix` arms: both read a specification body out of `Γ` by **equality**
(`DefnDecl`, and `CloseConstAt` for the emitted body), and an α-variant of a declared body is
not a declared body.
-/

/-- **`Lower` is not closed under α on its source.** At the block fixture of `LowerFix.lean`,
`Lower.fixBody` relates member 0's declared body `λ x. □` to the emitted `.fix`; renaming that
λ's binder leaves the relation, because the only two arms with a `.fix` image demand a
declared body and `specEnv` declares no `λ y. □`. -/
theorem Lower.not_alpha :
    ¬ ∀ (Γ : GlobalDeclarations) (t t' s : LBTerm), Lower Γ t s → LBTerm.AlphaEq t t' →
        ∃ s', LBTerm.AlphaEq s s' ∧ Lower Γ t' s' := by
  intro H
  obtain ⟨s', hs', hlow⟩ := H LowerFixFixture.specEnv LowerFixFixture.b₀
    (.lambda (.named "y") .box) (.fix LowerFixFixture.defs 0)
    (Lower.fixBody' LowerFixFixture.lowerfix_nv rfl (by decide)) (by decide)
  obtain ⟨defs', rfl, -⟩ := LBTerm.AlphaEq.fix_inv hs'
  obtain ⟨kns₂, bs₂, bs₂', ids₂, hblk₂, hcase⟩ := Lower.target_fix hlow rfl
  rcases hcase with ⟨kn, hkn, -⟩ | ⟨hj, -⟩
  · exact LBTerm.noConfusion hkn
  · obtain ⟨hj0, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have hd := hblk₂.hdecl 0 (by rw [← hblk₂.hb]; exact hj0)
    rw [hjeq] at hd
    rcases LowerFixFixture.specEnv_body_eq hd with h | h <;>
      simp [LowerFixFixture.b₀, LowerFixFixture.b₁] at h

end LeanToLambdaBox
