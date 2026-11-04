import EraseProof.Spec
import EraseProof.Bridge.Subst
import Metalean.Metatheory.SubjectReduction
import Metalean.Metatheory.Injectivity

/-!
# Definitional equality of congruent terms

`DCong E P Γ₁ Γ₂ t₁ t₂`: the term `t₁` in the context `Γ₁` and the term `t₂` in the context `Γ₂`
have the same shape, binders extending both contexts with their own binder types, except at leaves
(definitionally equal terms) and, when `P` holds, at projections of congruent majors, whose levels
and parameters may differ (the types of the majors fix them). `DCong.defeq`: without projection
nodes (`¬ P`), congruent terms are definitionally equal at every type of the first, when `Γ₁` is
well formed and its entries are equal types to those of `Γ₂` (`CtxConv`); the version for typed
terms on both sides is `DCong.defeq₂` (`Bridge/Det.lean`). `DCong.subst`: one term under pointwise
congruent substitutions gives congruent terms.
-/

open Metalean

namespace EraseProof

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {P : Prop}

/-- Congruence of terms in two contexts, with definitional equality at the leaves and, when `P`
holds, projections of congruent majors at any levels and parameters. -/
inductive DCong (E : Env ζ) (P : Prop) :
    {n : Nat} → Ctx ζ ℓ 0 n → Ctx ζ ℓ 0 n → Expr ζ ℓ n → Expr ζ ℓ n → Prop
  | refl {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {e : Expr ζ ℓ n} : DCong E P Γ₁ Γ₂ e e
  | leaf {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {e₁ e₂ T : Expr ζ ℓ n} :
      E[Γ₁] ⊢ e₁ ≡ e₂ : T → DCong E P Γ₁ Γ₂ e₁ e₂
  | app {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {f₁ f₂ a₁ a₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ f₁ f₂ → DCong E P Γ₁ Γ₂ a₁ a₂ → DCong E P Γ₁ Γ₂ (.app f₁ a₁) (.app f₂ a₂)
  | lam {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {A₁ A₂ : Expr ζ ℓ n} {b₁ b₂ : Expr ζ ℓ (n + 1)} :
      DCong E P Γ₁ Γ₂ A₁ A₂ → DCong E P (Γ₁.snoc A₁) (Γ₂.snoc A₂) b₁ b₂ →
      DCong E P Γ₁ Γ₂ (.lam A₁ b₁) (.lam A₂ b₂)
  | forallE {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {A₁ A₂ : Expr ζ ℓ n} {b₁ b₂ : Expr ζ ℓ (n + 1)} :
      DCong E P Γ₁ Γ₂ A₁ A₂ → DCong E P (Γ₁.snoc A₁) (Γ₂.snoc A₂) b₁ b₂ →
      DCong E P Γ₁ Γ₂ (.forallE A₁ b₁) (.forallE A₂ b₂)
  | letE {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {A₁ A₂ v₁ v₂ : Expr ζ ℓ n} {b₁ b₂ : Expr ζ ℓ (n + 1)} :
      DCong E P Γ₁ Γ₂ A₁ A₂ → DCong E P Γ₁ Γ₂ v₁ v₂ → DCong E P Γ₁ Γ₂ (b₁.inst v₁) (b₂.inst v₂) →
      DCong E P Γ₁ Γ₂ (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂)
  | ind {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
      {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} :
      (∀ p, DCong E P Γ₁ Γ₂ (ps₁ p) (ps₂ p)) → (∀ i, DCong E P Γ₁ Γ₂ (is₁ i) (is₂ i)) →
      DCong E P Γ₁ Γ₂ (.ind η s ls ps₁ is₁) (.ind η s ls ps₂ is₂)
  | ctor {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
      {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
      {rf₁ rf₂ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n} :
      (∀ p, DCong E P Γ₁ Γ₂ (ps₁ p) (ps₂ p)) → (∀ f, DCong E P Γ₁ Γ₂ (fds₁ f) (fds₂ f)) →
      (∀ f, DCong E P Γ₁ Γ₂ (rf₁ f) (rf₂ f)) →
      DCong E P Γ₁ Γ₂ (.ctor η s c ls ps₁ fds₁ rf₁) (.ctor η s c ls ps₂ fds₂ rf₂)
  | recr {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
      {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
      {mins₁ mins₂ : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n}
      {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} {maj₁ maj₂ : Expr ζ ℓ n} :
      (∀ p, DCong E P Γ₁ Γ₂ (ps₁ p) (ps₂ p)) → (∀ t, DCong E P Γ₁ Γ₂ (ms₁ t) (ms₂ t)) →
      (∀ t c, DCong E P Γ₁ Γ₂ (mins₁ t c) (mins₂ t c)) → (∀ i, DCong E P Γ₁ Γ₂ (is₁ i) (is₂ i)) →
      DCong E P Γ₁ Γ₂ maj₁ maj₂ →
      DCong E P Γ₁ Γ₂ (.recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁) (.recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂)
  | quot {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l : Level ℓ} {α₁ α₂ r₁ r₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ α₁ α₂ → DCong E P Γ₁ Γ₂ r₁ r₂ →
      DCong E P Γ₁ Γ₂ (.quot η l α₁ r₁) (.quot η l α₂ r₂)
  | quotMk {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l : Level ℓ}
      {α₁ α₂ r₁ r₂ a₁ a₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ α₁ α₂ → DCong E P Γ₁ Γ₂ r₁ r₂ → DCong E P Γ₁ Γ₂ a₁ a₂ →
      DCong E P Γ₁ Γ₂ (.quotMk η l α₁ r₁ a₁) (.quotMk η l α₂ r₂ a₂)
  | quotLift {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l₁ l₂ : Level ℓ}
      {α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ h₁ h₂ a₁ a₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ α₁ α₂ → DCong E P Γ₁ Γ₂ r₁ r₂ → DCong E P Γ₁ Γ₂ β₁ β₂ →
      DCong E P Γ₁ Γ₂ f₁ f₂ → DCong E P Γ₁ Γ₂ h₁ h₂ → DCong E P Γ₁ Γ₂ a₁ a₂ →
      DCong E P Γ₁ Γ₂ (.quotLift η l₁ l₂ α₁ r₁ β₁ f₁ h₁ a₁) (.quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂)
  | quotInd {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l : Level ℓ}
      {α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ a₁ a₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ α₁ α₂ → DCong E P Γ₁ Γ₂ r₁ r₂ → DCong E P Γ₁ Γ₂ β₁ β₂ →
      DCong E P Γ₁ Γ₂ f₁ f₂ → DCong E P Γ₁ Γ₂ a₁ a₂ →
      DCong E P Γ₁ Γ₂ (.quotInd η l α₁ r₁ β₁ f₁ a₁) (.quotInd η l α₂ r₂ β₂ f₂ a₂)
  /-- Structure projections of congruent majors, at any levels and parameters. -/
  | projStruct {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)}
      {s : Fin ι.nsorts} {c₁ c₂ : Fin (ι.nctors s)} (hP : P)
      (h₁ : (E.get η).block.IsStructure s c₁) (h₂ : (E.get η).block.IsStructure s c₂)
      {ls₁ ls₂ : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
      {e₁ e₂ : Expr ζ ℓ n}
      (f₁ : Fin (ι.ctors s c₁).nfields) (f₂ : Fin (ι.ctors s c₂).nfields) (hf : f₁.val = f₂.val) :
      DCong E P Γ₁ Γ₂ e₁ e₂ →
      DCong E P Γ₁ Γ₂ (h₁.projTerm η ls₁ ps₁ f₁ e₁) (h₂.projTerm η ls₂ ps₂ f₂ e₂)
  /-- Proof projections of congruent majors, at any levels and parameters. -/
  | projProof {n} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)}
      {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hP : P) {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
      {hi₁ hi₂ : ι.nindices s = 0} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {f : Nat}
      {e₁ e₂ : Expr ζ ℓ n} :
      DCong E P Γ₁ Γ₂ e₁ e₂ →
      DCong E P Γ₁ Γ₂ (projProofTerm E η s c ls₁ hi₁ ps₁ f e₁) (projProofTerm E η s c ls₂ hi₂ ps₂ f e₂)

/-- The entries of `Γ₁` are equal types to those of `Γ₂`, in `Γ₁`. -/
def CtxConv (E : Env ζ) {n : Nat} (Γ₁ Γ₂ : Ctx ζ ℓ 0 n) : Prop :=
  ∀ v, E[Γ₁] ⊢ Γ₁.get v ≡ Γ₂.get v typ

/-- The major of a typed recursor has the inductive type at the recursor's levels, parameters
and indices. Reference: `Defeq.recr_inv` (`ML Typing/Inversion.lean:193`). -/
theorem recr_major {n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig} {η : Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
    {mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n} {maj T : Expr ζ ℓ n}
    (h : E[Γ] ⊢ .recr η s ls l ps ms mins is maj : T) : E[Γ] ⊢ maj : .ind η s ls ps is := by
  obtain ⟨_, _, _, _, _, -, hps, -, -, his, hmaj, -, -⟩ := h.recr_inv
  exact (TypeEq.ofDefEq (Defeq.indDF hps his)).conv hmaj.right

namespace DCong

/-- Type equality is stable under weakening. -/
theorem typeEq_wk {n : Nat} {Γ : Ctx ζ ℓ 0 n} {a b : Expr ζ ℓ n} (A : Expr ζ ℓ n)
    (h : E[Γ] ⊢ a ≡ b typ) : E[Γ.snoc A] ⊢ a.wk ≡ b.wk typ := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h => obtain ⟨u, h⟩ := h; exact .ofDefEq (u := u) (h.wk A)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A well-formed context converts itself. -/
theorem CtxConv.refl {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok) : CtxConv E Γ Γ :=
  fun v => (hΓ.get v).typeEq

/-- Extending both contexts with equal types. -/
theorem CtxConv.snoc {n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {A₁ A₂ : Expr ζ ℓ n}
    (hc : CtxConv E Γ₁ Γ₂) (hA : E[Γ₁] ⊢ A₁ ≡ A₂ typ) : CtxConv E (Γ₁.snoc A₁) (Γ₂.snoc A₂) := by
  intro v
  cases v using Fin.lastCases with
  | last => simpa using typeEq_wk A₁ hA
  | cast v =>
    rw [Ctx.get_snoc _ _ _ (Nat.ne_of_lt v.isLt), Ctx.get_snoc _ _ _ (Nat.ne_of_lt v.isLt)]
    simpa using typeEq_wk A₁ (hc v)

/-- A judgement in `Γ₂` holds in `Γ₁`. Reference: `Defeq.substitution`
(`ML Typing/Substitution.lean:182`) with the identity substitution. -/
theorem CtxConv.transport {n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} (hΓ : E[Γ₁] ⊢ ok)
    (hc : CtxConv E Γ₁ Γ₂) {a b T : Expr ζ ℓ n} (h : E[Γ₂] ⊢ a ≡ b : T) : E[Γ₁] ⊢ a ≡ b : T := by
  have hσ : E[Γ₁] ⊢ Subst.id ⊣ Γ₂ := fun v => by
    simp; exact (hc v).conv (hΓ.var v)
  simpa using h.substitution hσ

/-- A term with two inductive types has equal levels and definitionally equal parameters. -/
theorem ind_type_inj (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok) {ι : IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}
    {e : Expr ζ ℓ n} (h₁ : E[Γ] ⊢ e : .ind η s ls₁ ps₁ is₁) (h₂ : E[Γ] ⊢ e : .ind η s ls₂ ps₂ is₂) :
    ls₁ = ls₂ ∧ ∀ p, ∃ t, E[Γ] ⊢ ps₁ p ≡ ps₂ p : t := by
  obtain ⟨l, hl⟩ := (Defeq.uniqTy hE hΓ h₁ h₂).sort_uniq hE hΓ
  obtain ⟨_, _, hps, his, -⟩ := hl.left.ind_inv
  obtain ⟨hls, hps', -⟩ := (Defeq.retype hE hΓ hl (Defeq.indDF hps his).right).ind_inj hE hΓ
  exact ⟨hls, hps'⟩

/-- `ctorDF` with the field-type premises derived from the environment's well-formedness. -/
theorem ctor_defeq (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ls : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {rf₁ rf₂ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
    (hps : ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (hfds : ∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
      (((E.get η).block.ctors s c).ordinary f).type{ls}.subst
        (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le)))
    (hrf : ∀ f, E[Γ] ⊢ rf₁ f ≡ rf₂ f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps₁ (Fin.append ps₁ fds₁)) :
    E[Γ] ⊢ .ctor η s c ls ps₁ fds₁ rf₁ ≡ .ctor η s c ls ps₂ fds₂ rf₂ :
      .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) := by
  have hB := (hE.entryWF η).block
  have hC := hB.ctors s c
  exact .ctorDF hps hfds hrf
    (fun f => hC.ordinaryFieldExpr_congr hB.params f hps fun g _ => hfds g)
    (fun f => (hC.recursiveFieldExpr_congr hB.params rfl f hps hfds).choose_spec)
    (.indDF hps fun i => hC.targetIndex_congr hB.params i hps hfds)

/-- Congruent terms without projection nodes are definitionally equal at every type of the
first. -/
theorem defeq (hE : EnvWF E) (hnP : ¬ P) {n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {t₁ t₂ : Expr ζ ℓ n}
    (h : DCong E P Γ₁ Γ₂ t₁ t₂) :
    E[Γ₁] ⊢ ok → CtxConv E Γ₁ Γ₂ → ∀ {T}, E[Γ₁] ⊢ t₁ : T → E[Γ₁] ⊢ t₁ ≡ t₂ : T := by
  induction h with
  | refl => intro _ _ _ ht; exact ht
  | leaf h => intro hΓ _ _ ht; exact Defeq.retype hE hΓ h ht
  | app _ _ ihf iha =>
    intro hΓ hc T ht
    obtain ⟨A, B, hf, ha, hT⟩ := ht.app_inv
    have hf' := ihf hΓ hc hf
    have ha' := iha hΓ hc ha
    obtain ⟨_, hfa⟩ := hf.regular
    obtain ⟨l₁, l₂, hA, hB, -⟩ := hfa.forallE_ty_inv
    exact hT.symm.conv (Defeq.appDF hA hB hf' ha' (hB.inst_congr ha'))
  | lam _ _ ihA ihb =>
    intro hΓ hc T ht
    obtain ⟨B, hb, hT⟩ := ht.lam_inv hΓ
    obtain ⟨u, hfa⟩ := hT.right
    obtain ⟨l₁, l₂, hA, hB, -⟩ := hfa.forallE_ty_inv
    have hA' := ihA hΓ hc hA
    have hb' := ihb (.snoc hΓ ⟨_, hA⟩) (CtxConv.snoc hc (.ofDefEq hA')) hb
    exact hT.symm.conv (.lamDF hA' hB (hA'.snocConv hB) hb' (hA'.snocConv hb'))
  | forallE _ _ ihA ihB =>
    intro hΓ hc T ht
    obtain ⟨l₁, l₂, hA, hB, hT⟩ := ht.forallE_ty_inv
    have hA' := ihA hΓ hc hA
    have hB' := ihB (.snoc hΓ ⟨_, hA⟩) (CtxConv.snoc hc (.ofDefEq hA')) hB
    exact hT.symm.conv (.forallEDF hA' hB' (hA'.snocConv hB'))
  | letE _ _ _ ihA ihv ihb =>
    intro hΓ hc T ht
    obtain ⟨r, ⟨u, hA⟩, hv, hb, hT⟩ := ht.letE_inv hΓ
    have hA' := ihA hΓ hc hA
    have hv' := ihv hΓ hc hv
    have hb' := ihb hΓ hc hb
    obtain ⟨l, hr⟩ := hb.regular
    have z₁ := Defeq.zeta hA hv hr hb
    have z₂ := Defeq.zeta hA'.right ((TypeEq.ofDefEq hA').conv hv'.right) hr hb'.right
    exact hT.symm.conv (z₁.trans (hb'.trans z₂.symm))
  | ind _ _ ihps ihis =>
    intro hΓ hc T ht
    obtain ⟨ps₀, is₀, hps, his, hT⟩ := ht.ind_inv
    have h₂p p := (hps p).trans (ihps p hΓ hc (hps p).right)
    have h₂i i := (his i).trans (ihis i hΓ hc (his i).right)
    exact hT.symm.conv ((Defeq.indDF hps his).symm.trans (.indDF h₂p h₂i))
  | ctor _ _ _ ihps ihfds ihrf =>
    intro hΓ hc T ht
    obtain ⟨ps₀, fds₀, rf₀, hps, hfds, hrf, -, hT⟩ := ht.ctor_inv
    have h₂p p := (hps p).trans (ihps p hΓ hc (hps p).right)
    have h₂f f := (hfds f).trans (ihfds f hΓ hc (hfds f).right)
    have h₂r f := (hrf f).trans (ihrf f hΓ hc (hrf f).right)
    exact hT.symm.conv ((ctor_defeq hE hps hfds hrf).symm.trans (ctor_defeq hE h₂p h₂f h₂r))
  | recr _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    intro hΓ hc T ht
    obtain ⟨ps₀, ms₀, mins₀, is₀, maj₀, hallow, hps, hms, hmins, his, hmaj, hres, hT⟩ :=
      ht.recr_inv
    have h₂p p := (hps p).trans (ihps p hΓ hc (hps p).right)
    have h₂m t := (hms t).trans (ihms t hΓ hc (hms t).right)
    have h₂n t c := (hmins t c).trans (ihmins t c hΓ hc (hmins t c).right)
    have h₂i i := (his i).trans (ihis i hΓ hc (his i).right)
    have h₂j := hmaj.trans (ihmaj hΓ hc hmaj.right)
    exact hT.symm.conv ((Defeq.recrDF hallow hps hms hmins his hmaj hres).symm.trans
      (.recrDF hallow h₂p h₂m h₂n h₂i h₂j
        ((hE.entryWF _).block.motiveResult_congr hΓ h₂p h₂m h₂i h₂j)))
  | quot _ _ ihα ihr =>
    intro hΓ hc T ht
    obtain ⟨hα, hr⟩ := ht.quot_formation_inv
    exact ht.quot_inv.symm.conv (.quotDF (ihα hΓ hc hα) (ihr hΓ hc hr))
  | quotMk _ _ _ ihα ihr iha =>
    intro hΓ hc T ht
    obtain ⟨α₀, r₀, a₀, hα, hr, ha, hT⟩ := ht.quotMk_prem
    have h₂α := hα.trans (ihα hΓ hc hα.right)
    have h₂r := hr.trans (ihr hΓ hc hr.right)
    have h₂a := ha.trans (iha hΓ hc ha.right)
    exact hT.symm.conv ((Defeq.quotMkDF hα hr ha).symm.trans (.quotMkDF h₂α h₂r h₂a))
  | quotLift _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    intro hΓ hc T ht
    obtain ⟨α₀, r₀, β₀, f₀, h₀, a₀, hα, hr, hβ, hf, hh, ha, hT⟩ := ht.quotLift_prem
    have h₂α := hα.trans (ihα hΓ hc hα.right)
    have h₂r := hr.trans (ihr hΓ hc hr.right)
    have h₂β := hβ.trans (ihβ hΓ hc hβ.right)
    have h₂f := hf.trans (ihf hΓ hc hf.right)
    have h₂h := hh.trans (ihh hΓ hc hh.right)
    have h₂a := ha.trans (iha hΓ hc ha.right)
    exact hT.symm.conv ((Defeq.quotLiftDF hα hr hβ hf hh ha).symm.trans
      (.quotLiftDF h₂α h₂r h₂β h₂f h₂h h₂a))
  | quotInd _ _ _ _ _ ihα ihr ihβ ihf iha =>
    intro hΓ hc T ht
    obtain ⟨α₀, r₀, β₀, f₀, a₀, hα, hr, hβ, hf, ha, hres, hT⟩ := ht.quotInd_prem
    have h₁β := ihβ hΓ hc hβ.right
    have h₁a := iha hΓ hc ha.right
    have h₂α := hα.trans (ihα hΓ hc hα.right)
    have h₂r := hr.trans (ihr hΓ hc hr.right)
    have h₂f := hf.trans (ihf hΓ hc hf.right)
    have happ : E[_] ⊢ .app _ _ ≡ .app _ _ : .prop :=
      Defeq.appDF (Defeq.quotDF hα.left hr.left) .sortDF h₁β h₁a (by simpa using .sortDF)
    exact hT.symm.conv ((Defeq.quotIndDF hα hr hβ hf ha hres).symm.trans
      (.quotIndDF h₂α h₂r (hβ.trans h₁β) h₂f (ha.trans h₁a) (hres.trans happ)))
  | projStruct hP | projProof hP => exact absurd hP hnP

/-- Weakening of both contexts at level `cut`. Reference: `Defeq.wkFrom`
(`ML Typing/Substitution.lean:122`). -/
theorem wkFrom {cut : Nat} {Γ₀₁ Γ₀₂ : Ctx ζ ℓ 0 cut} (A₁ A₂ : Expr ζ ℓ cut) {n : Nat}
    {Δ₁ Δ₂ : Ctx ζ ℓ cut n} {t₁ t₂ : Expr ζ ℓ n} (h : DCong E P (Γ₀₁ ++ Δ₁) (Γ₀₂ ++ Δ₂) t₁ t₂) :
    DCong E P (Γ₀₁.insert A₁ Δ₁) (Γ₀₂.insert A₂ Δ₂) (t₁.wkFrom cut) (t₂.wkFrom cut) := by
  generalize hΓ₁ : Γ₀₁ ++ Δ₁ = Γ₁ at h
  generalize hΓ₂ : Γ₀₂ ++ Δ₂ = Γ₂ at h
  induction h with
  | refl => exact .refl
  | leaf h => subst hΓ₁; exact .leaf (Defeq.wkFrom Γ₀₁ Δ₁ A₁ h)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂)
  | @lam _ _ _ A₁' A₂' _ _ _ _ ih₁ ih₂ =>
    rw [Expr.wkFrom_lam Δ₁.le, Expr.wkFrom_lam Δ₁.le]
    exact .lam (ih₁ hΓ₁ hΓ₂) (ih₂ (Δ₁ := Δ₁.snoc A₁') (Δ₂ := Δ₂.snoc A₂') (by rw [← hΓ₁]; rfl)
      (by rw [← hΓ₂]; rfl))
  | @forallE _ _ _ A₁' A₂' _ _ _ _ ih₁ ih₂ =>
    rw [Expr.wkFrom_forallE Δ₁.le, Expr.wkFrom_forallE Δ₁.le]
    exact .forallE (ih₁ hΓ₁ hΓ₂) (ih₂ (Δ₁ := Δ₁.snoc A₁') (Δ₂ := Δ₂.snoc A₂') (by rw [← hΓ₁]; rfl)
      (by rw [← hΓ₂]; rfl))
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    rw [Expr.wkFrom_letE Δ₁.le, Expr.wkFrom_letE Δ₁.le]
    have h₃ := ih₃ hΓ₁ hΓ₂
    rw [Expr.inst_wkFrom Δ₁.le, Expr.inst_wkFrom Δ₁.le] at h₃
    exact .letE (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂) h₃
  | ind _ _ ih₁ ih₂ => exact .ind (ih₁ · hΓ₁ hΓ₂) (ih₂ · hΓ₁ hΓ₂)
  | ctor _ _ _ ih₁ ih₂ ih₃ => exact .ctor (ih₁ · hΓ₁ hΓ₂) (ih₂ · hΓ₁ hΓ₂) (ih₃ · hΓ₁ hΓ₂)
  | recr _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    exact .recr (ih₁ · hΓ₁ hΓ₂) (ih₂ · hΓ₁ hΓ₂) (ih₃ · · hΓ₁ hΓ₂) (ih₄ · hΓ₁ hΓ₂) (ih₅ hΓ₁ hΓ₂)
  | quot _ _ ih₁ ih₂ => exact .quot (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂)
  | quotMk _ _ _ ih₁ ih₂ ih₃ => exact .quotMk (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂) (ih₃ hΓ₁ hΓ₂)
  | quotLift _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact .quotLift (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂) (ih₃ hΓ₁ hΓ₂) (ih₄ hΓ₁ hΓ₂) (ih₅ hΓ₁ hΓ₂)
      (ih₆ hΓ₁ hΓ₂)
  | quotInd _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    exact .quotInd (ih₁ hΓ₁ hΓ₂) (ih₂ hΓ₁ hΓ₂) (ih₃ hΓ₁ hΓ₂) (ih₄ hΓ₁ hΓ₂) (ih₅ hΓ₁ hΓ₂)
  | projStruct hP h₁ h₂ f₁ f₂ hf _ ih =>
    subst hΓ₁ hΓ₂
    rw [Inductive.IsStructure.projTerm_wkFrom, Inductive.IsStructure.projTerm_wkFrom]
    exact .projStruct hP h₁ h₂ f₁ f₂ hf (ih rfl rfl)
  | projProof hP _ ih =>
    subst hΓ₁ hΓ₂
    rw [Expr.wkFrom_eq_subst, projProofTerm_subst, Expr.wkFrom_eq_subst, projProofTerm_subst]
    simp only [← Expr.wkFrom_eq_subst]
    exact .projProof hP (ih rfl rfl)

/-- Weakening by one variable. -/
theorem wk {n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} (A₁ A₂ : Expr ζ ℓ n) {t₁ t₂ : Expr ζ ℓ n}
    (h : DCong E P Γ₁ Γ₂ t₁ t₂) : DCong E P (Γ₁.snoc A₁) (Γ₂.snoc A₂) t₁.wk t₂.wk :=
  wkFrom (Δ₁ := .nil) (Δ₂ := .nil) A₁ A₂ h

/-- One term under pointwise congruent substitutions. Reference: `Defeq.substitution_congr`
(`ML Typing/Telescope.lean:111`). -/
theorem subst {m : Nat} (e : Expr ζ ℓ m) :
    ∀ {n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {σ₁ σ₂ : Subst ζ ℓ m n},
      (∀ v, DCong E P Γ₁ Γ₂ (σ₁ v) (σ₂ v)) → DCong E P Γ₁ Γ₂ (e.subst σ₁) (e.subst σ₂) := by
  have lift {m n : Nat} {Γ₁ Γ₂ : Ctx ζ ℓ 0 n} {σ₁ σ₂ : Subst ζ ℓ m n} (A₁ A₂ : Expr ζ ℓ n)
      (h : ∀ v, DCong E P Γ₁ Γ₂ (σ₁ v) (σ₂ v)) (v : Var (m + 1)) :
      DCong E P (Γ₁.snoc A₁) (Γ₂.snoc A₂) (σ₁.lift v) (σ₂.lift v) := by
    cases v using Fin.lastCases with
    | last => simp only [Subst.lift_last]; exact .refl
    | cast v => simp only [Subst.lift_castSucc]; exact wk A₁ A₂ (h v)
  induction e with
  | var x => intro _ _ _ _ _ h; exact h x
  | sort | const => intros; exact .refl
  | ind _ _ _ _ _ ih₁ ih₂ => intro _ _ _ _ _ h; exact .ind (ih₁ · h) (ih₂ · h)
  | ctor _ _ _ _ _ _ _ ih₁ ih₂ ih₃ => intro _ _ _ _ _ h; exact .ctor (ih₁ · h) (ih₂ · h) (ih₃ · h)
  | recr _ _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    intro _ _ _ _ _ h; exact .recr (ih₁ · h) (ih₂ · h) (ih₃ · · h) (ih₄ · h) (ih₅ h)
  | quot _ _ _ _ ih₁ ih₂ => intro _ _ _ _ _ h; exact .quot (ih₁ h) (ih₂ h)
  | quotMk _ _ _ _ _ ih₁ ih₂ ih₃ => intro _ _ _ _ _ h; exact .quotMk (ih₁ h) (ih₂ h) (ih₃ h)
  | quotLift _ _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    intro _ _ _ _ _ h; exact .quotLift (ih₁ h) (ih₂ h) (ih₃ h) (ih₄ h) (ih₅ h) (ih₆ h)
  | quotInd _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    intro _ _ _ _ _ h; exact .quotInd (ih₁ h) (ih₂ h) (ih₃ h) (ih₄ h) (ih₅ h)
  | app _ _ ih₁ ih₂ => intro _ _ _ _ _ h; exact .app (ih₁ h) (ih₂ h)
  | lam A _ ih₁ ih₂ =>
    intro _ _ _ _ _ h; exact .lam (ih₁ h) (ih₂ (lift (A.subst _) (A.subst _) h))
  | forallE A _ ih₁ ih₂ =>
    intro _ _ _ _ _ h; exact .forallE (ih₁ h) (ih₂ (lift (A.subst _) (A.subst _) h))
  | letE _ v _ ih₁ ih₂ ih₃ =>
    intro _ _ _ σ₁ σ₂ h
    refine .letE (ih₁ h) (ih₂ h) ?_
    rw [Expr.inst_subst_lift, Expr.inst_subst_lift]
    refine ih₃ fun w => ?_
    cases w using Fin.lastCases with
    | last => simpa [Subst.extend] using ih₂ h
    | cast w => simpa [Subst.extend] using h w

end DCong

end EraseProof
