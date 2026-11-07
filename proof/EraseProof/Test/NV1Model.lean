import EraseProof.Test.NV1Data
import EraseProof.Spec
import Metalean.Typing.Env
import Metalean.Metatheory.Unique
import Metalean.Metatheory.Injectivity
import Mathlib.Tactic.FinCases

/-!
# NV-1: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-1 (`Test/NV1Data.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `E` with name table `B`
(`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`, which
is typed (`he`, `hty`).

`bBlock` is `B`'s block (`inductive B | f | t`: no parameters, no indices, two field-less
constructors, in `Type`). Typing facts are proved for any environment whose head `η` holds
`bBlock`, as `ML Builtin/Env.lean` does for `Eq` and `Iff`. `E` holds three entries: the block,
`B.casesOn` (a definition whose value is a saturated `recr`) and `B.neg`.
-/

open Lean Metalean

namespace EraseProof.Test.NV1

abbrev bCtorSig : CtorSig 1 :=
  { nfields := 0, nrecFields := 0, recursiveArity := ![], recursiveTarget := ![] }
abbrev bSig : IndSig :=
  { nlevels := 0, nparams := 0, nsorts := 1, nindices _ := 0, nctors _ := 2, ctors _ _ := bCtorSig }

/-- `inductive B | f | t` as a Metalean block. -/
@[reducible] def bBlock {ζ : Sigs} : Inductive ζ bSig where
  params := .nil
  indices _ := .nil
  level := .succ .zero
  ctors _ _ := { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                 targetIndices := fun i => Fin.elim0 i }

@[simp] theorem bBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@bBlock ζ₁).map pre = @bBlock ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  dsimp [Ctor.map]
  congr <;> funext i <;> exact Fin.elim0 i

theorem bBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E bBlock :=
  ⟨.nil, fun _ => .nil, fun _ _ =>
    { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
      targetIndices := fun i => Fin.elim0 i }⟩

/-! ## Terms -/

section Terms
variable {ζ : Sigs} (η : Head ζ (.inductive bSig)) {ℓ n : Nat}

/-- `B`. -/
def mB : Expr ζ ℓ n := .ind η 0 Fin.elim0 Fin.elim0 Fin.elim0
/-- `B.f`, `B.t`. -/
def mF : Expr ζ ℓ n := .ctor η 0 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
def mT : Expr ζ ℓ n := .ctor η 0 1 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
/-- `B → Sort u` at the level `l`. -/
def mMot (l : Level ℓ) : Expr ζ ℓ n := .forallE (mB η) (.sort l)

end Terms


/-- Functions out of `Fin 0` are equal (closes the side goals of the simp set below). -/
@[simp] theorem fin0_eq {α : Sort _} (f g : Fin 0 → α) : (f = g) = True := by
  simp only [eq_iff_iff, iff_true]; funext i; exact i.elim0

/-- Unfold Metalean's telescopes, recursor types and weakenings on `B`'s terms. -/
syntax (name := _nvsimp) "nvsimp" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| nvsimp) => `(tactic| nvsimp [Ctx.get])
  | `(tactic| nvsimp [$ts,*]) => `(tactic| simp [$[$ts:ident],*, Ctx.get, mMot, mB, mF, mT, Expr.wk, Expr.wkFrom,
    Inductive.motiveType, Inductive.motiveTele, Inductive.indexTele, Inductive.caseFnType,
    Inductive.caseTele, Inductive.caseType, Inductive.motiveResult, Ctor.fieldTele,
    Ctor.ordinaryFieldTele, Ctor.ordinaryFieldTeleAux, Ctor.recursiveFieldTeleAux, Ctor.ihTele,
    Ctx.substN, CtorSig.caseParams, CtorSig.caseOrdinary, CtorSig.caseRecursive, Expr.inst,
    Subst.lift, Subst.extend_apply, Subst.id])

/-- Application at a Π-type. -/
theorem app_typed {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {f a t : Expr ζ ℓ n}
    {t' : Expr ζ ℓ (n + 1)} (hf : E[Γ] ⊢ f : .forallE t t') (ha : E[Γ] ⊢ a : t) :
    E[Γ] ⊢ .app f a : t'.inst a := by
  have ⟨_, hT⟩ := hf.regular
  have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hT.forallE_inv
  exact .appDF ht ht' hf ha (ht'.inst_congr ha)

/-- A constant at its declared type. -/
theorem const_typed {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (hE : EnvWF E)
    {kind : ConstKind} {nl : Nat} (η : Head ζ (.const kind nl)) (ls : Fin nl → Level ℓ)
    {T : Expr ζ ℓ n} (h : (E.get η).constType{ls}.wkClosed = T) : E[Γ] ⊢ .const η ls : T := by
  have ⟨_, hT⟩ := EntryWF.constType (Γ := Γ) (hE.entryWF η) ls
  exact h ▸ Defeq.constDF hT

theorem typed_of_eq {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e T T' : Expr ζ ℓ n}
    (h : E[Γ] ⊢ e : T) (hT : T = T') : E[Γ] ⊢ e : T' :=
  hT ▸ h

theorem var_of_get {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (v : Var n) {T : Expr ζ ℓ n} (h : Γ.get v = T) : E[Γ] ⊢ .var v : T :=
  h ▸ hΓ.var v

section Generic
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive bSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem indB_typed (hb : (E.get η).block = bBlock) {s : Fin 1}
    {ls : Fin bSig.nlevels → Level ℓ} {ps : Fin bSig.nparams → Expr ζ ℓ n}
    {is : Fin (bSig.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ .ind η s ls ps is : .sort (.succ .zero) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := s) (ls := ls) (ps₁ := ps) (ps₂ := ps)
    (is₁ := is) (is₂ := is) (fun p => Fin.elim0 p) (fun i => Fin.elim0 i)
  rw [hb] at h
  simpa using h

theorem ctorB_typed (_hb : (E.get η).block = bBlock) {s : Fin 1} {c : Fin (bSig.nctors s)}
    {ls : Fin bSig.nlevels → Level ℓ} {ps : Fin bSig.nparams → Expr ζ ℓ n}
    {fds : Fin (bSig.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (bSig.ctors s c).nrecFields → Expr ζ ℓ n}
    {is : Fin (bSig.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ .ctor η s c ls ps fds recFds : .ind η s ls ps is := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := s) (c := c) (ls := ls)
    (ps₁ := ps) (ps₂ := ps) (fds₁ := fds) (fds₂ := fds) (recFds₁ := recFds) (recFds₂ := recFds)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert h using 2

/-- `B → Sort l` is a type. -/
theorem motB_typed (hb : (E.get η).block = bBlock) {l : Level ℓ} :
    E[Γ] ⊢ mMot η l : .sort (.imax (.succ .zero) (.succ l)) :=
  .forallEDF (indB_typed hb) .sortDF .sortDF

/-- `motive a : Sort l` for `motive : B → Sort l`, `a : B`. -/
theorem appMot_typed (hb : (E.get η).block = bBlock) {l : Level ℓ} {f a : Expr ζ ℓ n}
    (hf : E[Γ] ⊢ f : mMot η l) (ha : E[Γ] ⊢ a : mB η) : E[Γ] ⊢ .app f a : .sort l :=
  .appDF (indB_typed hb) .sortDF hf ha .sortDF

/-- Large elimination of `B` into `Sort l`. -/
theorem recAllowedB (hb : (E.get η).block = bBlock) {l : Level ℓ} :
    (E.get η).block.RecAllowed (Fin.elim0 : Fin 0 → Level ℓ) l := by
  rw [hb]
  exact Or.inr (Level.le_imax_iff.mpr fun ν h => by simp at h)

end Generic

/-! ## `B.casesOn`'s type and value (context `motive, t, f, t_1`) -/

section CasesOn
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive bSig)}

/-- The motive's level `u`. -/
abbrev lu : Level 1 := .param 0

/-- The minors `f`, `t_1` of the recursor in `B.casesOn`'s value (variables 2, 3). -/
def minsC {ζ : Sigs} : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => .var ⟨c.val + 2, by have h : c.val < 2 := c.isLt; omega⟩

/-- `B.casesOn`'s type in Metalean. -/
def casesOnTyM (η : Head ζ (.inductive bSig)) : Expr ζ 1 0 :=
  .forallE (mMot η lu) (.forallE (mB η) (.forallE (.app #0 (mF η))
    (.forallE (.app #0 (mT η)) (.app #0 #1))))

/-- `B.casesOn`'s value in Metalean: the saturated recursor. -/
def casesOnValM (η : Head ζ (.inductive bSig)) : Expr ζ 1 0 :=
  .lam (mMot η lu) (.lam (mB η) (.lam (.app #0 (mF η)) (.lam (.app #0 (mT η))
    (.recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsC Fin.elim0 #1))))

/-- The context `motive : B → Sort u, t : B, f : motive B.f, t_1 : motive B.t`. -/
def ΓC (η : Head ζ (.inductive bSig)) : Ctx ζ 1 0 4 :=
  #t[mMot η lu, mB η, .app #0 (mF η), .app #0 (mT η)]

theorem ΓC_wf (hb : (E.get η).block = bBlock) : E[ΓC η] ⊢ ok := by
  have h1 : E[#t[mMot η lu]] ⊢ ok := .snoc .nil ⟨_, motB_typed hb⟩
  have h2 : E[#t[mMot η lu, mB η]] ⊢ ok := .snoc h1 ⟨_, indB_typed hb⟩
  have h3 : E[#t[mMot η lu, mB η, .app #0 (mF η)]] ⊢ ok :=
    .snoc h2 ⟨_, appMot_typed (l := lu) hb (var_of_get h2 ⟨0, by decide⟩ (by nvsimp)) (ctorB_typed hb)⟩
  show E[#t[mMot η lu, mB η, .app #0 (mF η), .app #0 (mT η)]] ⊢ ok
  exact .snoc h3 ⟨_, appMot_typed (l := lu) hb (var_of_get h3 ⟨0, by decide⟩ (by nvsimp)) (ctorB_typed hb)⟩

theorem casesOnValM_typed (hb : (E.get η).block = bBlock) :
    E[.nil] ⊢ casesOnValM η : casesOnTyM η := by
  have hΓ := ΓC_wf hb
  have hbody : E[ΓC η] ⊢ .recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0)
      minsC Fin.elim0 #1 : .app #0 #1 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓC η) (η := η) (s := 0) (ls := Fin.elim0) (l := lu)
      (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsC) (mins₂ := minsC) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #1) (maj₂ := #1) (recAllowedB hb) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hb]; exact var_of_get hΓ ⟨0, by decide⟩ (by nvsimp [ΓC])
    · intro s c; fin_cases s; fin_cases c <;> rw [hb]
      · exact var_of_get hΓ ⟨2, by decide⟩ (by nvsimp [ΓC])
      · exact var_of_get hΓ ⟨3, by decide⟩ (by nvsimp [ΓC])
    · exact var_of_get hΓ ⟨1, by decide⟩ (by nvsimp [ΓC])
    · exact appMot_typed (l := lu) hb (var_of_get hΓ ⟨0, by decide⟩ (by nvsimp [ΓC]))
        (var_of_get hΓ ⟨1, by decide⟩ (by nvsimp [ΓC]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓC η) hΓ hbody

theorem casesOnTyM_isType (hb : (E.get η).block = bBlock) : E[.nil] ⊢ casesOnTyM η typ :=
  (casesOnValM_typed hb).regular

end CasesOn

/-! ## The recursor's η-term `recrTerm` (context `motive, f, t, t_1`) -/

section Rec
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive bSig)}

def minsR {ζ : Sigs} : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => .var ⟨c.val + 1, by have h : c.val < 2 := c.isLt; omega⟩

/-- `B.rec`'s type in Metalean. -/
def recTyM (η : Head ζ (.inductive bSig)) : Expr ζ 1 0 :=
  .forallE (mMot η lu) (.forallE (.app #0 (mF η)) (.forallE (.app #0 (mT η))
    (.forallE (mB η) (.app #0 #3))))

/-- What `Frontend.recrTerm` builds for `B.rec`. -/
def recTermM (η : Head ζ (.inductive bSig)) : Expr ζ 1 0 :=
  .lam (mMot η lu) (.lam (.app #0 (mF η)) (.lam (.app #0 (mT η)) (.lam (mB η)
    (.recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsR Fin.elim0 #3))))

/-- `recrTerm`'s result, by evaluation. -/
def recTermR (η : Head ζ (.inductive bSig)) : Expr ζ 1 0 :=
  match Frontend.recrTerm (bBlock (ζ := ζ)) η 0 Fin.elim0 lu (fun _ _ => []) with
  | .ok t => t
  | .error _ => .prop

theorem recrTerm_eq {ls : Fin 0 → Level 1} :
    Frontend.recrTerm (bBlock (ζ := ζ)) η 0 ls lu (fun _ _ => []) = .ok (recTermM η) := by
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have h : recTermR η = recTermM η := by
    show Expr.lam _ (Expr.lam _ (Expr.lam _ (Expr.lam _ (Expr.recr _ _ _ _ _ _ _ _ _)))) = _
    simp only [recTermM]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t; rfl)
      | (funext i; exact i.elim0)
      | (nvsimp [Expr.wkN]; done)
      | congr 1)
  rw [← h]
  rfl

def ΓR (η : Head ζ (.inductive bSig)) : Ctx ζ 1 0 4 :=
  #t[mMot η lu, .app #0 (mF η), .app #0 (mT η), mB η]

theorem ΓR_wf (hb : (E.get η).block = bBlock) : E[ΓR η] ⊢ ok := by
  have h1 : E[#t[mMot η lu]] ⊢ ok := .snoc .nil ⟨_, motB_typed hb⟩
  have h2 : E[#t[mMot η lu, .app #0 (mF η)]] ⊢ ok :=
    .snoc h1 ⟨_, appMot_typed (l := lu) hb (var_of_get h1 ⟨0, by decide⟩ (by nvsimp))
      (ctorB_typed hb)⟩
  have h3 : E[#t[mMot η lu, .app #0 (mF η), .app #0 (mT η)]] ⊢ ok :=
    .snoc h2 ⟨_, appMot_typed (l := lu) hb (var_of_get h2 ⟨0, by decide⟩ (by nvsimp))
      (ctorB_typed hb)⟩
  exact .snoc h3 ⟨_, indB_typed hb⟩

theorem recTermM_typed (hb : (E.get η).block = bBlock) :
    E[.nil] ⊢ recTermM η : recTyM η := by
  have hΓ := ΓR_wf hb
  have hbody : E[ΓR η] ⊢ .recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0)
      minsR Fin.elim0 #3 : .app #0 #3 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓR η) (η := η) (s := 0) (ls := Fin.elim0) (l := lu)
      (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsR) (mins₂ := minsR) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #3) (maj₂ := #3) (recAllowedB hb) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hb]; exact var_of_get hΓ ⟨0, by decide⟩ (by nvsimp [ΓR])
    · intro s c; fin_cases s; fin_cases c <;> rw [hb]
      · exact var_of_get hΓ ⟨1, by decide⟩ (by nvsimp [ΓR])
      · exact var_of_get hΓ ⟨2, by decide⟩ (by nvsimp [ΓR])
    · exact var_of_get hΓ ⟨3, by decide⟩ (by nvsimp [ΓR])
    · exact appMot_typed (l := lu) hb (var_of_get hΓ ⟨0, by decide⟩ (by nvsimp [ΓR]))
        (var_of_get hΓ ⟨3, by decide⟩ (by nvsimp [ΓR]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓR η) hΓ hbody

end Rec


/-! ## The environments `E1 = [B]`, `E2 = E1 + B.casesOn`, `E3 = E2 + neg` -/

abbrev ζ1 : Sigs := Sigs.nil.snoc (.inductive bSig)
abbrev ζ2 : Sigs := ζ1.snoc (.const .def 1)
abbrev ζ3 : Sigs := ζ2.snoc (.const .def 0)

/-- `B`'s head in each environment. -/
abbrev ηB1 : Head ζ1 (.inductive bSig) := .here
abbrev ηB2 : Head ζ2 (.inductive bSig) := .there .here
abbrev ηB3 : Head ζ3 (.inductive bSig) := .there (.there .here)
/-- `B.casesOn`'s head. -/
abbrev ηC2 : Head ζ2 (.const .def 1) := .here
/-- `neg`'s head. -/
abbrev ηN3 : Head ζ3 (.const .def 0) := .here

/-- `B.casesOn.{1}`'s level argument. -/
def ls1 : Fin 1 → Level 0 := fun _ => .succ .zero

/-- `neg`'s type and value in Metalean. -/
def negTyM : Expr ζ2 0 0 := .forallE (mB ηB2) (mB ηB2)
def negValM : Expr ζ2 0 0 :=
  .lam (mB ηB2) (.app (.app (.app (.app (.const ηC2 ls1) (.lam (mB ηB2) (mB ηB2))) #0)
    (mT ηB2)) (mF ηB2))

def E1 : Env ζ1 := Env.nil.snoc (.inductive bBlock)
def E2 : Env ζ2 := E1.snoc (.def (casesOnTyM ηB1) (casesOnValM ηB1))
def E3 : Env ζ3 := E2.snoc (.def negTyM negValM)

theorem hb1 : (E1.get ηB1).block = bBlock := by simp! [E1, Env.get, Entry.block]
theorem hb2 : (E2.get ηB2).block = bBlock := by simp! [E2, E1, Env.get, Entry.block]
theorem hb3 : (E3.get ηB3).block = bBlock := by simp! [E3, E2, E1, Env.get, Entry.block]

theorem wf1 : EnvWF E1 := .snoc .nil (.inductive (bBlock_wf _))

theorem wf2 : EnvWF E2 :=
  .snoc wf1 (.def (casesOnTyM_isType hb1) (casesOnValM_typed hb1))



/-! ## `neg`'s value is typed in `E2` -/

/-- `fun x : B => B`. -/
def mvB {ζ : Sigs} (η : Head ζ (.inductive bSig)) {n : Nat} : Expr ζ 0 n := .lam (mB η) (mB η)

/-- `B.casesOn.{1}`'s type, under the binder `b : B`. -/
def T0 : Expr ζ2 0 1 :=
  .forallE (mMot ηB2 (.succ .zero)) (.forallE (mB ηB2) (.forallE (.app #1 (mF ηB2))
    (.forallE (.app #1 (mT ηB2)) (.app #1 #2))))

theorem hc2 : (E2.get ηC2).constType = casesOnTyM ηB2 := by
  simp! [E2, Env.get, Entry.constType, casesOnTyM, mMot, mB, mF, mT]

/-- `(fun x : B => B) a ≡ B`. -/
theorem mvB_beta {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive bSig)} {n : Nat}
    {Γ : Ctx ζ 0 0 n} (hb : (E.get η).block = bBlock) {a : Expr ζ 0 n} (ha : E[Γ] ⊢ a : mB η) :
    E[Γ] ⊢ .app (mvB η) a ≡ mB η : .sort (.succ .zero) := by
  have h := Defeq.beta (t := mB η) (e' := mB η) (t' := .sort (.succ .zero)) (indB_typed hb)
    .sortDF (indB_typed hb) ha .sortDF (by nvsimp [Expr.inst]; exact indB_typed hb)
  convert h using 1 <;> nvsimp [Expr.inst, mvB]

theorem mvB_typed {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive bSig)} {n : Nat}
    {Γ : Ctx ζ 0 0 n} (hb : (E.get η).block = bBlock) :
    E[Γ] ⊢ mvB η : mMot η (.succ .zero) :=
  .lamDF (indB_typed hb) .sortDF .sortDF (indB_typed hb) (indB_typed hb)

theorem negValM_typed : E2[.nil] ⊢ negValM : negTyM := by
  have hΓ : E2[(#t[mB ηB2] : Ctx ζ2 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hb2⟩
  have hb : E2[#t[mB ηB2]] ⊢ #0 : mB ηB2 := var_of_get hΓ ⟨0, by decide⟩ (by nvsimp)
  have h0 : E2[#t[mB ηB2]] ⊢ .const ηC2 ls1 : T0 :=
    const_typed wf2 ηC2 ls1 (by rw [hc2]; nvsimp [T0, casesOnTyM, Expr.wkClosed, ls1])
  have h1 := app_typed h0 (mvB_typed hb2)
  have h2 := app_typed h1 (typed_of_eq hb (by nvsimp [Expr.inst]))
  have h2' := typed_of_eq h2 (T' := .forallE (.app (mvB ηB2) (mF ηB2))
    (.forallE (.app (mvB ηB2) (mT ηB2)) (.app (mvB ηB2) #0))) (by nvsimp [Expr.inst, mvB])
  have h3 := app_typed (a := mT ηB2) h2' (.defeqDF (mvB_beta hb2 (ctorB_typed hb2)).symm (ctorB_typed hb2))
  have h3' := typed_of_eq h3 (T' := .forallE (.app (mvB ηB2) (mT ηB2)) (.app (mvB ηB2) #0))
    (by nvsimp [Expr.inst, mvB])
  have h4 := app_typed (a := mF ηB2) h3' (.defeqDF (mvB_beta hb2 (ctorB_typed hb2)).symm (ctorB_typed hb2))
  have h4' := typed_of_eq h4 (T' := .app (mvB ηB2) #0) (by nvsimp [Expr.inst, mvB])
  have h5 := Defeq.defeqDF (mvB_beta hb2 hb) h4'
  exact .lamDF (indB_typed hb2) (indB_typed hb2) (indB_typed hb2) h5 h5

theorem wf3 : EnvWF E3 := .snoc wf2 (.def negValM_typed.regular negValM_typed)

/-! ## The erased term `neg B.f` is typed in `E3` -/

/-- `neg B.f` in Metalean. -/
def tE : Expr ζ3 0 0 := .app (.const ηN3 Fin.elim0) (mF ηB3)

theorem hn3 : (E3.get ηN3).constType = .forallE (mB ηB3) (mB ηB3) := by
  simp! [E3, Env.get, Entry.constType, negTyM, mB]

theorem tE_typed : E3[.nil] ⊢ tE : mB ηB3 := by
  have h0 : E3[(.nil : Ctx ζ3 0 0 0)] ⊢ .const ηN3 Fin.elim0 : .forallE (mB ηB3) (mB ηB3) :=
    const_typed wf3 ηN3 Fin.elim0 (by rw [hn3]; nvsimp [Expr.wkClosed])
  exact typed_of_eq (app_typed h0 (ctorB_typed hb3)) (by nvsimp)


/-! ## Name tables -/

/-- After `B`'s block. -/
def B1 : Binds ζ1 := fun n =>
  if n = `B then some (.ind ηB1 0)
  else if n = `B.f then some (.ctor ηB1 0 0 [])
  else if n = `B.t then some (.ctor ηB1 0 1 [])
  else if n = `B.rec then some (.recr ηB1 0 [[[], []]])
  else none

def B2 : Binds ζ2 := (Binds.wk B1).set `B.casesOn (.const .here)
def B3 : Binds ζ3 := (Binds.wk B2).set `B.neg (.const .here)

theorem B2_B : B2 `B = some (.ind ηB2 0) := rfl
theorem B2_f : B2 `B.f = some (.ctor ηB2 0 0 []) := rfl
theorem B2_t : B2 `B.t = some (.ctor ηB2 0 1 []) := rfl
theorem B2_casesOn : B2 `B.casesOn = some (.const ηC2) := rfl
theorem B3_B : B3 `B = some (.ind ηB3 0) := rfl
theorem B3_f : B3 `B.f = some (.ctor ηB3 0 0 []) := rfl
theorem B3_neg : B3 `B.neg = some (.const ηN3) := rfl

theorem trLevels_nil {lps : List Name} :
    TrLevels lps [] 0 = some (Fin.elim0 : Fin 0 → Metalean.Level lps.length) := by
  simp [TrLevels]

/-! ## Generic `TrM` facts for `B`'s constants -/

section Generic
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {η : Head ζ (.inductive bSig)} {lps : List Name}
  {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

theorem tr_B (h : B `B = some (.ind η 0)) : TrM E B lps Γ Δ tB (mB η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := []) (ls := Fin.elim0)
      (ps := Fin.elim0) (is := Fin.elim0) (rest := []) trLevels_nil)

theorem tr_ctor {c : Fin 2} {nm : Name} (h : B nm = some (.ctor η 0 c [])) :
    TrM E B lps Γ Δ (.const nm []) (.ctor η 0 c Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := c) (us := []) (order := [])
      (ls := Fin.elim0) (fs := []) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := Fin.elim0) trLevels_nil rfl rfl (fun o => Fin.elim0 o))

theorem tr_F (h : B `B.f = some (.ctor η 0 0 [])) : TrM E B lps Γ Δ cF (mF η) := tr_ctor h
theorem tr_T (h : B `B.t = some (.ctor η 0 1 [])) : TrM E B lps Γ Δ cT (mT η) := tr_ctor h

theorem notSpecial_bvar {i : Nat} : ¬ SpecialHead B (.bvar i) := by
  rintro ⟨c, us, b, h, -⟩; cases h

end Generic

theorem trLevel_u : TrLevel [`u] (.param `u) = some lu := rfl

theorem tr_mot {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {η : Head ζ (.inductive bSig)} {n : Nat}
    {Γ : Ctx ζ 1 0 n} {Δ : MLCtx ζ 1 n} (h : B `B = some (.ind η 0)) :
    TrM E B [`u] Γ Δ motTy (mMot η lu) :=
  TrM.forallE (tr_B h) (TrM.sort trLevel_u)

/-! ## The block's types (`ConstTyped` parts) in `E1`/`B1` -/

theorem B1_B : B1 `B = some (.ind ηB1 0) := rfl
theorem B1_f : B1 `B.f = some (.ctor ηB1 0 0 []) := rfl
theorem B1_t : B1 `B.t = some (.ctor ηB1 0 1 []) := rfl
theorem B1_rec : B1 `B.rec = some (.recr ηB1 0 [[[], []]]) := rfl

theorem tr_recTy : TrM E1 B1 [`u] .nil [] recTy (recTyM ηB1) :=
  TrM.forallE (tr_mot B1_B)
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F B1_f))
      (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T B1_t))
        (TrM.forallE (tr_B B1_B) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem largeElimB {ζ : Sigs} : (bBlock (ζ := ζ)).LargeElim :=
  fun _ => .large (le_refl _)

theorem tr_rec : TrM E1 B1 [`u] .nil [] (.const `B.rec [.param `u]) (recTermM ηB1) := by
  refine TrM.special (as := []) (as' := []) B1_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := E1) (lps := [`u]) (η := ηB1) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) (fun _ _ => []) ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [hb1]; exact largeElimB, _, rfl, trLevel_u⟩
  · intro t c; fin_cases t; fin_cases c <;> rfl
  · rw [hb1]; exact recrTerm_eq

/-! ## `B.casesOn` in `E1`/`B1` -/

theorem tr_casesOnTy : TrM E1 B1 [`u] .nil [] casesOnTy (casesOnTyM ηB1) :=
  TrM.forallE (tr_mot B1_B)
    (TrM.forallE (tr_B B1_B)
      (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F B1_f))
        (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T B1_t))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

/-- Close `Expr` equalities that differ in `Fin 0` functions and small `Fin` functions. -/
macro (name := _exprEq) "exprEq" : tactic => `(tactic| repeat' (first
    | (funext t c; fin_cases t; fin_cases c <;> rfl)
    | (funext t; fin_cases t; rfl)
    | (funext i; exact i.elim0)
    | (nvsimp [Expr.wkN]; done)
    | rfl
    | congr 1))

theorem tr_casesOnVal : TrM E1 B1 [`u] .nil [] casesOnVal (casesOnValM ηB1) := by
  have h : TrM E1 B1 [`u] .nil [] casesOnVal _ :=
    TrM.lam (tr_mot B1_B) (TrM.lam (tr_B B1_B)
      (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F B1_f))
        (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T B1_t))
          (TrM.special (c := `B.rec) (us := [.param `u])
            (as := [.bvar 3, .bvar 1, .bvar 0, .bvar 2]) (as' := [#0, #2, #3, #1]) B1_rec rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;>
                exact TrM.bvar rfl)
            (SatTr.recrSat (E := E1) (lps := [`u]) (η := ηB1) (s := 0) (us := [.param `u])
              (us' := []) (ls := Fin.elim0) (l := lu) (fun _ _ => []) ![#0, #2, #3, #1] []
              minsC (Or.inl ⟨by rw [hb1]; exact largeElimB, _, rfl, trLevel_u⟩) trLevels_nil
              (by intro t c; fin_cases t; fin_cases c <;> rfl)
              (by
                intro t c; fin_cases t; fin_cases c <;>
                  rfl))))))
  convert h using 1
  simp only [casesOnValM]
  exprEq

/-! ## `B.neg` in `E2`/`B2`, the erased term in `E3`/`B3` -/

theorem trLevels_one : TrLevels [] [.succ .zero] 1 = some ls1 :=
  congrArg some (funext fun i => by fin_cases i; rfl)

theorem notSpecial_const {ζ : Sigs} {B : Binds ζ} {c : Name} {kind : ConstKind} {nl : Nat}
    {η : Head ζ (.const kind nl)} (hc : B c = some (.const η)) {e : Expr}
    (he : ∃ us, e.getAppFn = .const c us) : ¬ SpecialHead B e := by
  rintro ⟨c', us', b, h1, h2, h3⟩
  obtain ⟨us, h⟩ := he
  rw [h] at h1; cases h1
  rw [hc] at h2; cases h2; cases h3

theorem tr_negTy : TrM E2 B2 [] .nil [] negTy negTyM := TrM.forallE (tr_B B2_B) (tr_B B2_B)

theorem tr_negVal : TrM E2 B2 [] .nil [] negVal negValM :=
  TrM.lam (tr_B B2_B)
    (TrM.app (notSpecial_const B2_casesOn ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B2_casesOn ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B2_casesOn ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B2_casesOn ⟨_, rfl⟩) (TrM.const B2_casesOn trLevels_one)
            (TrM.lam (tr_B B2_B) (tr_B B2_B)))
          (TrM.bvar rfl))
        (tr_T B2_t))
      (tr_F B2_f))

theorem tr_e : TrM E3 B3 [] .nil [] e tE :=
  TrM.app (notSpecial_const B3_neg ⟨_, rfl⟩) (TrM.const B3_neg trLevels_nil) (tr_F B3_f)

/-! ## `ProgEnv P ζ3 E3 B3` -/

def IsB : Fin bSig.nsorts → InductiveVal := fun _ => B_ind
def CsB : (s : Fin bSig.nsorts) → Fin (bSig.nctors s) → ConstructorVal :=
  fun _ c => if c.val = 0 then Bf_ctor else Bt_ctor
def RsB : Fin bSig.nsorts → RecursorVal := fun _ => B_rec
def ordersB : (s : Fin bSig.nsorts) → Fin (bSig.nctors s) → List Nat := fun _ _ => []

/-- The block's declarations, in `ProgEnv`'s order. -/
def P1 : List ConstantInfo := IndBlock.decls IsB CsB RsB

theorem P1_eq : P1 = [.recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind] :=
  rfl

theorem indBlock1 : IndBlock E1 B1 ηB1 [] IsB CsB RsB ordersB where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
  ctorType s c := by fin_cases s; fin_cases c <;> exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [hb1]; exact largeElimB) h, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  minors s t c := by fin_cases s; fin_cases t; fin_cases c <;> rfl
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTyped1 : ∀ ci ∈ P1, ConstTyped E1 B1 ci := by
  rw [P1_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨_, _, tr_recTy, tr_rec, recTermM_typed hb1⟩
  · exact ⟨_, _, tr_B B1_B, tr_F B1_f, ctorB_typed hb1⟩
  · exact ⟨_, _, tr_B B1_B, tr_T B1_t, ctorB_typed hb1⟩
  · exact ⟨_, _, TrM.sort rfl, tr_B B1_B, indB_typed hb1⟩

theorem henv1 : ProgEnv P1 ζ1 E1 B1 := by
  have h := ProgEnv.induct (P := []) (I := bBlock) (B' := B1) (lps := []) (Is := IsB) (Cs := CsB)
    (Rs := RsB) (orders := ordersB) .nil (by decide) (by simp [findDecl]) (by decide)
    (fun n hn => by
      have hl : (IndBlock.decls IsB CsB RsB).map (·.name) = [`B.rec, `B.f, `B.t, `B] := rfl
      rw [hl] at hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      simp [B1, Binds.wk, h1, h2, h3, h4])
    indBlock1 constTyped1
  rw [List.append_nil] at h
  exact h

theorem henv2 : ProgEnv (.defnInfo B_casesOn :: P1) ζ2 E2 B2 :=
  ProgEnv.defn henv1 (by decide) (by decide) rfl rfl tr_casesOnTy tr_casesOnVal

theorem henv3 : ProgEnv P ζ3 E3 B3 :=
  ProgEnv.defn henv2 (by decide) (by decide) rfl rfl tr_negTy tr_negVal


/-! ## The premises -/

/-- The Metalean environment of NV-1. -/
abbrev E : Env ζ3 := E3
/-- The name table of NV-1. -/
abbrev B : Binds ζ3 := B3

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζ3 E B := henv3

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wf3

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_e

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := ⟨_, tE_typed⟩

end EraseProof.Test.NV1
