import EraseProof.Test.NVRData
import EraseProof.Test.NV2Model

/-!
# NV-R: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-R (`Test/NVRData.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `EN` with name table `BN`
(`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`, which is
typed (`he`, `hty`).

`nBlock` is `N`'s block (`inductive N | z | s (n : N)`: no parameters, no indices, two
constructors, the second with one recursive field without arguments, in `Type`). Typing facts are
proved for any environment whose head holds `nBlock`. `EN` holds two entries: NV-1's block `B`
and the block `N`.
-/

open Lean Metalean

namespace EraseProof.Test.NVR

open EraseProof.Test.NV1 (tB cT mB mT bSig bBlock indB_typed ctorB_typed typed_of_eq var_of_get
  app_typed ζ1 E1 B1 wf1 henv1 P1 P1_eq tr_B tr_T notSpecial_bvar notSpecial_const trLevels_nil
  trLevel_u lu fin0_eq B_ind Bf_ctor Bt_ctor B_rec)
open EraseProof.Test.NVP (typed_of_eq' trLevels_one)

/-! ## The block of `N` -/

abbrev nCtorSig (c : Fin 2) : CtorSig 1 :=
  { nfields := 0, nrecFields := if c.val = 0 then 0 else 1, recursiveArity := fun _ => 0,
    recursiveTarget := fun _ => 0 }
abbrev nSig : IndSig :=
  { nlevels := 0, nparams := 0, nsorts := 1, nindices _ := 0, nctors _ := 2,
    ctors _ c := nCtorSig c }

/-- `inductive N | z | s (n : N)` as a Metalean block: the field of `N.s` is recursive, without
arguments, into `N` itself. -/
@[reducible] def nBlock {ζ : Sigs} : Inductive ζ nSig where
  params := .nil
  indices _ := .nil
  level := .succ .zero
  ctors
    | _, ⟨0, _⟩ => { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                     targetIndices := fun i => Fin.elim0 i }
    | _, ⟨1, _⟩ => { ordinary := fun f => Fin.elim0 f,
                     recursive := fun _ => ⟨.nil, fun i => Fin.elim0 i⟩,
                     targetIndices := fun i => Fin.elim0 i }

@[simp] theorem nBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@nBlock ζ₁).map pre = @nBlock ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  fin_cases s; fin_cases c
  · dsimp [Ctor.map]
    congr <;> funext i <;> exact Fin.elim0 i
  · dsimp [Ctor.map]
    congr
    · funext i; exact Fin.elim0 i
    · funext f; dsimp [RecField.map]; congr; funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i

theorem nBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E nBlock :=
  ⟨.nil, fun _ => .nil, fun s c => by
    fin_cases s; fin_cases c
    · exact ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f, fun i => Fin.elim0 i⟩
    · exact ⟨fun f => Fin.elim0 f, fun _ => ⟨.nil, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i⟩⟩

section Terms
variable {ζ : Sigs} {ℓ n : Nat}

/-- `N`, `N.z`, `N.s a`. -/
def mN (η : Head ζ (.inductive nSig)) : Expr ζ ℓ n := .ind η 0 Fin.elim0 Fin.elim0 Fin.elim0
def mZ (η : Head ζ (.inductive nSig)) : Expr ζ ℓ n :=
  .ctor η 0 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
def mS (η : Head ζ (.inductive nSig)) (a : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 1 Fin.elim0 Fin.elim0 Fin.elim0 ![a]

end Terms

section Generic
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive nSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem indN_typed (hn : (E.get η).block = nBlock) {s : Fin 1}
    {ls : Fin nSig.nlevels → Level ℓ} {ps : Fin nSig.nparams → Expr ζ ℓ n}
    {is : Fin (nSig.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ .ind η s ls ps is : .sort (.succ .zero) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := s) (ls := ls) (ps₁ := ps) (ps₂ := ps)
    (is₁ := is) (is₂ := is) (fun p => Fin.elim0 p) (fun i => Fin.elim0 i)
  rw [hn] at h
  simpa using h

theorem mN_typed (hn : (E.get η).block = nBlock) : E[Γ] ⊢ mN η : .sort (.succ .zero) :=
  indN_typed hn

theorem mZ_typed (_hn : (E.get η).block = nBlock) : E[Γ] ⊢ mZ η : mN η := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := Fin.elim0)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert h using 2 <;> first | rfl | (simp only [mN]; congr 1; funext i; exact i.elim0)

theorem mS_typed (hn : (E.get η).block = nBlock) {a : Expr ζ ℓ n} (ha : E[Γ] ⊢ a : mN η) :
    E[Γ] ⊢ mS η a : mN η := by
  have hd := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 1) (ls := Fin.elim0)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := ![a]) (recFds₂ := ![a])
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := ![.succ .zero])
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f)
    (fun f => by
      rw [hn]; fin_cases f
      refine typed_of_eq ha ?_
      show mN η = Expr.ind η 0 _ _ _
      simp only [mN]; congr 1; funext i; exact i.elim0)
    (fun f => Fin.elim0 f)
    (fun f => by
      rw [hn]; fin_cases f
      convert (indN_typed (Γ := Γ) (s := 0) (ls := Fin.elim0) (ps := Fin.elim0)
        (is := Fin.elim0) hn) using 2 <;>
        first | rfl | (show Expr.ind η 0 _ _ _ = _; congr 1; funext i; exact i.elim0))
    (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert hd using 2 <;> first | rfl | (simp only [mN]; congr 1; funext i; exact i.elim0)

end Generic

/-- Unfold Metalean's telescopes, recursor types and weakenings on `N`'s terms; close equalities of
small `Fin` functions. -/
syntax (name := _rsimp) "rsimp" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| rsimp) => `(tactic| rsimp [Ctx.get])
  | `(tactic| rsimp [$ts,*]) => `(tactic| (nvsimp [$[$ts:ident],*, mN, mZ, mS,
      Inductive.paramType, Inductive.indexType, Ctx.proj, Ctor.targetIndex, Fin.fun_vecCons,
      Fin.fun_vecEmpty, Expr.wkN, funext_iff, Fin.forall_fin_two, Fin.forall_fin_one,
      Fin.sum_succ, Fin.sum_zero, Level.inst_param, Subst.liftN, Ren.wkFrom, Fin.castLE,
      Expr.apps_succ, CtorSig.fieldParams, InstLevel.inst, Expr.instL, Ctx.instL, Tele.map,
      Expr.boundVars, Ctor.fieldTele, RecField.instantiatedType, RecField.instantiatedIndices,
      RecField.instantiatedTelescope, RecField.ihType, Ctor.ihType, Ctor.ihTypeWith,
      CtorSig.fieldRecursive, CtorSig.caseRecursive, Expr.applyBound] <;> finCongr))

/-! ## `N.s`'s and `N.rec`'s η-terms -/

section NRec
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive nSig)}

/-- `N.s`'s type `(n : N) → N` and η-term `fun n => N.s n` in Metalean. -/
def sTyM (η : Head ζ (.inductive nSig)) : Expr ζ 0 0 := .forallE (mN η) (mN η)
def sTermM (η : Head ζ (.inductive nSig)) : Expr ζ 0 0 := .lam (mN η) (mS η #0)

theorem ctorTerm_eqN (hn : (E.get η).block = nBlock) {ls : Fin 0 → Level 0} :
    Frontend.ctorTerm (E.get η).block η 0 1 ls [0] = .ok (sTermM η) := by
  rw [hn]
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have : (match Frontend.ctorTerm (nBlock (ζ := ζ)) η 0 1 Fin.elim0 [0] with
      | .ok t => t | .error _ => .prop) = sTermM η := by
    show Metalean.Expr.lam _ _ = _
    simp only [sTermM]
    rsimp
  rw [← this]
  rfl

/-- `N → Sort l`. -/
def motN (η : Head ζ (.inductive nSig)) {ℓ n : Nat} (l : Level ℓ) : Expr ζ ℓ n :=
  .forallE (mN η) (.sort l)

/-- `(n : N) → motive n → motive (N.s n)`, the motive variable 0, at depth 2. -/
def minSTyM (η : Head ζ (.inductive nSig)) : Expr ζ 1 2 :=
  .forallE (mN η) (.forallE (.app #0 #2) (.app #0 (mS η #2)))

/-- `N.rec`'s type in Metalean. -/
def recTyM (η : Head ζ (.inductive nSig)) : Expr ζ 1 0 :=
  .forallE (motN η lu) (.forallE (.app #0 (mZ η)) (.forallE (minSTyM η)
    (.forallE (mN η) (.app #0 #3))))

/-- The minors of `N.rec`'s η-term (variables 1, 2). -/
def minsR {ζ : Sigs} : (t : Fin 1) → Fin (nSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => .var ⟨c.val + 1, by have h : c.val < 2 := c.isLt; omega⟩

/-- What `Frontend.recrTerm` builds for `N.rec`. -/
def recTermM (η : Head ζ (.inductive nSig)) : Expr ζ 1 0 :=
  .lam (motN η lu) (.lam (.app #0 (mZ η)) (.lam (minSTyM η) (.lam (mN η)
    (.recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsR Fin.elim0 #3))))

/-- `N`'s field orders: identities. -/
def ordersN : (s : Fin nSig.nsorts) → Fin (nSig.nctors s) → List Nat :=
  fun _ c => if c.val = 0 then [] else [0]

set_option linter.unusedTactic false in
theorem recrTerm_eqN (hn : (E.get η).block = nBlock) {ls : Fin 0 → Level 1} :
    Frontend.recrTerm (E.get η).block η 0 ls lu ordersN = .ok (recTermM η) := by
  rw [hn]
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have : (match Frontend.recrTerm (nBlock (ζ := ζ)) η 0 Fin.elim0 lu ordersN with
      | .ok t => t | .error _ => .prop) = recTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.recr _ _ _ _ _ _ _ _ _)))) = _
    simp only [recTermM, minSTyM, motN]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t; rfl)
      | (funext i; exact i.elim0)
      | (rsimp [Expr.wkN]; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

theorem sTermM_typed (hn : (E.get η).block = nBlock) : E[.nil] ⊢ sTermM η : sTyM η := by
  have h1 : E[(#t[mN η] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN η]) h1
    (mS_typed hn (var_of_get h1 ⟨0, by decide⟩ (by rsimp)))

theorem recAllowedN (hn : (E.get η).block = nBlock) {ℓ : Nat} {l : Level ℓ} :
    (E.get η).block.RecAllowed (Fin.elim0 : Fin 0 → Level ℓ) l := by
  rw [hn]
  exact Or.inr (Level.le_imax_iff.mpr fun ν h => by simp at h)

theorem largeElimN : (nBlock (ζ := ζ)).LargeElim := fun _ => .large (le_refl _)

theorem motN_typed (hn : (E.get η).block = nBlock) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {l : Level ℓ} : E[Γ] ⊢ motN η l : .sort (.imax (.succ .zero) (.succ l)) :=
  .forallEDF (mN_typed hn) .sortDF .sortDF

theorem appMotN_typed (hn : (E.get η).block = nBlock) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {l : Level ℓ} {f a : Expr ζ ℓ n} (hf : E[Γ] ⊢ f : motN η l) (ha : E[Γ] ⊢ a : mN η) :
    E[Γ] ⊢ .app f a : .sort l :=
  .appDF (mN_typed hn) .sortDF hf ha .sortDF

/-- `motive, z` (`N.rec`'s first binders) is well formed. -/
theorem ΓR2_wf (hn : (E.get η).block = nBlock) :
    E[(#t[motN η lu, .app #0 (mZ η)] : Ctx ζ 1 0 2)] ⊢ ok := by
  have h1 : E[(#t[motN η lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motN_typed hn⟩
  exact .snoc h1 ⟨_, appMotN_typed hn (var_of_get h1 ⟨0, by decide⟩ (by rsimp [motN]))
    (mZ_typed hn)⟩

theorem minSTyM_typed (hn : (E.get η).block = nBlock) :
    E[(#t[motN η lu, .app #0 (mZ η)] : Ctx ζ 1 0 2)] ⊢ minSTyM η :
      .sort (.imax (.succ .zero) (.imax lu lu)) := by
  have h2 := ΓR2_wf hn
  have h3 : E[(#t[motN η lu, .app #0 (mZ η), mN η] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, mN_typed hn⟩
  have hm3 : E[(#t[motN η lu, .app #0 (mZ η), mN η] : Ctx ζ 1 0 3)] ⊢ .app #0 #2 : .sort lu :=
    appMotN_typed hn (var_of_get h3 ⟨0, by decide⟩ (by rsimp [motN]))
      (var_of_get h3 ⟨2, by decide⟩ (by rsimp))
  have h4 : E[(#t[motN η lu, .app #0 (mZ η), mN η, .app #0 #2] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hm3⟩
  have hm4 : E[(#t[motN η lu, .app #0 (mZ η), mN η, .app #0 #2] : Ctx ζ 1 0 4)] ⊢
      .app #0 (mS η #2) : .sort lu :=
    appMotN_typed hn (var_of_get h4 ⟨0, by decide⟩ (by rsimp [motN]))
      (mS_typed hn (var_of_get h4 ⟨2, by decide⟩ (by rsimp)))
  exact .forallEDF (mN_typed hn) (.forallEDF hm3 hm4 hm4) (.forallEDF hm3 hm4 hm4)

/-- `N.rec`'s binder context `motive z s t`. -/
def ΓR (η : Head ζ (.inductive nSig)) : Ctx ζ 1 0 4 :=
  #t[motN η lu, .app #0 (mZ η), minSTyM η, mN η]

theorem ΓR_wf (hn : (E.get η).block = nBlock) : E[ΓR η] ⊢ ok :=
  .snoc (.snoc (ΓR2_wf hn) ⟨_, minSTyM_typed hn⟩) ⟨_, mN_typed hn⟩

theorem recTermM_typed (hn : (E.get η).block = nBlock) : E[.nil] ⊢ recTermM η : recTyM η := by
  have hΓ := ΓR_wf hn
  have hbody : E[ΓR η] ⊢ .recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsR Fin.elim0 #3 :
      .app #0 #3 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓR η) (η := η) (s := 0) (ls := Fin.elim0)
      (l := lu) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsR) (mins₂ := minsR) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (maj₁ := #3)
      (maj₂ := #3) (recAllowedN hn) (fun p => Fin.elim0 p) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hn]; exact var_of_get hΓ ⟨0, by decide⟩ (by rsimp [ΓR, motN])
    · intro s c; fin_cases s; fin_cases c <;> rw [hn]
      · exact var_of_get hΓ ⟨1, by decide⟩ (by rsimp [ΓR])
      · exact var_of_get hΓ ⟨2, by decide⟩ (by rsimp [ΓR, minSTyM])
    · exact var_of_get hΓ ⟨3, by decide⟩ (by rsimp [ΓR])
    · exact appMotN_typed hn (var_of_get hΓ ⟨0, by decide⟩ (by rsimp [ΓR, motN]))
        (var_of_get hΓ ⟨3, by decide⟩ (by rsimp [ΓR]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓR η) hΓ hbody

end NRec

/-! ## The environment `EN = E1 + N` -/

abbrev ζN : Sigs := ζ1.snoc (.inductive nSig)

abbrev ηNN : Head ζN (.inductive nSig) := .here
abbrev ηBN : Head ζN (.inductive bSig) := .there .here

def EN : Env ζN := E1.snoc (.inductive nBlock)

theorem hnN : (EN.get ηNN).block = nBlock := by simp! [EN, Env.get, Entry.block]
theorem hbN : (EN.get ηBN).block = bBlock := by simp! [EN, E1, Env.get, Entry.block]

theorem wfN : EnvWF EN := .snoc wf1 (.inductive (nBlock_wf _))

/-! ## Name table -/

def BN : Binds ζN := fun n =>
  if n = `N then some (.ind ηNN 0)
  else if n = `N.z then some (.ctor ηNN 0 0 [])
  else if n = `N.s then some (.ctor ηNN 0 1 [0])
  else if n = `N.rec then some (.recr ηNN 0 [[[], [0]]])
  else Binds.wk B1 n

theorem BN_N : BN `N = some (.ind ηNN 0) := rfl
theorem BN_z : BN `N.z = some (.ctor ηNN 0 0 []) := rfl
theorem BN_s : BN `N.s = some (.ctor ηNN 0 1 [0]) := rfl
theorem BN_rec : BN `N.rec = some (.recr ηNN 0 [[[], [0]]]) := rfl
theorem BN_B : BN `B = some (.ind ηBN 0) := rfl
theorem BN_t : BN `B.t = some (.ctor ηBN 0 1 []) := rfl

/-! ## Generic `TrM` facts for `N`'s constants -/

section TrGeneric
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {η : Head ζ (.inductive nSig)}

theorem tr_N (h : B `N = some (.ind η 0)) : TrM E B lps Γ Δ tN (mN η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := []) (ls := Fin.elim0)
      (ps := Fin.elim0) (is := Fin.elim0) (rest := []) trLevels_nil)

theorem tr_Z (h : B `N.z = some (.ctor η 0 0 [])) : TrM E B lps Γ Δ cZ (mZ η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := []) (order := [])
      (ls := Fin.elim0) (fs := []) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := Fin.elim0) trLevels_nil rfl rfl (fun o => Fin.elim0 o))

/-- `N.s a`. -/
theorem tr_S (h : B `N.s = some (.ctor η 0 1 [0])) {a : Lean.Expr}
    {a' : Metalean.Expr ζ lps.length n} (ha : TrM E B lps Γ Δ a a') :
    TrM E B lps Γ Δ (.app cS a) (mS η a') :=
  TrM.special (as := [a]) (as' := [a']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | i <;> simp at h1 h2
      subst h1 h2
      exact ha)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 1) (us := []) (order := [0])
      (ls := Fin.elim0) (fs := [a']) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := ![a']) trLevels_nil rfl rfl
      (by intro o; fin_cases o; exact ⟨_, _, rfl, rfl, rfl⟩))

end TrGeneric

/-! ## `N`'s block in `EN`/`BN` -/

theorem tr_recTy : TrM EN BN [`u] .nil [] recTy (recTyM ηNN) :=
  TrM.forallE (TrM.forallE (tr_N BN_N) (TrM.sort trLevel_u))
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z BN_z))
      (TrM.forallE (TrM.forallE (tr_N BN_N) (TrM.forallE
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S BN_s (TrM.bvar rfl)))))
        (TrM.forallE (tr_N BN_N) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_rec : TrM EN BN [`u] .nil [] (.const `N.rec [.param `u]) (recTermM ηNN) := by
  refine TrM.special (as := []) (as' := []) BN_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := EN) (lps := [`u]) (η := ηNN) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) ordersN ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [hnN]; exact largeElimN, _, rfl, trLevel_u⟩
  · intro t c; fin_cases t; fin_cases c <;> rfl
  · exact recrTerm_eqN hnN

theorem tr_sTy : TrM EN BN [] .nil [] sTy (sTyM ηNN) := TrM.forallE (tr_N BN_N) (tr_N BN_N)

theorem tr_sConst : TrM EN BN [] .nil [] cS (sTermM ηNN) :=
  TrM.special (as := []) (as' := []) BN_s rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := ηNN) (s := 0) (c := 1) (order := [0]) trLevels_nil
      (by decide) (ctorTerm_eqN hnN))

def IsN : Fin nSig.nsorts → InductiveVal := fun _ => N_ind
def CsN : (s : Fin nSig.nsorts) → Fin (nSig.nctors s) → ConstructorVal :=
  fun _ c => if c.val = 0 then Nz_ctor else Ns_ctor
def RsN : Fin nSig.nsorts → RecursorVal := fun _ => N_rec

theorem PN_eq : IndBlock.decls IsN CsN RsN =
    [.recInfo N_rec, .ctorInfo Nz_ctor, .ctorInfo Ns_ctor, .inductInfo N_ind] := rfl

theorem indBlockN : IndBlock EN BN ηNN [] IsN CsN RsN ordersN where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [0], rfl, rfl, rfl, .nil, by decide,
        List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c <;> exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [hnN]; exact largeElimN) h, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c <;> rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedN : ∀ ci ∈ IndBlock.decls IsN CsN RsN, ConstTyped EN BN ci := by
  rw [PN_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨_, _, tr_recTy, tr_rec, recTermM_typed hnN⟩
  · exact ⟨_, _, tr_N BN_N, tr_Z BN_z, mZ_typed hnN⟩
  · exact ⟨_, _, tr_sTy, tr_sConst, sTermM_typed hnN⟩
  · exact ⟨_, _, TrM.sort rfl, tr_N BN_N, indN_typed hnN⟩

theorem henvN : ProgEnv P ζN EN BN :=
  ProgEnv.induct (I := nBlock) (lps := []) (orders := ordersN) henv1 (by decide)
    (by rw [PN_eq, P1_eq]; decide) (by decide)
    (fun n hn => by
      rw [PN_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      have h1' : n ≠ `N.rec := h1
      have h2' : n ≠ `N.z := h2
      have h3' : n ≠ `N.s := h3
      have h4' : n ≠ `N := h4
      simp [BN, h1', h2', h3', h4'])
    indBlockN constTypedN

/-! ## The erased term in `EN`/`BN` -/

/-- `fun x : N => B`. -/
def mvN {n : Nat} : Expr ζN 0 n := .lam (mN ηNN) (mB ηBN)
/-- `fun n (ih : B) => ih`. -/
def minSM : Expr ζN 0 0 := .lam (mN ηNN) (.lam (mB ηBN) #1)
/-- `N.s N.z`. -/
def mjM {n : Nat} : Expr ζN 0 n := mS ηNN (mZ ηNN)
/-- The minor premises `B.t` and `fun n ih => ih`. -/
def minsE : (t : Fin 1) → Fin (nSig.nctors t) → Expr ζN 0 0 :=
  fun _ c => if c.val = 0 then mT ηBN else minSM

/-- The erased term in Metalean: the saturated recursor. -/
def tE : Expr ζN 0 0 :=
  .recr ηNN 0 Fin.elim0 (.succ .zero) Fin.elim0 (fun _ => mvN) minsE Fin.elim0 mjM

theorem tr_e : TrM EN BN [] .nil [] e tE := by
  show TrM EN BN [] .nil [] (mkAppN (.const `N.rec [.succ .zero]) [motB, cT, minS, mj].toArray) tE
  have h : TrM EN BN [] .nil []
      (mkAppN (.const `N.rec [.succ .zero]) [motB, cT, minS, mj].toArray) _ :=
    TrM.special (c := `N.rec) (us := [.succ .zero]) (as := [motB, cT, minS, mj])
      (as' := ([mvN, mT ηBN, minSM, mjM] : List (Expr ζN 0 0))) BN_rec rfl rfl
      (by
        intro i a a' h1 h2
        rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
        · exact TrM.lam (tr_N BN_N) (tr_B BN_B)
        · exact tr_T BN_t
        · exact TrM.lam (tr_N BN_N) (TrM.lam (tr_B BN_B) (TrM.bvar rfl))
        · exact tr_S BN_s (tr_Z BN_z))
      (SatTr.recrSat (E := EN) (lps := []) (η := ηNN) (s := 0) (orders := [[[], [0]]])
        (us := [.succ .zero]) (us' := []) (ls := Fin.elim0) (l := .succ .zero) ordersN
        ![mvN, mT ηBN, minSM, mjM] [] minsE
        (Or.inl ⟨by rw [hnN]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
        (by intro t c; fin_cases t; fin_cases c <;> rfl)
        (by intro t c; fin_cases t; fin_cases c <;> rfl))
  convert h using 1
  simp only [tE]
  exprEq

section Input
variable {n : Nat} {Γ : Ctx ζN 0 0 n}

theorem mvN_beta {a : Expr ζN 0 n} (ha : EN[Γ] ⊢ a : mN ηNN) :
    EN[Γ] ⊢ .app mvN a ≡ mB ηBN : .sort (.succ .zero) := by
  have h := Defeq.beta (t := mN ηNN) (e' := mB ηBN) (t' := .sort (.succ .zero)) (mN_typed hnN)
    .sortDF (indB_typed hbN) ha .sortDF (by nvsimp [Expr.inst]; exact indB_typed hbN)
  convert h using 1 <;> nvsimp [Expr.inst, mvN]

theorem mvN_typed : EN[Γ] ⊢ mvN : motN ηNN (.succ .zero) :=
  .lamDF (mN_typed hnN) .sortDF .sortDF (indB_typed hbN) (indB_typed hbN)

theorem mjM_typed : EN[Γ] ⊢ mjM : mN ηNN := mS_typed hnN (mZ_typed hnN)

end Input

/-- `(n : N) → (fun x => B) n → (fun x => B) (N.s n) ≡ N → B → B`. -/
theorem minTy_defeq :
    EN[.nil] ⊢ .forallE (mN ηNN) (.forallE (.app mvN #0) (.app mvN (mS ηNN #0))) ≡
      .forallE (mN ηNN) (.forallE (mB ηBN) (mB ηBN)) :
      .sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
  have h1 : EN[(#t[mN ηNN] : Ctx ζN 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hnN⟩
  have hv : EN[(#t[mN ηNN] : Ctx ζN 0 0 1)] ⊢ #0 : mN ηNN := var_of_get h1 ⟨0, by decide⟩ (by rsimp)
  have hβ0 := mvN_beta hv
  have h2 : EN[(#t[mN ηNN, .app mvN #0] : Ctx ζN 0 0 2)] ⊢ ok := .snoc h1 ⟨_, hβ0.left⟩
  have h2' : EN[(#t[mN ηNN, mB ηBN] : Ctx ζN 0 0 2)] ⊢ ok := .snoc h1 ⟨_, indB_typed hbN⟩
  have hβ1 : EN[(#t[mN ηNN, .app mvN #0] : Ctx ζN 0 0 2)] ⊢ .app mvN (mS ηNN #0) ≡ mB ηBN :
      .sort (.succ .zero) :=
    mvN_beta (mS_typed hnN (var_of_get h2 ⟨0, by decide⟩ (by rsimp)))
  have hβ2 : EN[(#t[mN ηNN, mB ηBN] : Ctx ζN 0 0 2)] ⊢ .app mvN (mS ηNN #0) ≡ mB ηBN :
      .sort (.succ .zero) :=
    mvN_beta (mS_typed hnN (var_of_get h2' ⟨0, by decide⟩ (by rsimp)))
  have hin : EN[(#t[mN ηNN] : Ctx ζN 0 0 1)] ⊢ .forallE (.app mvN #0) (.app mvN (mS ηNN #0)) ≡
      .forallE (mB ηBN) (mB ηBN) : .sort (.imax (.succ .zero) (.succ .zero)) :=
    .forallEDF hβ0 hβ1 hβ2
  exact .forallEDF (mN_typed hnN) hin hin

theorem minSM_typed : EN[.nil] ⊢ minSM : .forallE (mN ηNN) (.forallE (mB ηBN) (mB ηBN)) := by
  have h1 : EN[(#t[mN ηNN] : Ctx ζN 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hnN⟩
  have h2 : EN[(#t[mN ηNN, mB ηBN] : Ctx ζN 0 0 2)] ⊢ ok := .snoc h1 ⟨_, indB_typed hbN⟩
  have hv : EN[(#t[mN ηNN, mB ηBN] : Ctx ζN 0 0 2)] ⊢ #1 : mB ηBN :=
    var_of_get h2 ⟨1, by decide⟩ (by rsimp)
  have hin : EN[(#t[mN ηNN] : Ctx ζN 0 0 1)] ⊢ .lam (mB ηBN) #1 : .forallE (mB ηBN) (mB ηBN) :=
    .lamDF (indB_typed hbN) (indB_typed hbN) (indB_typed hbN) hv hv
  exact .lamDF (mN_typed hnN) (.forallEDF (indB_typed hbN) (indB_typed hbN) (indB_typed hbN))
    (.forallEDF (indB_typed hbN) (indB_typed hbN) (indB_typed hbN)) hin hin

theorem tE_typed : EN[.nil] ⊢ tE : .app mvN mjM := by
  have h := Defeq.recrDF (E := EN) (Γ := .nil) (η := ηNN) (s := 0) (ls := Fin.elim0)
    (l := .succ .zero) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => mvN)
    (ms₂ := fun _ => mvN) (mins₁ := minsE) (mins₂ := minsE) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
    (maj₁ := mjM) (maj₂ := mjM) (recAllowedN hnN) (fun p => Fin.elim0 p) ?_ ?_
    (fun i => Fin.elim0 i) mjM_typed ?_
  · exact h
  · intro s; fin_cases s; rw [hnN]; exact typed_of_eq mvN_typed (by rsimp [motN])
  · intro s c; fin_cases s; fin_cases c <;> rw [hnN]
    · exact typed_of_eq (.defeqDF (mvN_beta (mZ_typed hnN)).symm (ctorB_typed hbN))
        (by rsimp [mvN])
    · exact typed_of_eq (.defeqDF minTy_defeq.symm minSM_typed) (by rsimp [mvN])
  · exact .appDF (mN_typed hnN) .sortDF mvN_typed mjM_typed .sortDF

/-! ## The premises -/

/-- The Metalean environment of NV-R. -/
abbrev E : Env ζN := EN
/-- The name table of NV-R. -/
abbrev B : Binds ζN := BN

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζN E B := henvN

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wfN

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_e

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := ⟨_, tE_typed⟩

end EraseProof.Test.NVR
