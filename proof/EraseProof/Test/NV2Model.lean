import EraseProof.Test.NV2Data
import EraseProof.Test.NVPModel

/-!
# NV-2: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-2 (`Test/NV2Data.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `EC` with name table `BC`
(`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`, which is
typed (`he`, `hty`).

`tBlock` is `T`'s block (`inductive T : Prop | i`: one field-less constructor, in `Prop`, a
subsingleton). `wBlock ηB ηT` is `W`'s block over the heads of `B` and `T` (two constructors, the
second with the ordinary fields `b : B` and `h : T`, in `Type`). Typing facts are proved for any
environment whose heads hold these blocks. `EC` holds five entries: NV-1's block `B`, the blocks
`T` and `W`, and `W.casesOn` (a definition whose value is a saturated `recr`).
-/

open Lean Metalean

namespace EraseProof.Test.NV2

open EraseProof.Test.NV1 (tB cF cT mB mF mT bSig bCtorSig bBlock indB_typed ctorB_typed typed_of_eq
  var_of_get app_typed const_typed ζ1 E1 B1 wf1 henv1 P1 P1_eq tr_B tr_F tr_T notSpecial_bvar
  notSpecial_const trLevels_nil trLevel_u lu fin0_eq B_ind Bf_ctor Bt_ctor B_rec)
open EraseProof.Test.NVP (typed_of_eq' trLevels_one)

/-! ## The block of `T` -/

abbrev tSig : IndSig :=
  { nlevels := 0, nparams := 0, nsorts := 1, nindices _ := 0, nctors _ := 1, ctors _ _ := bCtorSig }

/-- `inductive T : Prop | i` as a Metalean block. -/
@[reducible] def tBlock {ζ : Sigs} : Inductive ζ tSig where
  params := .nil
  indices _ := .nil
  level := .zero
  ctors _ _ := { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                 targetIndices := fun i => Fin.elim0 i }

@[simp] theorem tBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@tBlock ζ₁).map pre = @tBlock ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  dsimp [Ctor.map]
  congr <;> funext i <;> exact Fin.elim0 i

theorem tBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E tBlock :=
  ⟨.nil, fun _ => .nil, fun _ _ =>
    { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
      targetIndices := fun i => Fin.elim0 i }⟩

section Terms
variable {ζ : Sigs} {ℓ n : Nat}

/-- `T`, `T.i`. -/
def mTT (η : Head ζ (.inductive tSig)) : Expr ζ ℓ n := .ind η 0 Fin.elim0 Fin.elim0 Fin.elim0
def mI (η : Head ζ (.inductive tSig)) : Expr ζ ℓ n :=
  .ctor η 0 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0

end Terms

section TGeneric
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive tSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem indT_typed (ht : (E.get η).block = tBlock) {s : Fin 1}
    {ls : Fin tSig.nlevels → Level ℓ} {ps : Fin tSig.nparams → Expr ζ ℓ n}
    {is : Fin (tSig.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ .ind η s ls ps is : .sort .zero := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := s) (ls := ls) (ps₁ := ps) (ps₂ := ps)
    (is₁ := is) (is₂ := is) (fun p => Fin.elim0 p) (fun i => Fin.elim0 i)
  rw [ht] at h
  simpa using h

theorem mTT_typed (ht : (E.get η).block = tBlock) : E[Γ] ⊢ mTT η : .sort .zero := indT_typed ht

theorem mI_typed (_ht : (E.get η).block = tBlock) : E[Γ] ⊢ mI η : mTT η := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := Fin.elim0)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert h using 2 <;> first | rfl | (simp only [mTT]; congr 1; funext i; exact i.elim0)

theorem tBlock_subsingleton {ζ : Sigs} {ℓ : Nat} {ls : Fin 0 → Level ℓ} {l : Level ℓ} :
    (tBlock (ζ := ζ)).RecAllowed ls l :=
  .inl ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩⟩

theorem largeElimT {ζ : Sigs} : (tBlock (ζ := ζ)).LargeElim :=
  fun _ => .subsingleton rfl (fun _ _ => Subsingleton.elim _ _)
    (fun _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩)

end TGeneric

/-! ## `T.rec`'s η-term (context `motive, i, t`) -/

section TRec
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive tSig)}

/-- `T → Sort l`. -/
def motT (η : Head ζ (.inductive tSig)) {ℓ n : Nat} (l : Level ℓ) : Expr ζ ℓ n :=
  .forallE (mTT η) (.sort l)

/-- `T.rec`'s type in Metalean. -/
def recTyTM (η : Head ζ (.inductive tSig)) : Expr ζ 1 0 :=
  .forallE (motT η lu) (.forallE (.app #0 (mI η)) (.forallE (mTT η) (.app #0 #2)))

/-- What `Frontend.recrTerm` builds for `T.rec`. -/
def recTermTM (η : Head ζ (.inductive tSig)) : Expr ζ 1 0 :=
  .lam (motT η lu) (.lam (.app #0 (mI η)) (.lam (mTT η)
    (.recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) (fun _ _ => #1) Fin.elim0 #2)))

theorem recrTerm_eqT {ls : Fin 0 → Level 1} :
    Frontend.recrTerm (tBlock (ζ := ζ)) η 0 ls lu (fun _ _ => []) = .ok (recTermTM η) := by
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have h : (match Frontend.recrTerm (tBlock (ζ := ζ)) η 0 Fin.elim0 lu (fun _ _ => []) with
      | .ok t => t | .error _ => .prop) = recTermTM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.recr _ _ _ _ _ _ _ _ _))) = _
    simp only [recTermTM, motT]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c; rfl)
      | (funext t; fin_cases t; rfl)
      | (funext i; exact i.elim0)
      | (nvsimp [Expr.wkN, mTT, mI]; done)
      | rfl
      | congr 1)
  rw [← h]
  rfl

theorem recTermTM_typed (ht : (E.get η).block = tBlock) :
    E[.nil] ⊢ recTermTM η : recTyTM η := by
  have h1 : E[(#t[motT η lu] : Ctx ζ 1 0 1)] ⊢ ok :=
    .snoc .nil ⟨_, .forallEDF (mTT_typed ht) .sortDF .sortDF⟩
  have hm1 : E[(#t[motT η lu] : Ctx ζ 1 0 1)] ⊢ #0 : motT η lu :=
    var_of_get h1 ⟨0, by decide⟩ (by nvsimp [motT, mTT])
  have h2 : E[(#t[motT η lu, .app #0 (mI η)] : Ctx ζ 1 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, .appDF (mTT_typed ht) .sortDF hm1 (mI_typed ht) .sortDF⟩
  have hΓ : E[(#t[motT η lu, .app #0 (mI η), mTT η] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, mTT_typed ht⟩
  have hm : E[(#t[motT η lu, .app #0 (mI η), mTT η] : Ctx ζ 1 0 3)] ⊢ #0 : motT η lu :=
    var_of_get hΓ ⟨0, by decide⟩ (by nvsimp [motT, mTT])
  have hbody : E[(#t[motT η lu, .app #0 (mI η), mTT η] : Ctx ζ 1 0 3)] ⊢
      .recr η 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) (fun _ _ => #1) Fin.elim0 #2 : .app #0 #2 := by
    have h := Defeq.recrDF (E := E) (Γ := #t[motT η lu, .app #0 (mI η), mTT η]) (η := η) (s := 0)
      (ls := Fin.elim0) (l := lu) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0)
      (ms₂ := fun _ => #0) (mins₁ := fun _ _ => #1) (mins₂ := fun _ _ => #1) (is₁ := Fin.elim0)
      (is₂ := Fin.elim0) (maj₁ := #2) (maj₂ := #2) (by rw [ht]; exact tBlock_subsingleton)
      (fun p => Fin.elim0 p) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [ht]; exact typed_of_eq hm (by nvsimp [motT, mTT])
    · intro s c; fin_cases s; fin_cases c; rw [ht]
      exact var_of_get hΓ ⟨1, by decide⟩ (by nvsimp [mI])
    · exact var_of_get hΓ ⟨2, by decide⟩ (by nvsimp [mTT])
    · exact .appDF (mTT_typed ht) .sortDF hm (var_of_get hΓ ⟨2, by decide⟩ (by nvsimp [mTT]))
        .sortDF
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[motT η lu, .app #0 (mI η), mTT η]) hΓ hbody

end TRec

/-! ## The block of `W` -/

abbrev wCtorSig (c : Fin 2) : CtorSig 1 :=
  { nfields := if c.val = 0 then 0 else 2, nrecFields := 0, recursiveArity := ![],
    recursiveTarget := ![] }
abbrev wSig : IndSig :=
  { nlevels := 0, nparams := 0, nsorts := 1, nindices _ := 0, nctors _ := 2,
    ctors _ c := wCtorSig c }

/-- `inductive W | n | s (b : B) (h : T)` as a Metalean block over the heads of `B` and `T`. -/
@[reducible] def wBlock {ζ : Sigs} (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig)) :
    Inductive ζ wSig where
  params := .nil
  indices _ := .nil
  level := .succ .zero
  ctors
    | _, ⟨0, _⟩ => { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                     targetIndices := fun i => Fin.elim0 i }
    | _, ⟨1, _⟩ => { ordinary := fun f => match f with
                       | ⟨0, _⟩ => ⟨mB ηB, .succ .zero⟩
                       | ⟨1, _⟩ => ⟨mTT ηT, .zero⟩,
                     recursive := fun f => Fin.elim0 f, targetIndices := fun i => Fin.elim0 i }

@[simp] theorem wBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) (ηB : Head ζ₁ (.inductive bSig))
    (ηT : Head ζ₁ (.inductive tSig)) :
    (wBlock ηB ηT).map pre = wBlock (ηB.map pre) (ηT.map pre) := by
  dsimp [Inductive.map]
  congr
  funext s c
  fin_cases s; fin_cases c
  · dsimp [Ctor.map]
    congr <;> funext i <;> exact Fin.elim0 i
  · dsimp [Ctor.map]
    congr
    · funext f; fin_cases f <;> (dsimp [Field.map]; congr 1; simp [mB, mTT, Expr.map]; try exprEq)
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i

section WTerms
variable {ζ : Sigs} {ℓ n : Nat}

/-- `W`, `W.n`, `W.s a h`. -/
def mW (η : Head ζ (.inductive wSig)) : Expr ζ ℓ n := .ind η 0 Fin.elim0 Fin.elim0 Fin.elim0
def mN (η : Head ζ (.inductive wSig)) : Expr ζ ℓ n :=
  .ctor η 0 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
def mS (η : Head ζ (.inductive wSig)) (a h : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 1 Fin.elim0 Fin.elim0 ![a, h] Fin.elim0

end WTerms

theorem levelOK_W {ζ : Sigs} {ηB : Head ζ (.inductive bSig)} {ηT : Head ζ (.inductive tSig)}
    {l : Level 0} (hl : l = .zero ∨ l = .succ .zero) : (wBlock ηB ηT).LevelOK l := by
  rcases hl with rfl | rfl <;> exact fun ν => by simp

theorem wBlock_wf {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)}
    {ηT : Head ζ (.inductive tSig)} (hb : (E.get ηB).block = bBlock)
    (ht : (E.get ηT).block = tBlock) : InductiveWF E (wBlock ηB ηT) :=
  ⟨.nil, fun _ => .nil, fun s c => by
    fin_cases s; fin_cases c
    · exact ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f, fun i => Fin.elim0 i⟩
    · refine ⟨fun f => ?_, fun f => Fin.elim0 f, fun i => Fin.elim0 i⟩
      fin_cases f
      · exact ⟨indB_typed hb, levelOK_W (.inr rfl)⟩
      · exact ⟨indT_typed ht, levelOK_W (.inl rfl)⟩⟩

section WGeneric
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηT : Head ζ (.inductive tSig)}
  {ηW : Head ζ (.inductive wSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem indW_typed (hw : (E.get ηW).block = wBlock ηB ηT) {s : Fin 1}
    {ls : Fin wSig.nlevels → Level ℓ} {ps : Fin wSig.nparams → Expr ζ ℓ n}
    {is : Fin (wSig.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ .ind ηW s ls ps is : .sort (.succ .zero) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := ηW) (s := s) (ls := ls) (ps₁ := ps) (ps₂ := ps)
    (is₁ := is) (is₂ := is) (fun p => Fin.elim0 p) (fun i => Fin.elim0 i)
  rw [hw] at h
  simpa using h

theorem mW_typed (hw : (E.get ηW).block = wBlock ηB ηT) : E[Γ] ⊢ mW ηW : .sort (.succ .zero) :=
  indW_typed hw

theorem mN_typed (_hw : (E.get ηW).block = wBlock ηB ηT) : E[Γ] ⊢ mN ηW : mW ηW := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := ηW) (s := 0) (c := 0) (ls := Fin.elim0)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert h using 2 <;> first | rfl | (simp only [mW]; congr 1; funext i; exact i.elim0)

theorem mS_typed (hw : (E.get ηW).block = wBlock ηB ηT) (hb : (E.get ηB).block = bBlock)
    (ht : (E.get ηT).block = tBlock) {a h : Expr ζ ℓ n} (ha : E[Γ] ⊢ a : mB ηB)
    (hh : E[Γ] ⊢ h : mTT ηT) : E[Γ] ⊢ mS ηW a h : mW ηW := by
  have hd := Defeq.ctorDF (E := E) (Γ := Γ) (η := ηW) (s := 0) (c := 1) (ls := Fin.elim0)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := ![a, h]) (fds₂ := ![a, h])
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := ![.succ .zero, .zero]) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p)
    (fun f => by
      rw [hw]; fin_cases f
      · convert ha using 1
        all_goals first | rfl | simp [mB, InstLevel.inst, Expr.instL, Expr.subst]
      · convert hh using 1
        all_goals first | rfl | simp [mTT, InstLevel.inst, Expr.instL, Expr.subst])
    (fun f => Fin.elim0 f)
    (fun f => by
      rw [hw]; fin_cases f
      · convert (indB_typed (Γ := Γ) (s := 0) (ls := Fin.elim0) (ps := Fin.elim0)
          (is := Fin.elim0) hb) using 1
        all_goals (unfold Ctor.ordinaryFieldExpr; simp [mB, InstLevel.inst, Expr.instL, Expr.subst])
      · convert (indT_typed (Γ := Γ) (s := 0) (ls := Fin.elim0) (ps := Fin.elim0)
          (is := Fin.elim0) ht) using 1
        all_goals (unfold Ctor.ordinaryFieldExpr; simp [mTT, InstLevel.inst, Expr.instL, Expr.subst]))
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  convert hd using 2 <;> first | rfl | (simp only [mW]; congr 1; funext i; exact i.elim0)

end WGeneric

/-- Unfold Metalean's telescopes, recursor types and weakenings on `W`'s terms; close equalities of
small `Fin` functions. -/
syntax (name := _wsimp) "wsimp" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| wsimp) => `(tactic| wsimp [Ctx.get])
  | `(tactic| wsimp [$ts,*]) => `(tactic| (nvsimp [$[$ts:ident],*, mW, mN, mS, mTT, mI,
      Inductive.paramType, Inductive.indexType, Ctx.proj, Ctor.targetIndex, Fin.fun_vecCons,
      Fin.fun_vecEmpty, Expr.wkN, funext_iff, Fin.forall_fin_two, Fin.forall_fin_one,
      Fin.sum_succ, Fin.sum_zero, Level.inst_param, Subst.liftN, Ren.wkFrom, Fin.castLE,
      Expr.apps_succ, CtorSig.fieldParams, Ctor.ordinaryFieldExpr, InstLevel.inst, Expr.instL,
      Ctor.ordinaryTeleAux, Ctx.instL, Tele.map, CtorSig.fieldOrdinary, Expr.boundVars] <;>
      finCongr))

/-! ## `W.s`'s η-term, `W.rec`'s η-term and `W.casesOn`'s value -/

section WRec
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηT : Head ζ (.inductive tSig)}
  {ηW : Head ζ (.inductive wSig)}

/-- `W.s`'s type `(b : B) → (h : T) → W` and η-term `fun b h => W.s b h` in Metalean. -/
def sTyM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 0 0 :=
  .forallE (mB ηB) (.forallE (mTT ηT) (mW ηW))
def sTermM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 0 0 :=
  .lam (mB ηB) (.lam (mTT ηT) (mS ηW #0 #1))

theorem ctorTerm_eqW (hw : (E.get ηW).block = wBlock ηB ηT) {ls : Fin 0 → Level 0} :
    Frontend.ctorTerm (E.get ηW).block ηW 0 1 ls [0, 1] = .ok (sTermM ηB ηT ηW) := by
  rw [hw]
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have : (match Frontend.ctorTerm (wBlock ηB ηT) ηW 0 1 Fin.elim0 [0, 1] with
      | .ok t => t | .error _ => .prop) = sTermM ηB ηT ηW := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ _) = _
    simp only [sTermM]
    wsimp
  rw [← this]
  rfl

theorem sTermM_typed (hw : (E.get ηW).block = wBlock ηB ηT) (hb : (E.get ηB).block = bBlock)
    (ht : (E.get ηT).block = tBlock) : E[.nil] ⊢ sTermM ηB ηT ηW : sTyM ηB ηT ηW := by
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hb⟩
  have h2 : E[(#t[mB ηB, mTT ηT] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mTT_typed ht⟩
  have hc : E[(#t[mB ηB, mTT ηT] : Ctx ζ 0 0 2)] ⊢ mS ηW #0 #1 : mW ηW :=
    mS_typed hw hb ht (var_of_get h2 ⟨0, by decide⟩ (by nvsimp))
      (var_of_get h2 ⟨1, by decide⟩ (by wsimp))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mB ηB, mTT ηT]) h2 hc

/-- `W → Sort l`. -/
def motW (ηW : Head ζ (.inductive wSig)) {ℓ n : Nat} (l : Level ℓ) : Expr ζ ℓ n :=
  .forallE (mW ηW) (.sort l)

/-- `(b : B) → (h : T) → motive (W.s b h)`, the motive variable 0, at depth 2. -/
def minS2 (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 2 :=
  .forallE (mB ηB) (.forallE (mTT ηT) (.app #0 (mS ηW #2 #3)))

/-- `W.rec`'s type in Metalean. -/
def recTyWM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 0 :=
  .forallE (motW ηW lu) (.forallE (.app #0 (mN ηW)) (.forallE (minS2 ηB ηT ηW)
    (.forallE (mW ηW) (.app #0 #3))))

/-- The minors of `W.rec`'s η-term (variables 1, 2). -/
def minsR {ζ : Sigs} : (t : Fin 1) → Fin (wSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => .var ⟨c.val + 1, by have h : c.val < 2 := c.isLt; omega⟩

/-- What `Frontend.recrTerm` builds for `W.rec`. -/
def recTermWM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 0 :=
  .lam (motW ηW lu) (.lam (.app #0 (mN ηW)) (.lam (minS2 ηB ηT ηW) (.lam (mW ηW)
    (.recr ηW 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsR Fin.elim0 #3))))

/-- `W`'s field orders: identities. -/
def ordersW : (s : Fin wSig.nsorts) → Fin (wSig.nctors s) → List Nat :=
  fun _ c => if c.val = 0 then [] else [0, 1]

set_option linter.unusedTactic false in
theorem recrTerm_eqW (hw : (E.get ηW).block = wBlock ηB ηT) {ls : Fin 0 → Level 1} :
    Frontend.recrTerm (E.get ηW).block ηW 0 ls lu ordersW = .ok (recTermWM ηB ηT ηW) := by
  rw [hw]
  have hls : ls = Fin.elim0 := funext fun i => i.elim0
  subst hls
  have : (match Frontend.recrTerm (wBlock ηB ηT) ηW 0 Fin.elim0 lu ordersW with
      | .ok t => t | .error _ => .prop) = recTermWM ηB ηT ηW := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.recr _ _ _ _ _ _ _ _ _)))) = _
    simp only [recTermWM, minS2, motW]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t; rfl)
      | (funext i; exact i.elim0)
      | (wsimp [Expr.wkN]; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

end WRec

section WTyping
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηT : Head ζ (.inductive tSig)}
  {ηW : Head ζ (.inductive wSig)}

theorem recAllowedW (hw : (E.get ηW).block = wBlock ηB ηT) {l : Level 1} :
    (E.get ηW).block.RecAllowed (Fin.elim0 : Fin 0 → Level 1) l := by
  rw [hw]
  exact Or.inr (Level.le_imax_iff.mpr fun ν h => by simp at h)

theorem largeElimW : (wBlock ηB ηT).LargeElim := fun _ => .large (le_refl _)

theorem motW_typed (hw : (E.get ηW).block = wBlock ηB ηT) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {l : Level ℓ} : E[Γ] ⊢ motW ηW l : .sort (.imax (.succ .zero) (.succ l)) :=
  .forallEDF (mW_typed hw) .sortDF .sortDF

theorem appMotW_typed (hw : (E.get ηW).block = wBlock ηB ηT) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {l : Level ℓ} {f a : Expr ζ ℓ n} (hf : E[Γ] ⊢ f : motW ηW l) (ha : E[Γ] ⊢ a : mW ηW) :
    E[Γ] ⊢ .app f a : .sort l :=
  .appDF (mW_typed hw) .sortDF hf ha .sortDF

variable (hw : (E.get ηW).block = wBlock ηB ηT) (hb : (E.get ηB).block = bBlock)
  (ht : (E.get ηT).block = tBlock)
include hw hb ht

omit hb ht in
/-- `motive, n` (`W.rec`'s first binders) is well formed. -/
theorem ΓR2_wf : E[(#t[motW ηW lu, .app #0 (mN ηW)] : Ctx ζ 1 0 2)] ⊢ ok := by
  have h1 : E[(#t[motW ηW lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motW_typed hw⟩
  exact .snoc h1 ⟨_, appMotW_typed hw (var_of_get h1 ⟨0, by decide⟩ (by wsimp [motW]))
    (mN_typed hw)⟩

theorem minS2_typed :
    E[(#t[motW ηW lu, .app #0 (mN ηW)] : Ctx ζ 1 0 2)] ⊢ minS2 ηB ηT ηW :
      .sort (.imax (.succ .zero) (.imax .zero lu)) := by
  have h2 := ΓR2_wf hw
  have h3 : E[(#t[motW ηW lu, .app #0 (mN ηW), mB ηB] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, indB_typed hb⟩
  have h4 : E[(#t[motW ηW lu, .app #0 (mN ηW), mB ηB, mTT ηT] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, mTT_typed ht⟩
  have hm : E[(#t[motW ηW lu, .app #0 (mN ηW), mB ηB, mTT ηT] : Ctx ζ 1 0 4)] ⊢
      .app #0 (mS ηW #2 #3) : .sort lu :=
    appMotW_typed hw (var_of_get h4 ⟨0, by decide⟩ (by wsimp [motW]))
      (mS_typed hw hb ht (var_of_get h4 ⟨2, by decide⟩ (by wsimp)) (var_of_get h4 ⟨3, by decide⟩ (by wsimp)))
  exact .forallEDF (indB_typed hb) (.forallEDF (mTT_typed ht) hm hm) (.forallEDF (mTT_typed ht) hm hm)

/-- `W.rec`'s binder context `motive n s t`. -/
def ΓRW (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Ctx ζ 1 0 4 :=
  #t[motW ηW lu, .app #0 (mN ηW), minS2 ηB ηT ηW, mW ηW]

theorem ΓRW_wf : E[ΓRW ηB ηT ηW] ⊢ ok :=
  .snoc (.snoc (ΓR2_wf hw) ⟨_, minS2_typed hw hb ht⟩) ⟨_, mW_typed hw⟩

theorem recTermWM_typed : E[.nil] ⊢ recTermWM ηB ηT ηW : recTyWM ηB ηT ηW := by
  have hΓ := ΓRW_wf hw hb ht
  have hbody : E[ΓRW ηB ηT ηW] ⊢ .recr ηW 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) minsR Fin.elim0 #3 :
      .app #0 #3 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓRW ηB ηT ηW) (η := ηW) (s := 0) (ls := Fin.elim0)
      (l := lu) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsR) (mins₂ := minsR) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (maj₁ := #3)
      (maj₂ := #3) (recAllowedW hw) (fun p => Fin.elim0 p) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hw]; exact var_of_get hΓ ⟨0, by decide⟩ (by wsimp [ΓRW, motW])
    · intro s c; fin_cases s; fin_cases c <;> rw [hw]
      · exact var_of_get hΓ ⟨1, by decide⟩ (by wsimp [ΓRW])
      · exact var_of_get hΓ ⟨2, by decide⟩ (by wsimp [ΓRW, minS2])
    · exact var_of_get hΓ ⟨3, by decide⟩ (by wsimp [ΓRW])
    · exact appMotW_typed hw (var_of_get hΓ ⟨0, by decide⟩ (by wsimp [ΓRW, motW]))
        (var_of_get hΓ ⟨3, by decide⟩ (by wsimp [ΓRW]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓRW ηB ηT ηW) hΓ hbody

/-- `(b : B) → (h : T) → motive (W.s b h)`, the motive variable 0, at depth 3. -/
def minS3 (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 3 :=
  .forallE (mB ηB) (.forallE (mTT ηT) (.app #0 (mS ηW #3 #4)))

/-- `W.casesOn`'s type in Metalean. -/
def casesOnTyWM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 0 :=
  .forallE (motW ηW lu) (.forallE (mW ηW) (.forallE (.app #0 (mN ηW))
    (.forallE (minS3 ηB ηT ηW) (.app #0 #1))))

/-- The minor `fun b h => s b h` of `W.casesOn`'s value. -/
def etaS (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig)) : Expr ζ 1 4 :=
  .lam (mB ηB) (.lam (mTT ηT) (.app (.app #3 #4) #5))

/-- The minors of `W.casesOn`'s value: `n` and `fun b h => s b h`. -/
def minsC (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig)) :
    (t : Fin 1) → Fin (wSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => if c.val = 0 then #2 else etaS ηB ηT

/-- The body of `W.casesOn`'s value. -/
def casesOnBodyW (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 4 :=
  .recr ηW 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) (minsC ηB ηT) Fin.elim0 #1

/-- `W.casesOn`'s value in Metalean: the saturated recursor. -/
def casesOnValWM (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Expr ζ 1 0 :=
  .lam (motW ηW lu) (.lam (mW ηW) (.lam (.app #0 (mN ηW)) (.lam (minS3 ηB ηT ηW)
    (casesOnBodyW ηB ηT ηW))))

/-- `W.casesOn`'s binder context `motive t n s`. -/
def ΓCW (ηB : Head ζ (.inductive bSig)) (ηT : Head ζ (.inductive tSig))
    (ηW : Head ζ (.inductive wSig)) : Ctx ζ 1 0 4 :=
  #t[motW ηW lu, mW ηW, .app #0 (mN ηW), minS3 ηB ηT ηW]

theorem ΓCW_wf : E[ΓCW ηB ηT ηW] ⊢ ok := by
  have h1 : E[(#t[motW ηW lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motW_typed hw⟩
  have h2 : E[(#t[motW ηW lu, mW ηW] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mW_typed hw⟩
  have h3 : E[(#t[motW ηW lu, mW ηW, .app #0 (mN ηW)] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, appMotW_typed hw (var_of_get h2 ⟨0, by decide⟩ (by wsimp [motW])) (mN_typed hw)⟩
  have h4 : E[(#t[motW ηW lu, mW ηW, .app #0 (mN ηW), mB ηB] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, indB_typed hb⟩
  have h5 : E[(#t[motW ηW lu, mW ηW, .app #0 (mN ηW), mB ηB, mTT ηT] : Ctx ζ 1 0 5)] ⊢ ok :=
    .snoc h4 ⟨_, mTT_typed ht⟩
  have hm : E[(#t[motW ηW lu, mW ηW, .app #0 (mN ηW), mB ηB, mTT ηT] : Ctx ζ 1 0 5)] ⊢
      .app #0 (mS ηW #3 #4) : .sort lu :=
    appMotW_typed hw (var_of_get h5 ⟨0, by decide⟩ (by wsimp [motW]))
      (mS_typed hw hb ht (var_of_get h5 ⟨3, by decide⟩ (by wsimp)) (var_of_get h5 ⟨4, by decide⟩ (by wsimp)))
  exact .snoc h3 ⟨_, .forallEDF (indB_typed hb) (.forallEDF (mTT_typed ht) hm hm)
    (.forallEDF (mTT_typed ht) hm hm)⟩

theorem etaS_typed :
    E[ΓCW ηB ηT ηW] ⊢ etaS ηB ηT : .forallE (mB ηB) (.forallE (mTT ηT) (.app #0 (mS ηW #4 #5))) := by
  have hΓ := ΓCW_wf hw hb ht
  have h5 : E[(ΓCW ηB ηT ηW).snoc (mB ηB)] ⊢ ok := .snoc hΓ ⟨_, indB_typed hb⟩
  have h6 : E[((ΓCW ηB ηT ηW).snoc (mB ηB)).snoc (mTT ηT)] ⊢ ok := .snoc h5 ⟨_, mTT_typed ht⟩
  have hs : E[((ΓCW ηB ηT ηW).snoc (mB ηB)).snoc (mTT ηT)] ⊢ #3 :
      .forallE (mB ηB) (.forallE (mTT ηT) (.app #0 (mS ηW #6 #7))) :=
    var_of_get h6 ⟨3, by decide⟩ (by wsimp [ΓCW, minS3])
  have h1 := typed_of_eq (app_typed hs (var_of_get h6 ⟨4, by decide⟩ (by wsimp)))
    (T' := .forallE (mTT ηT) (.app #0 (mS ηW #4 #6))) (by wsimp [Expr.inst])
  have h2 := typed_of_eq (app_typed h1 (var_of_get h6 ⟨5, by decide⟩ (by wsimp)))
    (T' := .app #0 (mS ηW #4 #5)) (by wsimp [Expr.inst])
  exact Ctx.lam_congr (Γ := ΓCW ηB ηT ηW) (Δ := #t[mB ηB, mTT ηT]) h6 h2

theorem casesOnValWM_typed : E[.nil] ⊢ casesOnValWM ηB ηT ηW : casesOnTyWM ηB ηT ηW := by
  have hΓ := ΓCW_wf hw hb ht
  have hbody : E[ΓCW ηB ηT ηW] ⊢ casesOnBodyW ηB ηT ηW : .app #0 #1 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓCW ηB ηT ηW) (η := ηW) (s := 0) (ls := Fin.elim0)
      (l := lu) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsC ηB ηT) (mins₂ := minsC ηB ηT) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #1) (maj₂ := #1) (recAllowedW hw) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hw]; exact var_of_get hΓ ⟨0, by decide⟩ (by wsimp [ΓCW, motW])
    · intro s c; fin_cases s; fin_cases c <;> rw [hw]
      · exact var_of_get hΓ ⟨2, by decide⟩ (by wsimp [ΓCW, minsC])
      · exact typed_of_eq (etaS_typed hw hb ht) (by wsimp [minsC])
    · exact var_of_get hΓ ⟨1, by decide⟩ (by wsimp [ΓCW])
    · exact appMotW_typed hw (var_of_get hΓ ⟨0, by decide⟩ (by wsimp [ΓCW, motW]))
        (var_of_get hΓ ⟨1, by decide⟩ (by wsimp [ΓCW]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓCW ηB ηT ηW) hΓ hbody

theorem casesOnTyWM_isType : E[.nil] ⊢ casesOnTyWM ηB ηT ηW typ :=
  (casesOnValWM_typed hw hb ht).regular

end WTyping

/-! ## The environments `ET = E1 + T`, `EW = ET + W`, `EC = EW + W.casesOn` -/

abbrev ζT : Sigs := ζ1.snoc (.inductive tSig)
abbrev ζW : Sigs := ζT.snoc (.inductive wSig)
abbrev ζC : Sigs := ζW.snoc (.const .def 1)

abbrev ηTT : Head ζT (.inductive tSig) := .here
abbrev ηBT : Head ζT (.inductive bSig) := .there .here
abbrev ηWW : Head ζW (.inductive wSig) := .here
abbrev ηTW : Head ζW (.inductive tSig) := .there .here
abbrev ηBW : Head ζW (.inductive bSig) := .there (.there .here)
abbrev ηCC : Head ζC (.const .def 1) := .here
abbrev ηWC : Head ζC (.inductive wSig) := .there .here
abbrev ηTC : Head ζC (.inductive tSig) := .there (.there .here)
abbrev ηBC : Head ζC (.inductive bSig) := .there (.there (.there .here))

def ET : Env ζT := E1.snoc (.inductive tBlock)
def EW : Env ζW := ET.snoc (.inductive (wBlock ηBT ηTT))
def EC : Env ζC := EW.snoc (.def (casesOnTyWM ηBW ηTW ηWW) (casesOnValWM ηBW ηTW ηWW))

theorem htT : (ET.get ηTT).block = tBlock := by simp! [ET, Env.get, Entry.block]
theorem hbT : (ET.get ηBT).block = bBlock := by simp! [ET, E1, Env.get, Entry.block]
theorem hwW : (EW.get ηWW).block = wBlock ηBW ηTW := by simp! [EW, Env.get, Entry.block]
theorem htW : (EW.get ηTW).block = tBlock := by simp! [EW, ET, Env.get, Entry.block]
theorem hbW : (EW.get ηBW).block = bBlock := by simp! [EW, ET, E1, Env.get, Entry.block]
theorem hwC : (EC.get ηWC).block = wBlock ηBC ηTC := by simp! [EC, EW, Env.get, Entry.block]
theorem htC : (EC.get ηTC).block = tBlock := by simp! [EC, EW, ET, Env.get, Entry.block]
theorem hbC : (EC.get ηBC).block = bBlock := by simp! [EC, EW, ET, E1, Env.get, Entry.block]

theorem wfT : EnvWF ET := .snoc wf1 (.inductive (tBlock_wf _))
theorem wfW : EnvWF EW := .snoc wfT (.inductive (wBlock_wf hbT htT))
theorem wfC : EnvWF EC :=
  .snoc wfW (.def (casesOnTyWM_isType hwW hbW htW) (casesOnValWM_typed hwW hbW htW))

theorem hcC : (EC.get ηCC).constType = casesOnTyWM ηBC ηTC ηWC := by
  simp! [EC, Env.get, Entry.constType, casesOnTyWM, motW, minS3, mW, mN, mS, mB, mTT, funext_iff,
    Fin.forall_fin_two, Fin.forall_fin_one]

/-! ## Name tables -/

def BT : Binds ζT := fun n =>
  if n = `T then some (.ind ηTT 0)
  else if n = `T.i then some (.ctor ηTT 0 0 [])
  else if n = `T.rec then some (.recr ηTT 0 [[[]]])
  else Binds.wk B1 n

def BW : Binds ζW := fun n =>
  if n = `W then some (.ind ηWW 0)
  else if n = `W.n then some (.ctor ηWW 0 0 [])
  else if n = `W.s then some (.ctor ηWW 0 1 [0, 1])
  else if n = `W.rec then some (.recr ηWW 0 [[[], [0, 1]]])
  else Binds.wk BT n

def BC : Binds ζC := (Binds.wk BW).set `W.casesOn (.const .here)

theorem BT_T : BT `T = some (.ind ηTT 0) := rfl
theorem BT_i : BT `T.i = some (.ctor ηTT 0 0 []) := rfl
theorem BT_rec : BT `T.rec = some (.recr ηTT 0 [[[]]]) := rfl
theorem BW_W : BW `W = some (.ind ηWW 0) := rfl
theorem BW_n : BW `W.n = some (.ctor ηWW 0 0 []) := rfl
theorem BW_s : BW `W.s = some (.ctor ηWW 0 1 [0, 1]) := rfl
theorem BW_rec : BW `W.rec = some (.recr ηWW 0 [[[], [0, 1]]]) := rfl
theorem BW_B : BW `B = some (.ind ηBW 0) := rfl
theorem BW_T : BW `T = some (.ind ηTW 0) := rfl
theorem BC_W : BC `W = some (.ind ηWC 0) := rfl
theorem BC_s : BC `W.s = some (.ctor ηWC 0 1 [0, 1]) := rfl
theorem BC_B : BC `B = some (.ind ηBC 0) := rfl
theorem BC_T : BC `T = some (.ind ηTC 0) := rfl
theorem BC_f : BC `B.f = some (.ctor ηBC 0 0 []) := rfl
theorem BC_t : BC `B.t = some (.ctor ηBC 0 1 []) := rfl
theorem BC_i : BC `T.i = some (.ctor ηTC 0 0 []) := rfl
theorem BC_casesOn : BC `W.casesOn = some (.const ηCC) := rfl

/-! ## Generic `TrM` facts for `T`'s and `W`'s constants -/

section TrGeneric
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

theorem tr_TT {η : Head ζ (.inductive tSig)} (h : B `T = some (.ind η 0)) :
    TrM E B lps Γ Δ tT (mTT η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := []) (ls := Fin.elim0)
      (ps := Fin.elim0) (is := Fin.elim0) (rest := []) trLevels_nil)

theorem tr_I {η : Head ζ (.inductive tSig)} (h : B `T.i = some (.ctor η 0 0 [])) :
    TrM E B lps Γ Δ cI (mI η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := []) (order := [])
      (ls := Fin.elim0) (fs := []) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := Fin.elim0) trLevels_nil rfl rfl (fun o => Fin.elim0 o))

theorem tr_W {η : Head ζ (.inductive wSig)} (h : B `W = some (.ind η 0)) :
    TrM E B lps Γ Δ tW (mW η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := []) (ls := Fin.elim0)
      (ps := Fin.elim0) (is := Fin.elim0) (rest := []) trLevels_nil)

theorem tr_N {η : Head ζ (.inductive wSig)} (h : B `W.n = some (.ctor η 0 0 [])) :
    TrM E B lps Γ Δ cN (mN η) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := []) (order := [])
      (ls := Fin.elim0) (fs := []) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := Fin.elim0) trLevels_nil rfl rfl (fun o => Fin.elim0 o))

/-- `W.s a h`. -/
theorem tr_S {η : Head ζ (.inductive wSig)} (h : B `W.s = some (.ctor η 0 1 [0, 1]))
    {a b : Lean.Expr} {a' b' : Metalean.Expr ζ lps.length n} (ha : TrM E B lps Γ Δ a a')
    (hb : TrM E B lps Γ Δ b b') :
    TrM E B lps Γ Δ (.app (.app cS a) b) (mS η a' b') :=
  TrM.special (as := [a, b]) (as' := [a', b']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> assumption)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 1) (us := []) (order := [0, 1])
      (ls := Fin.elim0) (fs := [a', b']) (rest := []) (ps := Fin.elim0) (fds := ![a', b'])
      (recFds := Fin.elim0) trLevels_nil rfl rfl
      (by intro o; fin_cases o <;> exact ⟨_, _, rfl, rfl, rfl⟩))

end TrGeneric

/-! ## `T`'s block in `ET`/`BT` -/

theorem tr_recTyT : TrM ET BT [`u] .nil [] recTyT (recTyTM ηTT) :=
  TrM.forallE (TrM.forallE (tr_TT BT_T) (TrM.sort trLevel_u))
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_I BT_i))
      (TrM.forallE (tr_TT BT_T) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_recT : TrM ET BT [`u] .nil [] (.const `T.rec [.param `u]) (recTermTM ηTT) := by
  refine TrM.special (as := []) (as' := []) BT_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := ET) (lps := [`u]) (η := ηTT) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) (fun _ _ => []) ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [htT]; exact largeElimT, _, rfl, trLevel_u⟩
  · intro t c; fin_cases t; fin_cases c; rfl
  · rw [htT]; exact recrTerm_eqT

def IsT : Fin tSig.nsorts → InductiveVal := fun _ => T_ind
def CsT : (s : Fin tSig.nsorts) → Fin (tSig.nctors s) → ConstructorVal := fun _ _ => Ti_ctor
def RsT : Fin tSig.nsorts → RecursorVal := fun _ => T_rec
def ordersT : (s : Fin tSig.nsorts) → Fin (tSig.nctors s) → List Nat := fun _ _ => []

theorem PT_eq : IndBlock.decls IsT CsT RsT = [.recInfo T_rec, .ctorInfo Ti_ctor, .inductInfo T_ind] :=
  rfl

theorem indBlockT : IndBlock ET BT ηTT [] IsT CsT RsT ordersT where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [htT]; exact largeElimT) h, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedT : ∀ ci ∈ IndBlock.decls IsT CsT RsT, ConstTyped ET BT ci := by
  rw [PT_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_recTyT, tr_recT, recTermTM_typed htT⟩
  · exact ⟨_, _, tr_TT BT_T, tr_I BT_i, mI_typed htT⟩
  · exact ⟨_, _, TrM.sort rfl, tr_TT BT_T, indT_typed htT⟩

theorem henvT : ProgEnv (IndBlock.decls IsT CsT RsT ++ P1) ζT ET BT :=
  ProgEnv.induct (I := tBlock) (lps := []) (orders := ordersT) henv1 (by decide)
    (by rw [PT_eq, P1_eq]; decide) (by decide)
    (fun n hn => by
      rw [PT_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `T.rec := h1
      have h2' : n ≠ `T.i := h2
      have h3' : n ≠ `T := h3
      simp [BT, h1', h2', h3'])
    indBlockT constTypedT

/-! ## `W`'s block in `EW`/`BW` -/

theorem tr_motTyW : TrM EW BW [`u] .nil [] motTyW (motW ηWW lu) :=
  TrM.forallE (tr_W BW_W) (TrM.sort trLevel_u)

theorem tr_recTyW : TrM EW BW [`u] .nil [] recTyW (recTyWM ηBW ηTW ηWW) :=
  TrM.forallE tr_motTyW
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_N BW_n))
      (TrM.forallE (TrM.forallE (tr_B BW_B) (TrM.forallE (tr_TT BW_T)
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S BW_s (TrM.bvar rfl) (TrM.bvar rfl)))))
        (TrM.forallE (tr_W BW_W) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_recW : TrM EW BW [`u] .nil [] (.const `W.rec [.param `u]) (recTermWM ηBW ηTW ηWW) := by
  refine TrM.special (as := []) (as' := []) BW_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := EW) (lps := [`u]) (η := ηWW) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) ordersW ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [hwW]; exact largeElimW, _, rfl, trLevel_u⟩
  · intro t c; fin_cases t; fin_cases c <;> rfl
  · exact recrTerm_eqW hwW

theorem tr_sTy : TrM EW BW [] .nil [] sTy (sTyM ηBW ηTW ηWW) :=
  TrM.forallE (tr_B BW_B) (TrM.forallE (tr_TT BW_T) (tr_W BW_W))

theorem tr_sConst : TrM EW BW [] .nil [] cS (sTermM ηBW ηTW ηWW) :=
  TrM.special (as := []) (as' := []) BW_s rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := ηWW) (s := 0) (c := 1) (order := [0, 1]) trLevels_nil
      (by decide) (ctorTerm_eqW hwW))

def IsW : Fin wSig.nsorts → InductiveVal := fun _ => W_ind
def CsW : (s : Fin wSig.nsorts) → Fin (wSig.nctors s) → ConstructorVal :=
  fun _ c => if c.val = 0 then Wn_ctor else Ws_ctor
def RsW : Fin wSig.nsorts → RecursorVal := fun _ => W_rec

theorem PW_eq : IndBlock.decls IsW CsW RsW =
    [.recInfo W_rec, .ctorInfo Wn_ctor, .ctorInfo Ws_ctor, .inductInfo W_ind] := rfl

theorem indBlockW : IndBlock EW BW ηWW [] IsW CsW RsW ordersW where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [0, 1], [], rfl, rfl, rfl, by decide, .nil,
        List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c <;> exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [hwW]; exact largeElimW) h, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c <;> rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedW : ∀ ci ∈ IndBlock.decls IsW CsW RsW, ConstTyped EW BW ci := by
  rw [PW_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨_, _, tr_recTyW, tr_recW, recTermWM_typed hwW hbW htW⟩
  · exact ⟨_, _, tr_W BW_W, tr_N BW_n, mN_typed hwW⟩
  · exact ⟨_, _, tr_sTy, tr_sConst, sTermM_typed hwW hbW htW⟩
  · exact ⟨_, _, TrM.sort rfl, tr_W BW_W, indW_typed hwW⟩

theorem henvW : ProgEnv (IndBlock.decls IsW CsW RsW ++ (IndBlock.decls IsT CsT RsT ++ P1)) ζW EW BW :=
  ProgEnv.induct (I := wBlock ηBT ηTT) (lps := []) (orders := ordersW) henvT (by decide)
    (by rw [PW_eq, PT_eq, P1_eq]; decide) (by decide)
    (fun n hn => by
      rw [PW_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      have h1' : n ≠ `W.rec := h1
      have h2' : n ≠ `W.n := h2
      have h3' : n ≠ `W.s := h3
      have h4' : n ≠ `W := h4
      simp [BW, h1', h2', h3', h4'])
    indBlockW constTypedW

/-! ## `W.casesOn` in `EW`/`BW` -/

theorem tr_casesOnTyW : TrM EW BW [`u] .nil [] casesOnTyW (casesOnTyWM ηBW ηTW ηWW) :=
  TrM.forallE tr_motTyW
    (TrM.forallE (tr_W BW_W)
      (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_N BW_n))
        (TrM.forallE (TrM.forallE (tr_B BW_B) (TrM.forallE (tr_TT BW_T)
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S BW_s (TrM.bvar rfl) (TrM.bvar rfl)))))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_casesOnValW : TrM EW BW [`u] .nil [] casesOnValW (casesOnValWM ηBW ηTW ηWW) := by
  have h : TrM EW BW [`u] .nil [] casesOnValW _ :=
    TrM.lam tr_motTyW (TrM.lam (tr_W BW_W)
      (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_N BW_n))
        (TrM.lam (TrM.forallE (tr_B BW_B) (TrM.forallE (tr_TT BW_T)
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S BW_s (TrM.bvar rfl) (TrM.bvar rfl)))))
          (TrM.special (c := `W.rec) (us := [.param `u])
            (as := [.bvar 3, .bvar 1,
              .lam `b tB (.lam `h tT (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default) .default,
              .bvar 2])
            (as' := [#0, #2, etaS ηBW ηTW, #1]) BW_rec rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
              · exact TrM.bvar rfl
              · exact TrM.bvar rfl
              · exact TrM.lam (tr_B BW_B) (TrM.lam (tr_TT BW_T) (TrM.app notSpecial_bvar
                  (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl)))
              · exact TrM.bvar rfl)
            (SatTr.recrSat (E := EW) (lps := [`u]) (η := ηWW) (s := 0) (us := [.param `u])
              (us' := []) (ls := Fin.elim0) (l := lu) ordersW ![#0, #2, etaS ηBW ηTW, #1] []
              (minsC ηBW ηTW) (Or.inl ⟨by rw [hwW]; exact largeElimW, _, rfl, trLevel_u⟩)
              trLevels_nil
              (by intro t c; fin_cases t; fin_cases c <;> rfl)
              (by
                intro t c; fin_cases t; fin_cases c <;>
                  simp [Frontend.wrapCase, Frontend.isIdentityOrder, ordersW] <;> rfl))))))
  convert h using 1
  simp only [casesOnValWM, casesOnBodyW]
  exprEq

theorem henvC : ProgEnv P ζC EC BC :=
  ProgEnv.defn henvW (by decide) (by decide) rfl rfl tr_casesOnTyW tr_casesOnValW

/-! ## The erased term in `EC`/`BC` -/

/-- `fun x : W => B`. -/
def mvW {n : Nat} : Expr ζC 0 n := .lam (mW ηWC) (mB ηBC)
/-- `W.s B.t T.i`. -/
def mjM {n : Nat} : Expr ζC 0 n := mS ηWC (mT ηBC) (mI ηTC)
/-- `fun b h => b`. -/
def altM {n : Nat} : Expr ζC 0 n := .lam (mB ηBC) (.lam (mTT ηTC) (.var ⟨n, by omega⟩))

/-- The erased term in Metalean. -/
def tE : Expr ζC 0 0 :=
  .app (.app (.app (.app (.const ηCC NV1.ls1) mvW) mjM) (mF ηBC)) altM

theorem tr_e : TrM EC BC [] .nil [] e tE :=
  TrM.app (notSpecial_const BC_casesOn ⟨_, rfl⟩)
    (TrM.app (notSpecial_const BC_casesOn ⟨_, rfl⟩)
      (TrM.app (notSpecial_const BC_casesOn ⟨_, rfl⟩)
        (TrM.app (notSpecial_const BC_casesOn ⟨_, rfl⟩) (TrM.const BC_casesOn NV1.trLevels_one)
          (TrM.lam (tr_W BC_W) (tr_B BC_B)))
        (tr_S BC_s (tr_T BC_t) (tr_I BC_i)))
      (tr_F BC_f))
    (TrM.lam (tr_B BC_B) (TrM.lam (tr_TT BC_T) (TrM.bvar rfl)))

section Input
variable {n : Nat} {Γ : Ctx ζC 0 0 n}

theorem mvW_beta {a : Expr ζC 0 n} (ha : EC[Γ] ⊢ a : mW ηWC) :
    EC[Γ] ⊢ .app mvW a ≡ mB ηBC : .sort (.succ .zero) := by
  have h := Defeq.beta (t := mW ηWC) (e' := mB ηBC) (t' := .sort (.succ .zero)) (mW_typed hwC)
    .sortDF (indB_typed hbC) ha .sortDF (by nvsimp [Expr.inst]; exact indB_typed hbC)
  convert h using 1 <;> nvsimp [Expr.inst, mvW]

theorem mvW_typed : EC[Γ] ⊢ mvW : motW ηWC (.succ .zero) :=
  .lamDF (mW_typed hwC) .sortDF .sortDF (indB_typed hbC) (indB_typed hbC)

theorem mjM_typed : EC[Γ] ⊢ mjM : mW ηWC :=
  mS_typed hwC hbC htC (ctorB_typed hbC) (mI_typed htC)

end Input

/-- `(b : B) → (h : T) → (fun x => B) (W.s b h) ≡ B → T → B`. -/
theorem altTy_defeq :
    EC[.nil] ⊢ .forallE (mB ηBC) (.forallE (mTT ηTC) (.app mvW (mS ηWC #0 #1))) ≡
      .forallE (mB ηBC) (.forallE (mTT ηTC) (mB ηBC)) :
      .sort (.imax (.succ .zero) (.imax .zero (.succ .zero))) := by
  have h1 : EC[(#t[mB ηBC] : Ctx ζC 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hbC⟩
  have h2 : EC[(#t[mB ηBC, mTT ηTC] : Ctx ζC 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mTT_typed htC⟩
  have hβ : EC[(#t[mB ηBC, mTT ηTC] : Ctx ζC 0 0 2)] ⊢ .app mvW (mS ηWC #0 #1) ≡ mB ηBC :
      .sort (.succ .zero) :=
    mvW_beta (mS_typed hwC hbC htC (var_of_get h2 ⟨0, by decide⟩ (by wsimp))
      (var_of_get h2 ⟨1, by decide⟩ (by wsimp)))
  have hin : EC[(#t[mB ηBC] : Ctx ζC 0 0 1)] ⊢ .forallE (mTT ηTC) (.app mvW (mS ηWC #0 #1)) ≡
      .forallE (mTT ηTC) (mB ηBC) : .sort (.imax .zero (.succ .zero)) :=
    .forallEDF (mTT_typed htC) hβ hβ
  exact .forallEDF (indB_typed hbC) hin hin

theorem altM_typed : EC[.nil] ⊢ altM : .forallE (mB ηBC) (.forallE (mTT ηTC) (mB ηBC)) := by
  have h1 : EC[(#t[mB ηBC] : Ctx ζC 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hbC⟩
  have h2 : EC[(#t[mB ηBC, mTT ηTC] : Ctx ζC 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mTT_typed htC⟩
  have hv : EC[(#t[mB ηBC, mTT ηTC] : Ctx ζC 0 0 2)] ⊢ #0 : mB ηBC :=
    var_of_get h2 ⟨0, by decide⟩ (by wsimp)
  have hin : EC[(#t[mB ηBC] : Ctx ζC 0 0 1)] ⊢ .lam (mTT ηTC) #0 : .forallE (mTT ηTC) (mB ηBC) :=
    .lamDF (mTT_typed htC) (indB_typed hbC) (indB_typed hbC) hv hv
  exact .lamDF (indB_typed hbC) (.forallEDF (mTT_typed htC) (indB_typed hbC) (indB_typed hbC))
    (.forallEDF (mTT_typed htC) (indB_typed hbC) (indB_typed hbC)) hin hin

theorem tE_typed : ∃ T, EC[.nil] ⊢ tE : T := by
  have h0 : EC[(.nil : Ctx ζC 0 0 0)] ⊢ .const ηCC NV1.ls1 :
      .forallE (motW ηWC (.succ .zero)) (.forallE (mW ηWC) (.forallE (.app #0 (mN ηWC))
        (.forallE (.forallE (mB ηBC) (.forallE (mTT ηTC) (.app #0 (mS ηWC #3 #4)))) (.app #0 #1)))) :=
    const_typed wfC ηCC NV1.ls1 (by rw [hcC]; wsimp [casesOnTyWM, motW, minS3, Expr.wkClosed, NV1.ls1])
  have h1 := typed_of_eq (app_typed h0 mvW_typed)
    (T' := .forallE (mW ηWC) (.forallE (.app mvW (mN ηWC))
      (.forallE (.forallE (mB ηBC) (.forallE (mTT ηTC) (.app mvW (mS ηWC #2 #3)))) (.app mvW #0))))
    (by wsimp [Expr.inst, mvW])
  have h2 := typed_of_eq (app_typed h1 mjM_typed)
    (T' := .forallE (.app mvW (mN ηWC))
      (.forallE (.forallE (mB ηBC) (.forallE (mTT ηTC) (.app mvW (mS ηWC #1 #2)))) (.app mvW mjM)))
    (by wsimp [Expr.inst, mvW, mjM])
  have hF : EC[(.nil : Ctx ζC 0 0 0)] ⊢ mF ηBC : .app mvW (mN ηWC) :=
    .defeqDF (mvW_beta (mN_typed hwC)).symm (ctorB_typed hbC)
  have h3 := typed_of_eq (app_typed h2 hF)
    (T' := .forallE (.forallE (mB ηBC) (.forallE (mTT ηTC) (.app mvW (mS ηWC #0 #1))))
      (.app mvW mjM))
    (by wsimp [Expr.inst, mvW, mjM])
  exact ⟨_, app_typed h3 (.defeqDF altTy_defeq.symm altM_typed)⟩

/-! ## The premises -/

/-- The Metalean environment of NV-2. -/
abbrev E : Env ζC := EC
/-- The name table of NV-2. -/
abbrev B : Binds ζC := BC

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζC E B := henvC

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wfC

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_e

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := tE_typed


end EraseProof.Test.NV2
