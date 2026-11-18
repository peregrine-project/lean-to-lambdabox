import EraseProof.Statements
import EraseProof.Test.NV2Data
import EraseProof.Test.NV1Run

/-!
# NV-2: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` holds on the program of `Test/NV2Data.lean`, each
stated as the theorem of that name. `hfrag` and `hrun` are the shipping `collectDeps`/`eraseEntry`
evaluated one traversal call at a time, as `Test/NV1Run.lean` does for NV-1. The kernel checks all
but the equation of the pure fold inside `hacc` (`checkDeclsPure … = .ok envNV2`), which `hacc` takes
as its premise and which a `#guard` checks by compiled evaluation, so the build fails if con-leche's
fold disagrees (DV-40). `krfl` (`Test/Run.lean`) is an auxiliary theorem `a = b` by `Eq.refl a`.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV1 EraseProof.Test.NV2

namespace EraseProof.Test.NV2

theorem hfrag : collectDeps view cfg e = .ok D := by krfl

def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-! ## Registration of `B` and `Box` -/

def stB (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `B (iidB, masksB)
    gdecls := (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩) :: st.gdecls }

theorem register_B_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok (((iidB, masksB), stB st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show B_ind.name = `B from rfl, h]
  apply bind_ok (a := [bodyB]) (st' := { st with inductives := st.inductives.insert `B (iidB, masksB) })
    (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem register_B_found {tc : TravCtx} (h : st.inductives[`B]? = some (iidB, masksB)) :
    (register_inductive (m := PureM) B_ind).runPure st tc pc ps = .ok (((iidB, masksB), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show B_ind.name = `B from rfl, h]
  rfl

def iidBox : InductiveId := ⟨mutualBlockKername [`Box], 0⟩
def masksBox : InductiveArgMasks := [#[.keep]]
def bodyBox : OneInductiveBody :=
  { name := toString `Box, propositional := false, ctors := [⟨toString `Box.mk, 1⟩], projs := [⟨"0"⟩] }

def stBox (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `Box (iidBox, masksBox)
    gdecls := (mutualBlockKername [`Box], .inductiveDecl ⟨.finite, 1, [bodyBox]⟩) :: st.gdecls }

theorem register_Box_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Box]? = none) :
    (register_inductive (m := PureM) Box_ind).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok (((iidBox, masksBox), stBox st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Box_ind.name = `Box from rfl, h]
  apply bind_ok (a := [bodyBox])
    (st' := { st with inductives := st.inductives.insert `Box (iidBox, masksBox) }) (ps' := ps) (by krfl)
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem register_Box_found {tc : TravCtx} (h : st.inductives[`Box]? = some (iidBox, masksBox)) :
    (register_inductive (m := PureM) Box_ind).runPure st tc pc ps = .ok (((iidBox, masksBox), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Box_ind.name = `Box from rfl, h]
  rfl

theorem stBox_B (h : st.inductives[`B]? = some (iidB, masksB)) :
    (stBox st).inductives[`B]? = some (iidB, masksB) := by
  simp only [stBox, Std.HashMap.getElem?_insert]; simpa using h

/-! ## Constructors -/

/-- The local of the binder `k` of the second alternative. -/
def fx (i : Nat) : FVarId := ⟨.num `_pure i⟩
def lk : Local := ⟨fx 0, `k, kTy, none⟩

/-- `visitConstructor` on `B.f` (index 0) or `B.t` (index 1) without arguments, `B` registered. -/
theorem visitConstructor_B_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} {c : Name}
    (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1)
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitConstructor (m := PureM) (n + 2) c #[]).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok ((.construct iidB k [], st), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [visitConstructor]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok (register_B_found h)
    simp only [toArray_toSubarray]
    krfl

/-- `visitConstructor` on `B.t` without arguments, `B` not registered: registers it. -/
theorem visitConstructor_Bt_new {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} (h : st.inductives[`B]? = none) :
    (visitConstructor (m := PureM) (n + 2) `B.t #[]).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok ((.construct iidB 1 [], stB st), ps) := by
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_B_new h)
  simp only [toArray_toSubarray]
  krfl

/-- `visitExpr` on `B.f` or `B.t`, at the top or under `k`: kept, a constructor; `B` registered. -/
theorem visitExpr_ctor_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    {c : Name} (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1) (hls : ls = [] ∨ ls = [lk])
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitExpr (m := PureM) (n + 6) (.const c [])).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok ((.construct iidB k [], st), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hls with rfl | rfl <;>
  · rw [visitExpr]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
    rw [visitApp]
    change (visitConstApp (m := PureM) (n + 4) _).runPure _ _ _ _ = _
    rw [visitConstApp]
    refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
    refine bind_ok (a := some 0) (st' := st) (ps' := ps) (by krfl) ?_
    change (withAppEtaToMinArity (m := PureM) (n + 3) _ 0 _).runPure _ _ _ _ = _
    rw [withAppEtaToMinArity]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := tB) (st' := st) (ps' := ps) (by krfl) ?_
    rw [withApp_const, withAppEtaToMinArity.go]
    exact visitConstructor_B_run (by simp) h

/-- `visitExpr` on the discriminant `B.t`, `B` not registered. -/
theorem visitExpr_Bt_new {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 6) cT).runPure st ⟨L, [], F, {}, dc⟩ pc ps =
      .ok ((.construct iidB 1 [], stB st), ps) := by
  rw [cT, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 4) _).runPure _ _ _ _ = _
  rw [visitConstApp]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 0) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 3) _ 0 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  exact visitConstructor_Bt_new h

/-- `visitExpr` on the erased type `B`, at the top or under `k`. -/
theorem visitExpr_tB_run {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hls : ls = [] ∨ ls = [lk]) :
    (visitExpr (m := PureM) (n + 1) tB).runPure st ⟨L, ls, F, {}, dc⟩ pc ps = .ok ((.box, st), ps) := by
  rcases hls with rfl | rfl <;>
  · rw [tB, visitExpr]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := true) (st' := st) (ps' := ps) (by krfl) ?_
    rfl

/-- The erasure of `Box.mk B B.t`. -/
def alt1L : LBTerm := .app (.app (.construct iidBox 0 []) .box) (.construct iidB 1 [])

theorem visitConstructor_alt1_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB)) (hBox : st.inductives[`Box]? = none) :
    (visitConstructor (m := PureM) (n + 8) `Box.mk #[tB, cT]).runPure st ⟨L, [], F, {}, dc⟩ pc ps =
      .ok ((alt1L, stBox st), ps) := by
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_Box_new hBox)
  simp only [Subarray.copy_eq_toArray, toArray_toSubarray]
  refine bind_ok (a := #[.keep]) (st' := stBox st) (ps' := ps) rfl ?_
  refine bind_ok (a := false) (st' := stBox st) (ps' := ps) rfl ?_
  apply bind_ok rfl
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply bind_ok rfl
  split
  · rename_i h; simp at h
  · rename_i h; simp at h
  all_goals
    rw [show #[tB, cT].extract 0 Boxmk_ctor.numParams ++ filter #[ConstructorArgRelevance.keep]
        (#[tB, cT].extract Boxmk_ctor.numParams (Boxmk_ctor.numParams + Boxmk_ctor.numFields)) ++
        #[tB, cT].extract (Boxmk_ctor.numParams + Boxmk_ctor.numFields) = #[tB, cT] by krfl,
      show Boxmk_ctor.cidx = 0 from rfl, visitAppArgs, ← Array.foldlM_toList]
    simp only [List.foldlM_cons, List.foldlM_nil]
    refine bind_ok (a := .app (.construct iidBox 0 []) .box) (st' := stBox st) (ps' := ps) ?_ ?_
    · apply bind_ok (visitExpr_tB_run (.inl rfl))
      rfl
    refine bind_ok (a := alt1L) (st' := stBox st) (ps' := ps) ?_ rfl
    apply bind_ok (visitExpr_ctor_run (k := 1) (.inr ⟨rfl, rfl⟩) (.inl rfl) (stBox_B hB))
    rfl


theorem withApp_alt1 {γ : Sort _} (k : Expr → Array Expr → γ) :
    alt1.withApp k = k cMk #[tB, cT] := by krfl

theorem visitExpr_alt1_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB)) (hBox : st.inductives[`Box]? = none) :
    (visitExpr (m := PureM) (n + 12) alt1).runPure st ⟨L, [], F, {}, dc⟩ pc ps =
      .ok ((alt1L, stBox st), ps) := by
  rw [alt1, visitExpr, ← alt1]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 10) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_alt1]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 2) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 9) _ 2 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tBox tB) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_alt1, withAppEtaToMinArity.go, ite_eq_left_of_eq_true _ _ (by decide)]
  exact visitConstructor_alt1_run hB hBox

/-! ## The η-expansion of `@Box.mk` -/

/-- The erasure of `Box.mk x y` with `x : Type` (erased) and `y : x`. -/
def boxApp (y : FVarId) : LBTerm := .app (.app (.construct iidBox 0 []) .box) (.fvar y)

/-- The locals under the two η-binders of `@Box.mk`: `val : α`, `α : Type`, at the fresh
variables `2` and `1`. -/
def lsη : List Local := [⟨fx 2, `val, .fvar (fx 1), none⟩, ⟨fx 1, `α, .sort l1, none⟩]

theorem visitConstructor_eta_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Box]? = some (iidBox, masksBox)) :
    (visitConstructor (m := PureM) (n + 3) `Box.mk #[.fvar (fx 1), .fvar (fx 2)]).runPure st
      ⟨L, lsη, F, {}, dc⟩ pc ps = .ok ((boxApp (fx 2), st), ps) := by
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_Box_found h)
  simp only [Subarray.copy_eq_toArray, toArray_toSubarray]
  krfl

/-- The erasure of `@Box.mk`, η-expanded: `fun α val => Box.mk □ val`. -/
def etaL : LBTerm :=
  .lambda (binderNameOf `α) (_root_.abstract (fx 1)
    (.lambda (binderNameOf `val) (_root_.abstract (fx 2) (boxApp (fx 2)))))

theorem visitExpr_mk_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Box]? = some (iidBox, masksBox)) :
    (visitExpr (m := PureM) (n + 9) cMk).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨1⟩ =
      .ok ((etaL, st), ⟨3⟩) := by
  rw [cMk, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 7) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_const]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := some 2) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 6) _ 2 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := mkTy) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [ite_eq_right_of_eq_false _ _ (by decide), forallMonocular]
  apply bind_ok rfl
  dsimp only [mkTy]
  rw [withLocalDecl]
  refine bind_ok (a := fx 1) (st' := st) (ps' := ⟨2⟩) rfl ?_
  rw [runPure_withReader]
  refine bind_ok (a := .lambda (binderNameOf `val) (_root_.abstract (fx 2) (boxApp (fx 2))))
    (st' := st) (ps' := ⟨3⟩) ?_ (by krfl)
  rw [withAppEtaToMinArity.go, ite_eq_right_of_eq_false _ _ (by decide), forallMonocular]
  refine bind_ok (a := .forallE `val (.fvar (fx 1)) (tBox (.fvar (fx 1))) .default) (st' := st)
    (ps' := ⟨2⟩) (by krfl) ?_
  dsimp only
  rw [withLocalDecl]
  refine bind_ok (a := fx 2) (st' := st) (ps' := ⟨3⟩) rfl ?_
  rw [runPure_withReader]
  refine bind_ok (a := boxApp (fx 2)) (st' := st) (ps' := ⟨3⟩) ?_ (by krfl)
  rw [withAppEtaToMinArity.go, ite_eq_left_of_eq_true _ _ (by decide)]
  exact visitConstructor_eta_run h

/-! ## The second alternative -/

/-- The body of `lamK` under `k`. -/
def bodyK : Expr := .app (.app (.fvar (fx 0)) tB) cF

theorem withApp_bodyK {γ : Sort _} (k : Expr → Array Expr → γ) :
    bodyK.withApp k = k (.fvar (fx 0)) #[tB, cF] := by krfl

/-- The erasure of `lamK`: `fun k => k □ B.f`. -/
def lamKL : LBTerm :=
  .lambda (binderNameOf `k) (_root_.abstract (fx 0) (.app (.app (.fvar (fx 0)) .box) (.construct iidB 0 [])))

theorem visitExpr_lamK_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitExpr (m := PureM) (n + 11) lamK).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((lamKL, st), ⟨1⟩) := by
  rw [lamK, visitExpr, ← lamK]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda, lamK, lambdaMonocular, withLocalDecl]
  refine bind_ok (a := fx 0) (st' := st) (ps' := ⟨1⟩) rfl ?_
  rw [runPure_withReader]
  refine bind_ok (a := .app (.app (.fvar (fx 0)) .box) (.construct iidB 0 [])) (st' := st)
    (ps' := ⟨1⟩) ?_ (by krfl)
  rw [show Backend.instantiate1 PureM (.app (.app (.bvar 0) tB) cF) (.fvar (fx 0)) = bodyK by krfl]
  rw [bodyK, visitExpr, ← bodyK]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp)), withApp_bodyK]
  refine bind_ok (a := .fvar (fx 0)) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app (.fvar (fx 0)) .box) (st' := st) (ps' := ⟨1⟩) ?_ ?_
  · apply bind_ok (visitExpr_tB_run (.inr rfl))
    rfl
  refine bind_ok (a := .app (.app (.fvar (fx 0)) .box) (.construct iidB 0 [])) (st' := st)
    (ps' := ⟨1⟩) ?_ rfl
  apply bind_ok (visitExpr_ctor_run (k := 0) (.inl ⟨rfl, rfl⟩) (.inr rfl) h)
  rfl

theorem withApp_alt2 {γ : Sort _} (k : Expr → Array Expr → γ) :
    alt2.withApp k = k lamK #[cMk] := withApp_app1 _ _ _ rfl

/-- The erasure of the second alternative: `(fun k => k □ B.f) (fun α val => Box.mk □ val)`. -/
def alt2L : LBTerm := .app lamKL etaL

theorem visitExpr_alt2_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB))
    (hBox : st.inductives[`Box]? = some (iidBox, masksBox)) :
    (visitExpr (m := PureM) (n + 13) alt2).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((alt2L, st), ⟨3⟩) := by
  rw [alt2, visitExpr, ← alt2]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp, ite_eq_right_of_eq_false _ _ (eq_false (by simp)), withApp_alt2]
  refine bind_ok (a := lamKL) (st' := st) (ps' := ⟨1⟩) (visitExpr_lamK_run hB) ?_
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := alt2L) (st' := st) (ps' := ⟨3⟩) ?_ rfl
  apply bind_ok (visitExpr_mk_run hBox)
  rfl

theorem visitAlt1_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB)) (hBox : st.inductives[`Box]? = none) :
    (visitAlt (m := PureM) (n + 13) 0 #[] [] alt1).runPure st ⟨L, [], F, {}, dc⟩ pc ps =
      .ok ((([], alt1L), stBox st), ps) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tBox tB) (st' := st) (ps' := ps) (by krfl) ?_
  rw [lambdaOrIntroToArity]
  apply bind_ok (visitExpr_alt1_run hB hBox)
  krfl

theorem visitAlt2_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB))
    (hBox : st.inductives[`Box]? = some (iidBox, masksBox)) :
    (visitAlt (m := PureM) (n + 14) 0 #[] [] alt2).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((([], alt2L), st), ⟨3⟩) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tBox tB) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [lambdaOrIntroToArity]
  apply bind_ok (visitExpr_alt2_run hB hBox)
  krfl

/-! ## The `case` on `B` -/

/-- `visitCases`'s alternatives: `B.f ↦ Box.mk B B.t`, `B.t ↦ (fun k => k B B.f) @Box.mk`. -/
def altsMap : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `B.f (0, alt1)).insert `B.t (0, alt2)

theorem altsMap_f : altsMap[`B.f]? = some (0, alt1) := by
  simp only [altsMap, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsMap_t : altsMap[`B.t]? = some (0, alt2) := by
  simp only [altsMap, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsMap_all : ([`B.f, `B.t].all fun x => altsMap.contains x) = true := by
  simp only [altsMap, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The erasure of `e`: the λ□ `case` on `B.t`. -/
def t0 : LBTerm := .case (iidB, 0) (.construct iidB 1 []) [([], alt1L), ([], alt2L)]

theorem stB_B : (stB st).inductives[`B]? = some (iidB, masksB) := by
  simp only [stB, Std.HashMap.getElem?_insert_self]

theorem stB_Box (h : st.inductives[`Box]? = none) : (stB st).inductives[`Box]? = none := by
  simp only [stB, Std.HashMap.getElem?_insert]; simpa using h

theorem stBox_Box : (stBox st).inductives[`Box]? = some (iidBox, masksBox) := by
  simp only [stBox, Std.HashMap.getElem?_insert_self]

theorem visitCasesOn_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = some (iidB, masksB)) (hBox : st.inductives[`Box]? = none) :
    (visitCasesOn (m := PureM) (n + 15) B_ind altsMap ∅ none (.construct iidB 1 [])).runPure st
      ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ = .ok ((t0, stBox st), ⟨3⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_B_found hB)
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsMap_f, altsMap_t, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[]] : List ConstructorArgMask)))
    (st' := stBox st) (ps' := ⟨0⟩) ?_ ?_
  · apply bind_ok (visitAlt1_run hB hBox)
    rfl
  refine bind_ok (a := (#[([], alt1L), ([], alt2L)], ([] : List ConstructorArgMask)))
    (st' := stBox st) (ps' := ⟨3⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([], alt2L)], ([] : List ConstructorArgMask)))
      (st' := stBox st) (ps' := ⟨3⟩) ?_ ?_
    · apply bind_ok (visitAlt2_run (stBox_B hB) stBox_Box)
      rfl
    · rfl
  rfl

/-- The recognizer recognizes `B.casesOn` over the closure (NV-1's `ciB`). -/
theorem casesInfo_B : casesInfo? D `B.casesOn = some ciB := by krfl

def args4 : Array Expr := cases4.toArray

theorem visitCases_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hB : st.inductives[`B]? = none) (hBox : st.inductives[`Box]? = none) :
    (visitCases (m := PureM) (n + 17) ciB args4).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((t0, stBox (stB st)), ⟨3⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  have hr : (ciB.altsRange.toList) = [2, 3] := by simp [ciB, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsMap, none, ?sEnd)) (st' := st) (ps' := ⟨0⟩) ?_ ?_
  case sEnd => exact (ciB.altNumParams.toSubarray 2 2)
  · rfl
  apply bind_ok (visitExpr_Bt_new hB)
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, altsMap_all, ite_true]
  apply bind_ok (visitCasesOn_run stB_B (stB_Box hBox))
  rw [show ciB.arity = args4.size from rfl, forIn_toSubarray_size]
  rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `B.casesOn [l1]) args4 := by krfl

theorem e_run {n : Nat} {L : LocalContext}
    (hB : st.inductives[`B]? = none) (hBox : st.inductives[`Box]? = none) :
    (visitExpr (m := PureM) (n + 21) e).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((t0, stBox (stB st)), ⟨3⟩) := by
  have he : e = .app (.app (.app (.app (.const `B.casesOn [l1]) motB) cT) alt1) alt2 := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 19) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := some ciB) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 18) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motB cT) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go, ite_eq_left_of_eq_true _ _ (by decide)]
  exact visitCases_run hB hBox

/-- The program `#erase` emits for NV-2. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`Box], .inductiveDecl ⟨.finite, 1, [bodyBox]⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)] (some t0)

theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 21) + 21 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 21 + 21) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((t0, stBox (stB {})), ⟨3⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hfrag, hpure]

/-! # The premises -/


/-! ## con-leche's records and environment (`k` = con-leche form) -/

def nm (s : String) : ConLeche.Name := .str .anonymous s
def nm2 (a b : String) : ConLeche.Name := .str (.str .anonymous a) b
def k1 : ConLeche.Level := .succ .zero
def kU : ConLeche.Level := .param (nm "u")
def kB : ConLeche.Expr := .const (nm "B") []
def kF : ConLeche.Expr := .const (nm2 "B" "f") []
def kT : ConLeche.Expr := .const (nm2 "B" "t") []
def kBox (a : ConLeche.Expr) : ConLeche.Expr := .app (.const (nm "Box") []) a
def kMk : ConLeche.Expr := .const (nm2 "Box" "mk") []
def kMotTy : ConLeche.Expr := .forallE kB (.sort kU)
def kRecType : ConLeche.Expr :=
  .forallE kMotTy (.forallE (.app (.bvar 0) kF) (.forallE (.app (.bvar 1) kT)
    (.forallE kB (.app (.bvar 3) (.bvar 0)))))
def kRule (c : String) (pick : Nat) : ConLeche.RecRule :=
  { ctor := nm2 "B" c, nfields := 0, fire := .plain,
    rhs := .lam kMotTy (.lam (.app (.bvar 0) kF) (.lam (.app (.bvar 1) kT) (.bvar pick))) }
def kBlock : ConLeche.Declaration :=
  .indDecl
    [ .indInfo ⟨nm "B", [], .sort k1⟩ {}
    , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
    , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
    , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0] ] 0
def kCasesOnTy : ConLeche.Expr :=
  .forallE kMotTy (.forallE kB (.forallE (.app (.bvar 1) kF) (.forallE (.app (.bvar 2) kT)
    (.app (.bvar 3) (.bvar 2)))))
def kCasesOnVal : ConLeche.Expr :=
  .lam kMotTy (.lam kB (.lam (.app (.bvar 1) kF) (.lam (.app (.bvar 2) kT)
    (.app (.app (.app (.app (.const (nm2 "B" "rec") [kU]) (.bvar 3)) (.bvar 1)) (.bvar 0)) (.bvar 2)))))
def kMkTy : ConLeche.Expr := .forallE (.sort k1) (.forallE (.bvar 0) (kBox (.bvar 1)))
def kBMotTy : ConLeche.Expr := .forallE (kBox (.bvar 0)) (.sort kU)
def kBMinTy : ConLeche.Expr := .forallE (.bvar 1) (.app (.bvar 1) (.app (.app kMk (.bvar 2)) (.bvar 0)))
def kBoxRecTy : ConLeche.Expr :=
  .forallE (.sort k1) (.forallE kBMotTy (.forallE kBMinTy (.forallE (kBox (.bvar 2)) (.app (.bvar 2) (.bvar 0)))))
def kBoxRule : ConLeche.RecRule :=
  { ctor := nm2 "Box" "mk", nfields := 1, fire := .plain,
    rhs := .lam (.sort k1) (.lam kBMotTy (.lam kBMinTy (.lam (.bvar 2) (.app (.bvar 1) (.bvar 0))))) }
def kBoxBlock : ConLeche.Declaration :=
  .indDecl
    [ .indInfo ⟨nm "Box", [], .forallE (.sort k1) (.sort k1)⟩ {}
    , .ctorInfo ⟨nm2 "Box" "mk", [], kMkTy⟩ 1 1 (nm "Box")
    , .recInfo ⟨nm2 "Box" "rec", [nm "u"], kBoxRecTy⟩ 3 3 false [kBoxRule] ] 1

/-- con-leche's input for NV-2 (`DeclsOf? P`). -/
def nv2full : List ConLeche.Declaration :=
  [kBlock, .defnDecl ⟨nm2 "B" "casesOn", [nm "u"], kCasesOnTy⟩ kCasesOnVal .abbrev, kBoxBlock]

/-- NV-2's accepted environment, newest first (the fold's result, `#guard` below). -/
def envNV2 : ConLeche.Env :=
  ⟨[ .recInfo ⟨nm2 "Box" "rec", [nm "u"], kBoxRecTy⟩ 3 3 false [kBoxRule]
   , .ctorInfo ⟨nm2 "Box" "mk", [], kMkTy⟩ 1 1 (nm "Box")
   , .indInfo ⟨nm "Box", [], .forallE (.sort k1) (.sort k1)⟩
       { eta := true, all := [nm "Box"], nparams := 1, nIdx := 0, ctors := [nm2 "Box" "mk"],
         neverZero := true }
   , .defnInfo ⟨nm2 "B" "casesOn", [nm "u"], kCasesOnTy⟩ kCasesOnVal .abbrev
   , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0]
   , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
   , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
   , .indInfo ⟨nm "B", [], .sort k1⟩
       { eta := false, all := [nm "B"], nparams := 0, nIdx := 0,
         ctors := [nm2 "B" "f", nm2 "B" "t"], neverZero := true } ],
   [{ structName := nm "Box", levelParams := [], numParams := 1, ctor := nm2 "Box" "mk",
      numFields := 1, bodies := #[.bvar 1] }]⟩

#guard match ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    nv2full with
  | .ok env => decide (env.consts = envNV2.consts) && decide (env.tables = envNV2.tables)
  | .error _ => false

theorem decls : DeclsOf? P = some nv2full := by krfl


def kTyK : ConLeche.Expr := .forallE (.sort k1) (.forallE (.bvar 0) (kBox (.bvar 1)))
def kMotB : ConLeche.Expr := .lam kB (kBox kB)
def kAlt1 : ConLeche.Expr := .app (.app kMk kB) kT
def kLamK : ConLeche.Expr := .lam kTyK (.app (.app (.bvar 0) kB) kF)
def kAlt2 : ConLeche.Expr := .app kLamK kMk
def kE : ConLeche.Expr := .app (.app (.app (.app (.const (nm2 "B" "casesOn") [k1]) kMotB) kT) kAlt1) kAlt2
theorem toCL_e : toCL? e = some kE := by krfl
theorem t_e : ConLeche.inferTypeCore .verified false envNV2 100 0 kE = .ok (.app kMotB kT) := by krfl
/-- the evaluation environment of the final theorem -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

/-! ## `hacc`, `hty`, `hview`, `hfrag`, `hnopre`, `hrun` -/

theorem hacc (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel)
    [] nv2full = .ok envNV2) : ConLecheAccepts P envNV2 :=
  ⟨nv2full, decls, hfold⟩

theorem hty : CLTyped envNV2 e := ⟨kE, 100, .app kMotB kT, toCL_e, t_e⟩

theorem hclean : NoMarkKeys e = true := by krfl

/-- A declaration without an `_unsafe_rec` companion in the view has no compiled pre-definition. -/
theorem preDef_none {view : EnvView} {cfg : ErasureConfig} {ci : ConstantInfo}
    (h : view.find? (Compiler.mkUnsafeRecName ci.name) = none) : preDef? view cfg ci = none := by
  cases ci with
  | defnInfo d =>
    have h' : view.find? (Compiler.mkUnsafeRecName d.name) = none := h
    simp only [preDef?, h']
  | _ => rfl

theorem hview : ViewAgrees view P := by
  intro ci h
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none (by krfl)] at hp <;> cases hp


theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-- The closure is part of the program (the conclusion of `collectDeps_sub` on NV-2). -/
theorem sub : SubEnv D P := by
  intro ci h
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> krfl

/-! ## `hmark`: the eraser's decisions on `e`, by symbolic evaluation of the oracle -/

/-- `@Box.mk` η-expanded as `MarkEta.intro` writes it, the type parameter erased. -/
def mkM : Expr := markEta (.lam `α (.sort l1) (markEta (.lam `val (.bvar 0)
  (.app (.app cMk (markErase (.bvar 1))) (.bvar 0)) .default)) .implicit)
def alt1M : Expr := .app (.app cMk (markErase tB)) cT
def lamKM : Expr := .lam `k kTy (.app (.app (.bvar 0) (markErase tB)) cF) .default
def alt2M : Expr := .app lamKM mkM
/-- The marking of `e`. -/
def eM : Expr := .app (.app (.app (.app (.const `B.casesOn [l1]) motB) cT) alt1M) alt2M

/-- A constructor without arguments is kept and has no mark (`visitConstructor`). -/
theorem mark_ctor {ls : List Local} {c : Name}
    (ho : oracle D ls (.const c []) = .ok false) (ha : markArity? D cfg c = some 0)
    (hi : Pure.inferType ⟨D⟩ oracleFuel ls [] (.const c []) = .ok tB)
    (hc : casesInfo? D c = none) (hr : ctorArity? D c = some 0) :
    MarkOf D cfg ls (.const c []) (.const c []) :=
  MarkOf.special (c := c) (us := []) (as := []) ho ha hi
    (MarkEta.sat (Nat.le_refl 0) (MarkSat.ctor (as := []) (âs := []) hc hr rfl (by simp)))

theorem mark_alt1 : MarkOf D cfg [] alt1 alt1M := by
  refine MarkOf.special (c := `Box.mk) (us := []) (as := [tB, cT]) (ar := 2) (T := tBox tB) (by krfl)
    (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.ctor (ar := 2) (as := [tB, cT]) (âs := [markErase tB, cT]) (by krfl) (by krfl) rfl ?_
  intro i a â ha hâ
  rcases i with _ | _ | i <;> simp at ha hâ <;> subst ha hâ
  · exact MarkOf.erase (by krfl)
  · exact mark_ctor (by krfl) (by krfl) (by krfl) (by krfl) (by krfl)

/-- The saturated spine under the η-binders. -/
def mkSat : Expr := .app (.app cMk (markErase (.fvar (fx 1)))) (.fvar (fx 2))

theorem mark_mk : MarkOf D cfg [] cMk mkM := by
  refine MarkOf.special (c := `Box.mk) (us := []) (as := []) (ar := 2) (T := mkTy) (by krfl) (by krfl)
    (by krfl) ?_
  refine MarkEta.intro (x := fx 1) (y := `α) (D := .sort l1)
    (C := .forallE `val (.bvar 0) (tBox (.bvar 1)) .default) (bi := .implicit)
    (ê := markEta (.lam `val (.fvar (fx 1)) (absFV (fx 2) 0 mkSat) .default)) (by decide) rfl ?_ ?_
  · simp [Fresh, FVarsIn, mkTy, tBox]
  refine MarkEta.intro (x := fx 2) (y := `val) (D := .fvar (fx 1)) (C := tBox (.fvar (fx 1)))
    (bi := .default) (ê := mkSat) (by decide) (by krfl) ?_ ?_
  · simp [Fresh, FVarsIn, tBox, Expr.instantiate1', Expr.liftLooseBVars', fx]
  refine MarkEta.sat (by decide) (MarkSat.ctor (ar := 2) (as := [.fvar (fx 1), .fvar (fx 2)])
    (âs := [markErase (.fvar (fx 1)), .fvar (fx 2)]) (by krfl) (by krfl) rfl ?_)
  intro i a â ha hâ
  rcases i with _ | _ | i <;> simp at ha hâ <;> subst ha hâ
  · exact MarkOf.erase (by krfl)
  · exact MarkOf.fvar (by krfl)

theorem mark_lamK : MarkOf D cfg [] lamK lamKM := by
  refine MarkOf.lam (n := `k) (A := kTy) (b := .app (.app (.bvar 0) tB) cF) (bi := .default)
    (x := fx 0) (bM := .app (.app (.fvar (fx 0)) (markErase tB)) cF) (by krfl)
    (by simp [Fresh, FVarsIn, tB, cF]) ?_
  refine MarkOf.app (f := .fvar (fx 0)) (fM := .fvar (fx 0)) (as := [tB, cF]) (âs := [markErase tB, cF])
    (by krfl) (by simp) rfl (by intro c us h; cases h) (MarkOf.fvar (by krfl)) rfl ?_
  intro i a â ha hâ
  rcases i with _ | _ | i <;> simp at ha hâ <;> subst ha hâ
  · exact MarkOf.erase (by krfl)
  · exact mark_ctor (by krfl) (by krfl) (by krfl) (by krfl) (by krfl)

theorem mark_alt2 : MarkOf D cfg [] alt2 alt2M := by
  refine MarkOf.app (f := lamK) (fM := lamKM) (as := [cMk]) (âs := [mkM]) (by krfl) (by simp) rfl
    (by intro c us h; cases h) mark_lamK rfl ?_
  intro i a â ha hâ
  rcases i with _ | i <;> simp at ha hâ <;> subst ha hâ
  exact mark_mk

theorem findD_f : findDecl D `B.f = some (.ctorInfo Bf_ctor) := by krfl
theorem findD_t : findDecl D `B.t = some (.ctorInfo Bt_ctor) := by krfl

theorem hmark : MarkOf D cfg [] e eM := by
  refine MarkOf.special (c := `B.casesOn) (us := [l1]) (as := cases4) (ar := 4) (T := .app motB cT)
    (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  exact MarkSat.cases (iv := B_ind) (cd := B_casesOn) (u := .succ .zero) (pre := [motB])
    (d := cT) (dM := cT) (alts := [alt1, alt2]) (âlts := [alt1M, alt2M]) (extra := []) (êxtra := [])
    (by krfl) (by krfl) (by decide) rfl rfl (by krfl) (fun h => by cases h)
    (mark_ctor (by krfl) (by krfl) (by krfl) (by krfl) (by krfl)) rfl
    (by
      intro i cn h
      rcases i with _ | _ | i <;> simp [B_ind] at h <;> subst h
      · exact ⟨_, findD_f⟩
      · exact ⟨_, findD_t⟩)
    (by
      intro i alt h
      rcases i with _ | _ | i <;> simp at h <;> subst h
      · exact ⟨tBox tB, by krfl⟩
      · exact ⟨tBox tB, by krfl⟩)
    (by
      intro i cn cv alt âlt T h1 h2 h3 h4 _
      rcases i with _ | _ | i <;> simp [B_ind] at h1 h3 h4 <;> subst h1 h3 h4
      · rw [findD_f] at h2; cases h2
        exact MarkAlt.done mark_alt1
      · rw [findD_t] at h2; cases h2
        exact MarkAlt.done mark_alt2)
    rfl (by simp)

/-! ## `hcert`: con-leche types the marked input and certifies its four marks

The marks of `eM`: `B` in the first alternative (no binder), `B` under the source λ `k`, and the
η-variable `α` of the η-expanded `@Box.mk` under its two η-binders. The emitted environment holds
no constant, so no body is asked of. -/

/-- the context of the η-variable `α`: `val : α`, `α : Type`, innermost first -/
def Γη : List CtxBinder := [(.bvar 0, none), (.sort l1, none)]

theorem cert_B0 : CLCert envNV2 [] tB :=
  ⟨kB, 0, kB, .sort k1, .sort k1, by krfl, by krfl, rfl, by krfl, .inl (by krfl)⟩

theorem cert_Bk : CLCert envNV2 [(kTy, none)] tB :=
  ⟨.lam kTyK kB, 1, kB, .forallE kTyK (.sort k1), .sort k1, by krfl, by krfl, by krfl, by krfl,
    .inl (by krfl)⟩

theorem cert_α : CLCert envNV2 Γη (.bvar 1) :=
  ⟨.lam (.sort k1) (.lam (.bvar 0) (.bvar 1)), 2, .fvar 0 (.sort k1),
    .forallE (.sort k1) (.forallE (.bvar 0) (.sort k1)), .sort k1, by krfl, by krfl, by krfl, by krfl,
    .inl (by krfl)⟩

/-- con-leche's reading of the marked input: the η-expansion is read as a λ. -/
def kEM : ConLeche.Expr :=
  .app (.app (.app (.app (.const (nm2 "B" "casesOn") [k1]) kMotB) kT) kAlt1)
    (.app kLamK (.lam (.sort k1) (.lam (.bvar 0) (.app (.app kMk (.bvar 1)) (.bvar 0)))))

theorem typedAt_eM : CLTypedAt envNV2 eM := ⟨kEM, .app kMotB kT, by krfl, by krfl⟩

theorem marks_eM : MarksCert envNV2 [] eM :=
  ⟨⟨⟨⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩, ⟨⟨trivial, cert_B0⟩, trivial⟩⟩,
    ⟨⟨⟨trivial, cert_Bk⟩, trivial⟩, ⟨⟨trivial, cert_α⟩, trivial⟩⟩⟩

theorem hcert : ProgCert envNV2 D cfg p0 eM := by
  refine ⟨typedAt_eM, marks_eM, ?_⟩
  intro lenv t hp ci hci v cb hv hl _
  cases hp
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try cases hv
  rw [show lookupConst [(mutualBlockKername [`Box], .inductiveDecl ⟨.finite, 1, [bodyBox]⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)]
      (toKername (ConstantInfo.defnInfo B_casesOn).name) = none by krfl] at hl
  cases hl

/-! ## `hev`: an explicit derivation of `eM ⇓ Box.mk □□B B.f`, its certificates by the kernel at
`envNV2` (none needs ι: the motive is constant) -/

theorem find_f : findDecl P `B.f = some (.ctorInfo Bf_ctor) := by krfl
theorem find_t : findDecl P `B.t = some (.ctorInfo Bt_ctor) := by krfl
theorem find_mk : findDecl P `Box.mk = some (.ctorInfo Boxmk_ctor) := by krfl

theorem ok_f : CLOk envNV2 cF := ⟨kF, 100, kB, by krfl, by krfl⟩
theorem ok_t : CLOk envNV2 cT := ⟨kT, 100, kB, by krfl, by krfl⟩

theorem ev_f : SrcEval envNV2 σ cF cF :=
  SrcEval.ctor (c := `B.f) (us := []) (as := []) (vs := []) find_f rfl rfl (by simp) ok_f
theorem ev_t : SrcEval envNV2 σ cT cT :=
  SrcEval.ctor (c := `B.t) (us := []) (as := []) (vs := []) find_t rfl rfl (by simp) ok_t

/-- `B` is a type former for con-leche. -/
theorem erasable_B : CLErasable envNV2 tB := ⟨kB, 100, .sort k1, by krfl, by krfl, .inl (by krfl)⟩
theorem erasable_mB : CLErasable envNV2 (markErase tB) := ⟨kB, 100, .sort k1, by krfl, by krfl, .inl (by krfl)⟩

/-- the value: `Box.mk □□B B.f` -/
def vM : Expr := .app (.app cMk (markErase (markErase tB))) cF

/-- the η-λ of `val` after the β-step on `α := □B` -/
def etaVal : Expr := markEta (.lam `val (markErase tB) (.app (.app cMk (markErase (markErase tB))) (.bvar 0)) .default)

theorem ok_v : CLOk envNV2 vM := ⟨.app (.app kMk kB) kF, 100, kBox kB, by krfl, by krfl⟩
theorem ev_v : SrcEval envNV2 σ vM vM :=
  SrcEval.ctor (c := `Box.mk) (us := []) (cv := Boxmk_ctor) (as := [markErase (markErase tB), cF])
    (vs := [markErase (markErase tB), cF]) find_mk rfl rfl (by
      intro i a v ha hv
      rcases i with _ | _ | i <;> simp at ha hv <;> subst ha hv
      · exact SrcEval.frozen erasable_mB
      · exact ev_f) ok_v

theorem not_short {x : Expr} (h : ∀ c us, x.getAppFn ≠ .const c us) : ¬ ShortSpine σ x := by
  rintro ⟨c, us, ar, h1, -⟩
  exact h c us h1

/-- `CLOk` of `(fun α val => Box.mk α val) B` -/
theorem ok_eta1 : CLOk envNV2 (.app mkM (markErase tB)) :=
  ⟨.app (.lam (.sort k1) (.lam (.bvar 0) (.app (.app kMk (.bvar 1)) (.bvar 0)))) kB, 100,
    .forallE kB (kBox kB), by krfl, by krfl⟩

/-- `CLOk` of `(fun val : B => Box.mk B val) B.f` -/
theorem ok_eta2 : CLOk envNV2 (.app etaVal cF) :=
  ⟨.app (.lam kB (.app (.app kMk kB) (.bvar 0))) kF, 100, kBox kB, by krfl, by krfl⟩

theorem ev_inner : SrcEval envNV2 σ (.app mkM (markErase tB)) etaVal :=
  SrcEval.etaBeta (n := `α) (A := .sort l1)
    (b := markEta (.lam `val (.bvar 0) (.app (.app cMk (markErase (.bvar 1))) (.bvar 0)) .default))
    (bi := .implicit) (not_short (by intro c us h; cases h)) SrcEval.etaLam
    (SrcEval.frozen erasable_B) ok_eta1 SrcEval.etaLam

theorem ev_body : SrcEval envNV2 σ (.app (.app mkM (markErase tB)) cF) vM :=
  SrcEval.etaBeta (n := `val) (A := markErase tB)
    (b := .app (.app cMk (markErase (markErase tB))) (.bvar 0)) (bi := .default)
    (not_short (by intro c us h; cases h)) ev_inner ev_f ok_eta2 ev_v

/-- `CLOk` of `(fun k => k B B.f) (fun α val => Box.mk α val)` -/
theorem ok_beta : CLOk envNV2 (.app lamKM mkM) :=
  ⟨.app kLamK (.lam (.sort k1) (.lam (.bvar 0) (.app (.app kMk (.bvar 1)) (.bvar 0)))), 100,
    kBox kB, by krfl, by krfl⟩

theorem ev_alt2 : SrcEval envNV2 σ alt2M vM :=
  SrcEval.beta (n := `k) (A := kTy) (b := .app (.app (.bvar 0) (markErase tB)) cF) (bi := .default)
    (not_short (by intro c us h; cases h)) (SrcEval.atom trivial) SrcEval.etaLam ok_beta ev_body

/-- `CLOk` of the saturated `casesOn` with its evaluated major. -/
theorem ok_cases : CLOk envNV2 eM := ⟨kEM, 100, .app kMotB kT, by krfl, by krfl⟩

theorem hev : SrcEval envNV2 σ eM vM :=
  SrcEval.casesIota (c := `B.casesOn) (us := [l1]) (iv := B_ind) (as := [motB, cT, alt1M, alt2M])
    (m := cT) (mv := cT) (i := 1) (fs := []) (alt := alt2M) (by krfl) rfl rfl ev_t
    ⟨`B.t, [], Bt_ctor, [], find_t, rfl, rfl, rfl, rfl, rfl⟩ ok_cases rfl ev_alt2

end EraseProof.Test.NV2
