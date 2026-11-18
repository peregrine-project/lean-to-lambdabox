import EraseProof.Test.NVUModel
import EraseProof.Test.NVAFinal

/-!
# NV-U: the source evaluation

`hev`: the term `e = Nat.add 2 3` of NV-U (`Test/NVUData.lean`) evaluates to
`Nat.succ (Nat.succ (Nat.succ 2))` at `σU := evalEnvOf view cfgU P`, under the conversion premise
`SrcConv E B []` of the statements. Under `cfgU`, `Nat.add` has no δ: its compiled pre-definition
`preVal` is its λ□ fixpoint's body, and `SrcEval.deltaRec` evaluates `Nat.add a b` by evaluating
`a`, `b` to `va`, `vb` and then `preVal va vb`, given `Nat.add va vb ≡ preVal va vb` (`deltaRec_add`).
`preVal 2 k` evaluates to `V k` (`ev_pre`), `V k` the literal `2` under `k` constructors `Nat.succ`:
the match `Nat.add.match_1` (δ, five β) is a `Nat.casesOn` on the literal `k`
(`SrcEval.casesLitZero`, `casesLitSucc`), whose second alternative calls `Nat.add 2 (k - 1)`, again
by `deltaRec`. The conversion at each call `Nat.add 2 k`, `k = 3, 2, 1, 0` (`conv_add`), is subject
reduction (`SrcEval.defeq`) on two evaluations to `V k`: NV-A's, at the kernel definition of
`Nat.add` (`structural := .kernel`, `ev_kernel`), and `ev_pre`; the two translations of `V k` are
congruent (`TrM.dcong`). `ev_add` proves the three facts for every `k` by induction.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVU

open EraseProof.Test.NVL (tN cZ cS Nat_ind Zero_ctor Succ_ctor)
open EraseProof.Test.NVS (l1 u1)
open EraseProof.Test.NVA (x14 P e view add_def match_def inst_def ofNat_def OfNat_mk borrowed cOf lit
  instK numK n58 V v5 σ ev_delta ev_atom ev_lit ns_const ns_lam ev_recG0 ev_recGS ev_recG ev_zMin
  ev_callB ctorT G_eq G T tv yv motA fVal Nat_brecOn Nat_brecOn_go add_f E B henv hwf hview
  natLitM_typed B13_N B13_z B13_s n13 addTyM ζ13)
open EraseProof.Test.NV1 (typed_of_eq app_typed)
open EraseProof.Test.NVS (app_typed')

/-- The evaluation environment of NV-U. -/
abbrev σU : EvalEnv := evalEnvOf view cfgU P

/-- The conversion premise of the statements. -/
abbrev CU : Lean.Expr → Lean.Expr → Prop := SrcConv E B []

/-! ## The kernel definition of `Nat.add` at NV-A's environment, on every literal -/

/-- The recursor of `Nat.brecOn.go` on the literal `k`. -/
theorem ev_recZ {C : Lean.Expr → Lean.Expr → Prop} :
    ∀ k, SrcEval σ C (EraseProof.Test.NVA.recG EraseProof.Test.NVA.zMin (lit k)) (T k)
  | 0 => ev_recG0 ev_zMin
  | k + 1 => ev_recGS ev_zMin (ev_recG k)

theorem ev_go {C : Lean.Expr → Lean.Expr → Prop} (k : Nat) :
    SrcEval σ C (.app (.app (.app (.const `Nat.brecOn.go [l1]) motA) (lit k)) fVal) (T k) := by
  have hns : specialArity σ `Nat.brecOn.go = none := by krfl
  have h0 := ev_delta (C := C) (c := `Nat.brecOn.go) (us := [l1]) (v := Nat_brecOn_go) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motA) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 (ev_lit k) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 (ev_atom (e := fVal) trivial) (ev_recZ k)

theorem ev_brecOn {C : Lean.Expr → Lean.Expr → Prop} (k : Nat) :
    SrcEval σ C (.app (.app (.app (.const `Nat.brecOn [l1]) motA) (lit k))
      (.const `Nat.add._f [])) (G k) := by
  have hns : specialArity σ `Nat.brecOn = none := by krfl
  have h0 := ev_delta (C := C) (c := `Nat.brecOn) (us := [l1]) (v := Nat_brecOn) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motA) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 (ev_lit k) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2
    (ev_delta (c := `Nat.add._f) (us := []) (v := add_f) (by krfl) (ev_atom trivial))
    (SrcEval.proj (ev_go k) (ctorT k) (fs := [G k, tv k]) rfl)

/-- `Nat.add 2 k ⇓ V k` at NV-A's environment, through `Nat.add`'s kernel definition (δ). -/
theorem ev_kernel {C : Lean.Expr → Lean.Expr → Prop} (k : Nat) :
    SrcEval σ C (.app (.app (.const `Nat.add []) (lit 2)) (lit k)) (V k) := by
  have hns : specialArity σ `Nat.add = none := by krfl
  have h0 := ev_delta (C := C) (c := `Nat.add) (us := []) (v := add_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_lit 2) (ev_atom trivial)
  have hb := ev_brecOn (C := C) k
  rw [G_eq] at hb
  exact SrcEval.beta (ns_const rfl hns) h1 (ev_lit k)
    (SrcEval.beta (ns_const rfl (by krfl)) hb (ev_lit 2) (ev_callB k))

/-! ## Steps at `σU` -/

theorem nsU_lam {f a : Lean.Expr} {n : Name} {A b : Lean.Expr} {bi : BinderInfo}
    (h : f.getAppFn = .lam n A b bi) : ¬ ShortSpine σU (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem nsU_const {f a : Lean.Expr} {c : Name} {us : List Level} (h : f.getAppFn = .const c us)
    (hc : specialArity σU c = none) : ¬ ShortSpine σU (.app f a) := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2

theorem evU_delta {c : Name} {us : List Level} {v : DefinitionVal} {r : Lean.Expr}
    (h : σU.unfold? c = some (.defnInfo v, v.value))
    (hr : SrcEval σU CU (Pure.instLevels v.levelParams us v.value) r) :
    SrcEval σU CU (.const c us) r :=
  .delta h hr

theorem evU_tN : SrcEval σU CU tN tN := .constAtom (by krfl)

/-- `Nat.succ a ⇓ Nat.succ v` when `a ⇓ v`. -/
theorem evU_succ {a v : Lean.Expr} (h : SrcEval σU CU a v) :
    SrcEval σU CU (.app cS a) (.app cS v) := by
  refine SrcEval.ctor (c := `Nat.succ) (us := []) (as := [a]) (vs := [v]) rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | i <;> simp at h1 h2
  subst h1 h2
  exact h

/-! ## The numerals at `σU` -/

theorem evU_mkOf (k : Nat) : SrcEval σU CU (EraseProof.Test.NVA.mkOf k)
    (EraseProof.Test.NVA.mkOf k) := by
  refine SrcEval.ctor (c := `OfNat.mk) (us := [.zero]) (as := [tN, lit k, lit k])
    (vs := [tN, lit k, lit k]) rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact evU_tN
  · exact .lit
  · exact .lit

theorem evU_instK (k : Nat) : SrcEval σU CU (instK k) (EraseProof.Test.NVA.mkOf k) :=
  .beta (nsU_const rfl (by krfl)) (evU_delta (v := inst_def) (by krfl) (.atom trivial)) .lit
    (evU_mkOf k)

/-- The numeral `k` evaluates to the literal `k` at `σU`, as at NV-A's environment. -/
theorem evU_numK (k : Nat) : SrcEval σU CU (numK k) (lit k) := by
  have h0 := evU_delta (c := `OfNat.ofNat) (us := [.zero]) (v := ofNat_def) (by krfl)
    (.atom trivial)
  have h1 := SrcEval.beta (nsU_const rfl (by krfl)) h0 (SrcEval.mdata (d := borrowed) evU_tN)
    (.atom trivial)
  have h2 := SrcEval.beta (nsU_const rfl (by krfl)) h1 (.lit (k := k)) (.atom trivial)
  exact SrcEval.beta (nsU_const rfl (by krfl)) h2 (evU_instK k)
    (SrcEval.proj (evU_mkOf k)
      ⟨`OfNat.mk, [.zero], OfNat_mk, [tN, lit k], rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fs := [lit k]) rfl)

/-! ## `deltaRec` on `Nat.add` -/

theorem find_add : findDecl σU.decls `Nat.add = some (.defnInfo add_def) := by krfl
theorem casesOn_add : σU.casesOn? `Nat.add = none := by krfl
theorem atom_add : σU.isAtom `Nat.add = false := by krfl
theorem ax_add : σU.axiomatized (.defnInfo add_def) = false := by krfl
theorem pre_add : σU.recPre? (.defnInfo add_def) = some preVal := preDef_add
theorem arity_pre : lamArity preVal = 2 := by krfl
theorem inst_pre : Pure.instLevels [] [] preVal = preVal := by krfl

theorem mkAppN_two (f a b : Lean.Expr) : mkAppN f [a, b].toArray = .app (.app f a) b := rfl

/-- `Nat.add a b ⇓ v` at `σU` (`SrcEval.deltaRec`): `a ⇓ va`, `b ⇓ vb`, the conversion
`Nat.add va vb ≡ preVal va vb`, and `preVal va vb ⇓ v`. Reference: none (DV-7). -/
theorem deltaRec_add {a b va vb v : Lean.Expr} (ha : SrcEval σU CU a va)
    (hb : SrcEval σU CU b vb)
    (hc : CU (.app (.app (.const `Nat.add []) va) vb) (.app (.app preVal va) vb))
    (hp : SrcEval σU CU (.app (.app preVal va) vb) v) :
    SrcEval σU CU (.app (.app (.const `Nat.add []) a) b) v := by
  have hlp : (ConstantInfo.defnInfo add_def).levelParams = [] := rfl
  have hc' : CU (mkAppN (.const `Nat.add []) [va, vb].toArray)
      (mkAppN (Pure.instLevels (ConstantInfo.defnInfo add_def).levelParams [] preVal)
        [va, vb].toArray) := by
    rw [hlp, inst_pre, mkAppN_two, mkAppN_two]; exact hc
  have hp' : SrcEval σU CU (mkAppN (Pure.instLevels (ConstantInfo.defnInfo add_def).levelParams []
      preVal) [va, vb].toArray) v := by
    rw [hlp, inst_pre, mkAppN_two]; exact hp
  have hargs : ∀ (i : Nat) x y, [a, b][i]? = some x → [va, vb][i]? = some y →
      SrcEval σU CU x y := by
    intro i x y h1 h2
    rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
    · exact ha
    · exact hb
  have h := SrcEval.deltaRec (σ := σU) (C := CU) (c := `Nat.add) (us := [])
    (ci := .defnInfo add_def) (pre := preVal) (as := [a, b]) (vs := [va, vb]) find_add rfl
    casesOn_add atom_add ax_add pre_add (by rw [arity_pre]; decide) (by rw [arity_pre]; rfl) rfl
    hargs hc' hp'
  rwa [mkAppN_two] at h

/-! ## The pre-definition at `σU` -/

/-- `Nat.add.match_1.{1} motPre 2 y altPre1 altPre2` -/
def m5P (y : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motPre) (lit 2)) y) altPre1) altPre2

/-- The arguments of `Nat.casesOn` in `m5P y` after δ and β. -/
def casesArgsP (y : Lean.Expr) : List Lean.Expr :=
  [.lam `x tN (.app (.app motPre (lit 2)) (.bvar 0)) .default, y, .app altPre1 (lit 2),
    .lam n58 tN (.app (.app altPre2 (lit 2)) (.bvar 0)) .default]

theorem casesOn_N : σU.casesOn? `Nat.casesOn = some Nat_ind := by krfl

/-- δ and the five β of `Nat.add.match_1` on `motPre 2 k altPre1 altPre2`, `k` a literal. -/
theorem evU_m5P {k : Nat} {v : Lean.Expr}
    (h : SrcEval σU CU (mkAppN (.const `Nat.casesOn [l1]) (casesArgsP (lit k)).toArray) v) :
    SrcEval σU CU (m5P (lit k)) v := by
  have hns : specialArity σU `Nat.add.match_1 = none := by krfl
  have h0 := evU_delta (c := `Nat.add.match_1) (us := [l1]) (v := match_def) (by krfl)
    (.atom trivial)
  have h1 := SrcEval.beta (nsU_const rfl hns) h0 (.atom (e := motPre) trivial) (.atom trivial)
  have h2 := SrcEval.beta (nsU_const rfl hns) h1 (.lit (k := 2)) (.atom trivial)
  have h3 := SrcEval.beta (nsU_const rfl hns) h2 (.lit (k := k)) (.atom trivial)
  have h4 := SrcEval.beta (nsU_const rfl hns) h3 (.atom (e := altPre1) trivial) (.atom trivial)
  refine SrcEval.beta (nsU_const rfl hns) h4 (.atom (e := altPre2) trivial) ?_
  convert h using 1
  simp +decide only [Pure.instLevels, Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', motPre,
    altPre1, altPre2, casesArgsP, mkAppN, tN, cS, lit, Nat.reduceAdd, ↓reduceIte]
  rfl

/-- The match on `0`: the first alternative, `2`. -/
theorem evU_m5P0 : SrcEval σU CU (m5P (lit 0)) (lit 2) := by
  refine evU_m5P (SrcEval.casesLitZero (c := `Nat.casesOn) (us := [l1])
    (as := casesArgsP (lit 0)) casesOn_N rfl rfl rfl .lit rfl ?_)
  exact .beta (nsU_lam rfl) (.atom trivial) .lit .lit

/-- The match on `k + 1`: the second alternative, `Nat.succ (Nat.add 2 k)`. -/
theorem evU_m5PS (k : Nat) {w : Lean.Expr}
    (hrec : SrcEval σU CU (.app (.app (.const `Nat.add []) (lit 2)) (lit k)) w) :
    SrcEval σU CU (m5P (lit (k + 1))) (.app cS w) := by
  refine evU_m5P (SrcEval.casesLitSucc (c := `Nat.casesOn) (us := [l1])
    (as := casesArgsP (lit (k + 1))) (k := k) casesOn_N rfl rfl rfl .lit rfl ?_)
  have h1 : SrcEval σU CU (.app altPre2 (lit 2)) (.lam `b tN
      (.app cS (.app (.app (.const `Nat.add []) (lit 2)) (.bvar 0))) .default) :=
    .beta (nsU_lam rfl) (.atom trivial) .lit (by
      convert SrcEval.atom (σ := σU) (C := CU) (e := .lam `b tN
        (.app cS (.app (.app (.const `Nat.add []) (lit 2)) (.bvar 0))) .default) trivial using 1
      simp [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', tN, cS, lit])
  have h2 : SrcEval σU CU (.app (.app altPre2 (lit 2)) (lit k)) (.app cS w) :=
    .beta (nsU_lam rfl) h1 .lit (by
      convert evU_succ hrec using 1
      simp [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', cS, lit])
  exact .beta (nsU_lam rfl) (.atom trivial) .lit (by
    convert h2 using 1
    simp [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', altPre2, tN, cS, lit])

/-- `preVal 2 k ⇓ v` when its match on `k` evaluates to `v`: two β. -/
theorem evU_pre_of {k : Nat} {v : Lean.Expr} (hm : SrcEval σU CU (m5P (lit k)) v) :
    SrcEval σU CU (.app (.app preVal (lit 2)) (lit k)) v := by
  have h1 : SrcEval σU CU (.app preVal (lit 2)) (.lam x14 tN
      (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motPre) (lit 2)) (.bvar 0))
        altPre1) altPre2) .default) :=
    .beta (nsU_lam rfl) (.atom trivial) .lit (by
      convert SrcEval.atom (σ := σU) (C := CU) (e := .lam x14 tN
        (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motPre) (lit 2)) (.bvar 0))
          altPre1) altPre2) .default) trivial using 1
      simp +decide [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', motPre, altPre1, altPre2,
        tN, cS, lit])
  refine .beta (nsU_lam rfl) h1 .lit ?_
  convert hm using 1
  simp +decide [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', motPre, altPre1, altPre2, m5P,
    tN, cS, lit]

/-! ## The conversion premises -/

theorem subU : SubEnv σU.decls P := fun _ => CollectSub.findDecl_of_view hview
theorem subA : SubEnv σ.decls P := fun _ => CollectSub.findDecl_of_view hview

/-- The translation of `preVal 2 k`: `preValM` applied to the literals' constructor chains. -/
def preAppM (k : Nat) : Metalean.Expr ζ13 0 0 :=
  .app (.app preValM (natLitM n13 2)) (natLitM n13 k)

theorem tr_preApp (k : Nat) :
    TrM E B [] .nil [] (.app (.app preVal (lit 2)) (lit k)) (preAppM k) :=
  TrM.app (by rintro ⟨c, us, b, h, -⟩; cases h)
    (TrM.app (by rintro ⟨c, us, b, h, -⟩; cases h) tr_preVal (TrM.lit B13_N B13_z B13_s))
    (TrM.lit B13_N B13_z B13_s)

theorem preAppM_typed (k : Nat) : E[.nil] ⊢ preAppM k : EraseProof.Test.NVL.mN n13 := by
  have h1 := app_typed' preValM_typed (natLitM_typed 2) (by arsx [addTyM])
  arsx at h1
  exact typed_of_eq (app_typed' h1 (natLitM_typed k) (by arsx)) (by arsx)

/-- The conversion premise of `deltaRec` at the call `Nat.add 2 k`, given `preVal 2 k ⇓ V k`:
every typed translation of `Nat.add 2 k` is definitionally equal, at its type, to `preAppM k`.
Subject reduction (`SrcEval.defeq`) on the kernel evaluation (`ev_kernel`) and on `hp` gives two
translations of `V k`, which are congruent (`TrM.dcong`, `DCong.defeq₂`). Reference: the
conclusion of `subject_reduction_eval` (`MR P/PCUICWcbvEval.v`). -/
theorem conv_add {k : Nat} (hp : SrcEval σU CU (.app (.app preVal (lit 2)) (lit k)) (V k)) :
    CU (.app (.app (.const `Nat.add []) (lit 2)) (lit k)) (.app (.app preVal (lit 2)) (lit k)) := by
  intro t T ht hT
  obtain ⟨w, hw, hd⟩ := SrcEval.defeq henv hwf subA ht hT (ev_kernel k)
  obtain ⟨w', hw', hd'⟩ := SrcEval.defeq henv hwf subU (tr_preApp k) (preAppM_typed k) hp
  have hww := (TrM.dcong hw hw' (LocCong.refl [])).defeq₂ hwf SrcDefeq.nil_ok SrcDefeq.nil_ok
    (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hd'.right⟩ hd.right
  exact ⟨_, tr_preApp k, SrcDefeq.dtrans hwf hd (SrcDefeq.dtrans hwf hww hd'.symm)⟩

/-! ## The calls and the term -/

/-- `preVal 2 k ⇓ V k` and `Nat.add 2 k ⇓ V k` at `σU`, for every `k`, by induction: the match on
`k + 1` calls `Nat.add 2 k`. -/
theorem ev_add : ∀ k, SrcEval σU CU (.app (.app preVal (lit 2)) (lit k)) (V k) ∧
    SrcEval σU CU (.app (.app (.const `Nat.add []) (lit 2)) (lit k)) (V k)
  | 0 => by
    have hp := evU_pre_of evU_m5P0
    exact ⟨hp, deltaRec_add .lit .lit (conv_add hp) hp⟩
  | k + 1 => by
    have hp : SrcEval σU CU (.app (.app preVal (lit 2)) (lit (k + 1))) (V (k + 1)) :=
      evU_pre_of (evU_m5PS k (ev_add k).2)
    exact ⟨hp, deltaRec_add .lit .lit (conv_add hp) hp⟩

/-- `hev`: `e = Nat.add 2 3` evaluates to `Nat.succ (Nat.succ (Nat.succ 2))` at `σU`, through
`deltaRec` on the numerals' literals. -/
theorem hev : SrcEval σU CU e v5 :=
  deltaRec_add (evU_numK 2) (evU_numK 3) (conv_add (ev_add 3).1) (ev_add 3).1

end EraseProof.Test.NVU
