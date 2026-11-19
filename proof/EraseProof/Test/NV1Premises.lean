import EraseProof.Statements
import EraseProof.Test.NV1Run
import EraseProof.Test.CasesOnVal

/-!
# NV-1: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` holds on the program of `Test/NV1Data.lean`, each
stated as the theorem of that name (`hfrag` and `hrun` are `Test/NV1Run.lean`'s `hcollect` and
`hrun`). They are checked in the kernel, except the equation of the pure fold inside `hacc`
(`checkDeclsPure … = .ok envNV1`), which `hacc` takes as its premise and which a `#guard` checks by
compiled evaluation, so the build fails if con-leche's fold disagrees: the kernel cannot evaluate
the block installer (DV-40). `krfl` (`Test/Run.lean`) is an auxiliary theorem `a = b` by `Eq.refl a`.
NV-1 has no mark, so `hcert` needs no compiled evaluation.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV1

namespace EraseProof.Test.NV1

/-! ## con-leche's records and environment (A-2/A-3; `k` = con-leche form) -/

def nm (s : String) : ConLeche.Name := .str .anonymous s
def nm2 (a b : String) : ConLeche.Name := .str (.str .anonymous a) b
def kU : ConLeche.Level := .param (nm "u")
def kB : ConLeche.Expr := .const (nm "B") []
def kF : ConLeche.Expr := .const (nm2 "B" "f") []
def kT : ConLeche.Expr := .const (nm2 "B" "t") []
def kMotTy : ConLeche.Expr := .forallE kB (.sort kU)
def kRecType : ConLeche.Expr :=
  .forallE kMotTy (.forallE (.app (.bvar 0) kF) (.forallE (.app (.bvar 1) kT)
    (.forallE kB (.app (.bvar 3) (.bvar 0)))))
def kRule (c : String) (pick : Nat) : ConLeche.RecRule :=
  { ctor := nm2 "B" c, nfields := 0, fire := .plain,
    rhs := .lam kMotTy (.lam (.app (.bvar 0) kF) (.lam (.app (.bvar 1) kT) (.bvar pick))) }
def kBlock : ConLeche.Declaration :=
  .indDecl
    [ .indInfo ⟨nm "B", [], .sort (.succ .zero)⟩ {}
    , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
    , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
    , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0] ] 0
def kCasesOnTy : ConLeche.Expr :=
  .forallE kMotTy (.forallE kB (.forallE (.app (.bvar 1) kF) (.forallE (.app (.bvar 2) kT)
    (.app (.bvar 3) (.bvar 2)))))
def kCasesOnVal : ConLeche.Expr :=
  .lam kMotTy (.lam kB (.lam (.app (.bvar 1) kF) (.lam (.app (.bvar 2) kT)
    (.app (.app (.app (.app (.const (nm2 "B" "rec") [kU]) (.bvar 3)) (.bvar 1)) (.bvar 0)) (.bvar 2)))))
def kNegVal : ConLeche.Expr :=
  .lam kB (.app (.app (.app (.app (.const (nm2 "B" "casesOn") [.succ .zero]) (.lam kB kB)) (.bvar 0)) kT) kF)

/-- con-leche's input for NV-1 (`DeclsOf? P`). -/
def nv1full : List ConLeche.Declaration :=
  [kBlock, .defnDecl ⟨nm2 "B" "casesOn", [nm "u"], kCasesOnTy⟩ kCasesOnVal .abbrev,
   .defnDecl ⟨nm2 "B" "neg", [], .forallE kB kB⟩ kNegVal (.regular 1)]

/-- NV-1's accepted environment, newest first (the fold's result, `#guard` below). -/
def envNV1 : ConLeche.Env :=
  ⟨[ .defnInfo ⟨nm2 "B" "neg", [], .forallE kB kB⟩ kNegVal (.regular 1)
   , .defnInfo ⟨nm2 "B" "casesOn", [nm "u"], kCasesOnTy⟩ kCasesOnVal .abbrev
   , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0]
   , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
   , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
   , .indInfo ⟨nm "B", [], .sort (.succ .zero)⟩
       { eta := false, all := [nm "B"], nparams := 0, nIdx := 0,
         ctors := [nm2 "B" "f", nm2 "B" "t"], neverZero := true } ], []⟩

/- `hfold`, the premise of the instance, by compiled evaluation: the fold accepts `nv1full` with
result `envNV1` (`ConstantInfo` and `ProjTable` have `DecidableEq`). The kernel cannot evaluate it
(`Std.HashMap`s hashed by the opaque `mixHash` in the block installer, A-2 B3). -/
#guard match ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    nv1full with
  | .ok env => decide (env.consts = envNV1.consts) && decide (env.tables = envNV1.tables)
  | .error _ => false

/-- the evaluation environment of the final theorem -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

/-! ## `hacc` from `hfold`: the bridge by the kernel -/

theorem decls : DeclsOf? P = some nv1full := by krfl

theorem hacc (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel)
    [] nv1full = .ok envNV1) : ConLecheAccepts P envNV1 :=
  ⟨nv1full, decls, hfold, by krfl, by krfl⟩

/-! ## `hty`: con-leche infers a type for `e` at `envNV1` -/

theorem hty : CLTyped envNV1 e := ⟨.app (.const (nm2 "B" "neg") []) kF, 100, kB, by krfl, by krfl⟩

theorem hclean : NoMarkKeys e = true := by krfl

/-! ## `hview`, `hnopre`, `hfrag`, `hrun` -/

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
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none (by krfl)] at hp <;> cases hp

/-- the ported `NV1.hcollect` -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-- `NoPreDefs` on the closure, by `decide` on its definition. -/
theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-- The closure is part of the program (the conclusion of `collectDeps_sub` on NV-1). -/
theorem sub : SubEnv D P := by
  intro ci h
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> krfl

/-! ## `hmark`: the eraser's decisions on `e`, by symbolic evaluation of the oracle

NV-1 has no mark: the oracle keeps every node the traversal visits (`e`, `B.f`; in `B.neg`'s value,
the λ, the `casesOn` spine, the discriminant `b` and the alternatives), and the motive is not
visited. So `ê = e`, and δ marks `B.neg`'s value as itself. -/

/-- A constructor without arguments is kept and has no mark (`visitConstructor`). -/
theorem mark_ctor {decls : List ConstantInfo} {ls : List Local} {c : Name}
    (ho : oracle decls ls (.const c []) = .ok false) (ha : markArity? decls cfg c = some 0)
    (hi : Pure.inferType ⟨decls⟩ oracleFuel ls [] (.const c []) = .ok tB)
    (hc : casesInfo? decls c = none) (hr : ctorArity? decls c = some 0) :
    MarkOf decls cfg ls (.const c []) (.const c []) :=
  MarkOf.special (c := c) (us := []) (as := []) ho ha hi
    (MarkEta.sat (Nat.le_refl 0) (MarkSat.ctor (as := []) (âs := []) hc hr rfl (by simp)))

theorem hmark : MarkOf D cfg [] e e := by
  refine MarkOf.constApp (c := `B.neg) (us := []) (as := [cF]) (âs := [cF]) (by krfl) (by krfl) rfl ?_
  intro i a â ha hâ
  rcases i with _ | i <;> simp at ha hâ
  subst ha hâ
  exact mark_ctor (by krfl) (by krfl) (by krfl) (by krfl) (by krfl)

/-- `findDecl P` on the constructors -/
theorem find_f : findDecl P `B.f = some (.ctorInfo Bf_ctor) := by krfl
theorem find_t : findDecl P `B.t = some (.ctorInfo Bt_ctor) := by krfl

/-- the body of `negVal` under its binder -/
def negBody : Expr :=
  .app (.app (.app (.app (.const `B.casesOn [.succ .zero]) motNeg) (.bvar 0)) cT) cF

/-- `findDecl D` on the constructors -/
theorem findD_f : findDecl D `B.f = some (.ctorInfo Bf_ctor) := by krfl
theorem findD_t : findDecl D `B.t = some (.ctorInfo Bt_ctor) := by krfl

/-- `B.neg`'s value is kept as it is: `fun b => B.casesOn.{1} (fun x => B) b B.t B.f`, the λ, the
`casesOn` erased to a λ□ `case` on `b` (`MarkSat.cases`) and its alternatives without fields; over
the program and over the closure. -/
theorem mark_neg {decls : List ConstantInfo} (hd : decls = P ∨ decls = D) :
    MarkOf decls cfg [] negVal negVal := by
  have hf : findDecl decls `B.f = some (.ctorInfo Bf_ctor) := by
    rcases hd with rfl | rfl; exact find_f; exact findD_f
  have ht : findDecl decls `B.t = some (.ctorInfo Bt_ctor) := by
    rcases hd with rfl | rfl; exact find_t; exact findD_t
  refine MarkOf.lam (n := `b) (A := tB) (b := negBody) (bi := .default) (x := xb) (bM := bodyNeg)
    (by rcases hd with rfl | rfl <;> krfl) (by simp [Fresh, FVarsIn, negBody, motNeg, tB, cT, cF]) ?_
  show MarkOf decls cfg [lb] bodyNeg bodyNeg
  refine MarkOf.special (c := `B.casesOn) (us := [.succ .zero]) (as := [motNeg, .fvar xb, cT, cF])
    (ar := 4) (T := .app motNeg (.fvar xb)) (by rcases hd with rfl | rfl <;> krfl)
    (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl)
    (MarkEta.sat (by decide) ?_)
  refine MarkSat.cases (iv := B_ind) (cd := B_casesOn) (u := .succ .zero) (pre := [motNeg])
    (d := .fvar xb) (dM := .fvar xb) (alts := [cT, cF]) (âlts := [cT, cF]) (extra := []) (êxtra := [])
    (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl) (by decide) rfl rfl
    (by rcases hd with rfl | rfl <;> krfl) (fun h => by cases h)
    (MarkOf.fvar (by rcases hd with rfl | rfl <;> krfl)) rfl ?_ ?_ ?_ rfl (by simp)
  · intro i cn h
    rcases i with _ | _ | i <;> simp [B_ind] at h <;> subst h
    · exact ⟨_, hf⟩
    · exact ⟨_, ht⟩
  · intro i alt h
    rcases i with _ | _ | i <;> simp at h <;> subst h
    · exact ⟨tB, by rcases hd with rfl | rfl <;> krfl⟩
    · exact ⟨tB, by rcases hd with rfl | rfl <;> krfl⟩
  · intro i cn cv alt âlt T h1 h2 h3 h4 _
    rcases i with _ | _ | i <;> simp [B_ind] at h1 h3 h4 <;> subst h1 h3 h4
    · rw [hf] at h2; cases h2
      exact MarkAlt.done (mark_ctor (by rcases hd with rfl | rfl <;> krfl)
        (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl)
        (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl))
    · rw [ht] at h2; cases h2
      exact MarkAlt.done (mark_ctor (by rcases hd with rfl | rfl <;> krfl)
        (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl)
        (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl))

/-! ## `hcert`: con-leche certifies every mark of the input and of the closure's values: there is none

`ê = e` has no mark; the closure's values are `B.neg`'s and `B.casesOn`'s, and their markings
(`mark_neg`, `mark_casesOnVal`) have no mark. -/

/-- con-leche types the input and the closure's marked values as wholes, at `checkFuel`. -/
theorem typedAt_e : CLTypedAt envNV1 e := ⟨.app (.const (nm2 "B" "neg") []) kF, kB, by krfl, by krfl⟩
theorem typedAt_neg : CLTypedAt envNV1 negVal := ⟨kNegVal, .forallE kB (.app (.lam kB kB) (.bvar 0)), by krfl, by krfl⟩
theorem typedAt_casesOn : CLTypedAt envNV1 casesOnVal := ⟨kCasesOnVal, kCasesOnTy, by krfl, by krfl⟩

theorem hcert : ProgCert envNV1 D cfg e := by
  refine ⟨typedAt_e, ⟨trivial, trivial⟩, ?_⟩
  intro ci hci v hv
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  · exact ⟨_, mark_casesOnVal (.inl rfl), typedAt_casesOn, by simp [MarksCert, casesOnVal]⟩
  · exact ⟨_, mark_neg (.inr rfl), typedAt_neg, by simp [MarksCert, negVal, tB, cT, cF]⟩

/-! ## `hev`: an explicit derivation of `B.neg B.f ⇓ B.t`, its certificates by the kernel at
`envNV1` (none needs ι: the motive is constant) -/

/-- the evaluation environment of `hev`: the closure -/
abbrev σD : EvalEnv := evalEnvOf view cfg D

/-- `CLOk` of a constructor value -/
theorem ok_f : CLOk envNV1 cF := ⟨⟨kF, 100, kB, by krfl, by krfl⟩, kF, 100, kB, by krfl, by krfl⟩
theorem ok_t : CLOk envNV1 cT := ⟨⟨kT, 100, kB, by krfl, by krfl⟩, kT, 100, kB, by krfl, by krfl⟩

/-- the β-redex `(fun b => B.casesOn.{1} (fun x => B) b B.t B.f) B.f` -/
theorem ok_beta : CLOk envNV1 (.app negVal cF) :=
  ⟨⟨.app kNegVal kF, 100, .app (.lam kB kB) kF, by krfl, by krfl⟩, .app kNegVal kF, 100, .app (.lam kB kB) kF, by krfl, by krfl⟩

/-- the `casesIota` redex `B.casesOn.{1} (fun x => B) B.f B.t B.f` -/
def casesRedex : Expr := mkAppN (.const `B.casesOn [.succ .zero]) #[motNeg, cF, cT, cF]

theorem ok_cases : CLOk envNV1 casesRedex :=
  ⟨⟨.app (.app (.app (.app (.const (nm2 "B" "casesOn") [.succ .zero]) (.lam kB kB)) kF) kT) kF, 100,
    .app (.lam kB kB) kF, by krfl, by krfl⟩, .app (.app (.app (.app (.const (nm2 "B" "casesOn") [.succ .zero]) (.lam kB kB)) kF) kT) kF, 100,
    .app (.lam kB kB) kF, by krfl, by krfl⟩

/-- A constructor without arguments evaluates to itself (`SrcEval.ctor`). -/
theorem ev_ctor {c : Name} {cv : ConstructorVal} (hd : findDecl σD.decls c = some (.ctorInfo cv))
    (hn : cv.numParams + cv.numFields = 0) (hok : CLOk envNV1 (.const c [])) :
    SrcEval envNV1 σD (.const c []) (.const c []) :=
  SrcEval.ctor (c := c) (us := []) (as := []) (vs := []) hd hn.symm rfl (by simp) hok

theorem ev_f : SrcEval envNV1 σD cF cF := ev_ctor findD_f rfl ok_f
theorem ev_t : SrcEval envNV1 σD cT cT := ev_ctor findD_t rfl ok_t

/-- con-leche's ι step at `B.rec` fires on `B.f` with no certificate: `B` is never `Prop`. -/
theorem iota_f : IotaNoCertAt envNV1 `B cF :=
  ⟨`B.f, [], ⟨nm2 "B" "rec", [nm "u"], kRecType⟩, 3, 3, false, [kRule "f" 1, kRule "t" 0],
    kRule "f" 1, ⟨nm2 "B" "f", [], kB⟩, 0, 0, nm "B", rfl, by krfl, by krfl, by krfl, by krfl⟩

/-- ι: the major `B.f` selects the alternative `B.t` -/
theorem ev_cases : SrcEval envNV1 σD casesRedex cT :=
  SrcEval.casesIota (c := `B.casesOn) (us := [.succ .zero]) (iv := B_ind) (as := [motNeg, cF, cT, cF])
    (m := cF) (mv := cF) (i := 0) (fs := []) (alt := cT) (by krfl) rfl rfl ev_f
    ⟨`B.f, [], Bf_ctor, [], findD_f, rfl, rfl, rfl, rfl, rfl⟩ ok_cases iota_f rfl ev_t

theorem not_short {x : Expr} {c : Name} {us : List Level} (h : x.getAppFn = .const c us)
    (hs : specialArity σD c = none) : ¬ ShortSpine σD x := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  rw [h] at h1
  cases h1
  rw [hs] at h2
  cases h2

theorem hev : SrcEval envNV1 σD e cT :=
  SrcEval.beta (n := `b) (A := tB) (b := negBody) (bi := .default) (not_short rfl (by krfl))
    (SrcEval.delta (ci := .defnInfo neg_def) (body := negVal) (by krfl) (mark_neg (.inr rfl))
      (SrcEval.atom trivial))
    ev_f ok_beta ev_cases

/-! ## The marks coincide with the `□`s of `hrun`'s output: none and none

`Erases` relates a term to `□` exactly at its `erase` marks (`Erases.box`). `ê = e` and `B.neg`'s
marked value erase, without `Erases.box`, to the main term `t0` and the body `negL` that `p0` holds,
which contain no `□`. -/

theorem erases_ctor {Γ : List CtxBinder} {c : Name} {cv : ConstructorVal}
    (hd : findDecl σ.decls c = some (.ctorInfo cv))
    (hp : σ.propInd cv.induct = false) (hi : IndIdOf σ cv.induct = some iidB)
    (hn : cv.numParams + cv.numFields = 0) :
    Erases (CLCert envNV1) σ Γ (.const c []) (.construct iidB cv.cidx []) :=
  Erases.ctor (as := []) (as' := []) hd hp hi (by omega) rfl (by simp)

theorem not_special {x : Expr} {c : Name} {us : List Level} {d : DefinitionVal}
    (h : x.getAppFn = .const c us) (hd : findDecl σ.decls c = some (.defnInfo d))
    (hc : σ.casesOn? c = none) : ¬ SpecialSpine σ x := by
  rintro ⟨c', us', h1, h2⟩
  rw [h] at h1
  cases h1
  rcases h2 with ⟨cv, h⟩ | h | ⟨qv, h, -⟩ | ⟨rv, h⟩ <;> simp_all

theorem find_neg : findDecl σ.decls `B.neg = some (.defnInfo neg_def) := by krfl

theorem coincide_e : Erases (CLCert envNV1) σ [] e t0 :=
  Erases.app (not_special rfl find_neg (by krfl))
    (Erases.const (by krfl) (by krfl) fun rv h => by rw [find_neg] at h; cases h)
    (erases_ctor find_f (by krfl) (by krfl) rfl)

theorem negL_eq : negL = .lambda (binderNameOf `b)
    (.case (iidB, 0) (.bvar 0) [([], .construct iidB 1 []), ([], .construct iidB 0 [])]) := by krfl

theorem coincide_neg : Erases (CLCert envNV1) σ [] negVal negL := by
  rw [negL_eq]
  refine Erases.lam (Erases.cases (c := `B.casesOn) (us := [.succ .zero]) (iv := B_ind)
    (pre := [motNeg]) (alts := [cT, cF]) (extra := []) (extra' := []) (by krfl) (by krfl) rfl rfl
    Erases.bvar rfl ?_ ?_ rfl (by simp))
  · intro i cn h
    rcases i with _ | _ | i <;> simp [B_ind] at h <;> subst h <;> krfl
  · intro i cn alt br k h1 h2 h3 h4
    rcases i with _ | _ | i <;> simp [B_ind] at h1 h2 h3 <;> subst h1 h2 h3
    · rw [show ctorFields σ `B.f = some 0 by krfl] at h4; cases h4
      exact ErasesAlt.done (erases_ctor find_t (by krfl) (by krfl) rfl)
    · rw [show ctorFields σ `B.t = some 0 by krfl] at h4; cases h4
      exact ErasesAlt.done (erases_ctor find_f (by krfl) (by krfl) rfl)

/-- The marking δ uses in `hev` erases, with certified boxes, to the body `p0` holds for `B.neg`,
the one constant of `p0`: the witness half of `ErasesDecl` (its `∀` half follows with
`MarkOf.det`). -/
theorem decl_neg : MarkOf σ.decls σ.cfg [] negVal negVal ∧ Erases (CLCert envNV1) σ [] negVal negL :=
  ⟨mark_neg (.inl rfl), coincide_neg⟩

end EraseProof.Test.NV1
