import EraseProof.Statements
import EraseProof.Test.NV0Data
import EraseProof.Test.Run

/-!
# NV-0: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` (`hacc`, `hty`, `hclean`, `hview`, `hfrag`, `hnopre`,
`hrun`, `hmark`, `hcert`, `hev`) holds on the program of `Test/NV0Data.lean`, each stated as the
theorem of that name, in the kernel. `krfl` (`Test/Run.lean`) is an auxiliary theorem `a = b` by
`Eq.refl a`, checked by the kernel only. NV-0 has no inductive type, so the fold equation inside
`hacc` is also proved in the kernel (compare DV-40).
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV0

namespace EraseProof.Test.NV0

/-! ## con-leche's records and environment -/

def nm (s : String) : ConLeche.Name := .str .anonymous s
def cTT : ConLeche.Expr := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1))
def cIdT : ConLeche.Expr := .lam (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0))
def cU : ConLeche.Level := .param (nm "u")

def nv0ds : List ConLeche.Declaration :=
  [ .defnDecl ⟨nm "nv0id", [nm "u"], .forallE (.sort cU) (.forallE (.bvar 0) (.bvar 1))⟩
      (.lam (.sort cU) (.lam (.bvar 0) (.bvar 0))) (.regular 1)
  , .defnDecl ⟨nm "nv0main", [], cTT⟩
      (.app (.app (.const (nm "nv0id") [.succ (.succ .zero)]) cTT) cIdT) (.regular 2) ]

/-- NV-0's accepted environment, newest first. -/
def envNV0 : ConLeche.Env :=
  ⟨[ .defnInfo ⟨nm "nv0main", [], cTT⟩
       (.app (.app (.const (nm "nv0id") [.succ (.succ .zero)]) cTT) cIdT) (.regular 2)
   , .defnInfo ⟨nm "nv0id", [nm "u"], .forallE (.sort cU) (.forallE (.bvar 0) (.bvar 1))⟩
       (.lam (.sort cU) (.lam (.bvar 0) (.bvar 0))) (.regular 1) ], []⟩

/-- the evaluation environment of the final theorem -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

/-- `nv0id.{2}`'s δ-unfolded value: `fun (α : Sort 2) (a : α) => a` -/
def id2 : Expr := idLam (.succ (.succ .zero))

/-- the first β-redex: `nv0id.{2}`'s value applied to the frozen type argument -/
def beta1 : Expr := .app id2 (markErase tT)
/-- its contractum, `fun (a : □T) => a` -/
def lamA : Expr := .lam `a (markErase tT) (.bvar 0) .default
/-- the second β-redex -/
def beta2 : Expr := .app lamA idT


/-! ## `hacc`: con-leche's pure fold accepts `P`, all four conjuncts by the kernel -/

theorem decls : DeclsOf? P = some nv0ds := by krfl
theorem fold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    nv0ds = .ok envNV0 := by krfl
theorem hacc : ConLecheAccepts P envNV0 := ⟨nv0ds, decls, fold, by krfl, by krfl⟩

/-! ## `hty`: con-leche infers a type for `e` -/

theorem hty : CLTyped envNV0 e := ⟨.const (nm "nv0main") [], 100, cTT, by krfl, by krfl⟩

theorem hclean : NoMarkKeys e = true := by krfl

/-! ## `hview`, `hnopre` -/

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
  rcases h with rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none (by krfl)] at hp <;> cases hp

/-! ## `hfrag`: the fragment test's closure -/

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo := [.defnInfo id_def, .defnInfo main_def]

theorem hfrag : collectDeps view cfg e = .ok D := by krfl

/-- `NoPreDefs` on the closure, by `decide` on its definition. -/
theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-- The closure is part of the program (the conclusion of `collectDeps_sub` on NV-0). -/
theorem sub : SubEnv D P := by
  intro ci h
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> krfl

/-! ## `hrun`: the entry point of `#erase` on NV-0

As `Test/NV1Run.lean`: the pure path's run is evaluated by the kernel (`krfl`) between the
accesses to the traversal's `Std.HashMap`s (`constants`), which are rewritten with the map lemmas.
-/

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

def knId : Kername := toKername `nv0id
def knMain : Kername := toKername `nv0main
/-- the erasure of `fun α a => a` (the binder names stay symbolic: `binderNameOf` reads
`Name.toString`, which the kernel does not evaluate; `#eval` below shows `.anon`, `.named "a"`) -/
def idL : LBTerm := .lambda (binderNameOf `α) (.lambda (binderNameOf `a) (.bvar 0))
/-- the erasure of `nv0main`'s value: the type argument is `□` -/
def mainL : LBTerm := .app (.app (.const knId) .box) idL

variable {st : ErasureState} {dc : Name} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}

theorem idVal_run {n : Nat} :
    (visitExpr (m := PureM) (n + 5) (idLam (.param `u))).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((idL, st), ⟨2⟩) := by krfl

/-- The state after erasing `nv0id`. -/
def stId (st : ErasureState) : ErasureState :=
  { st with constants := st.constants.insert `nv0id knId,
            gdecls := (knId, .constantDecl ⟨some idL⟩) :: st.gdecls }

theorem visitMutual_id_run {n : Nat} :
    (visitMutual (m := PureM) (n + 6) `nv0id).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok (((), stId st), ⟨2⟩) := by krfl

theorem kername_id_run {n : Nat} (hc : st.constants[`nv0id]? = none) :
    (get_constant_kername (m := PureM) (n + 7) `nv0id).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((knId, stId st), ⟨2⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok visitMutual_id_run
  apply bind_ok rfl
  simp only [stId, Std.HashMap.getElem?_insert_self]
  rfl

theorem withApp_mainVal {γ : Sort _} (k : Expr → Array Expr → γ) :
    mainVal.withApp k = k (.const `nv0id [.succ (.succ .zero)]) #[tT, idT] := by krfl

theorem mainVal_run {n : Nat} (hc : st.constants[`nv0id]? = none) :
    (visitExpr (m := PureM) (n + 11) mainVal).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((mainL, stId st), ⟨4⟩) := by
  rw [mainVal, visitExpr, ← mainVal]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 9) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mainVal]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo id_def)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const knId) (st' := stId st) (ps' := ⟨2⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    apply bind_ok (kername_id_run hc)
    rfl
  krfl

/-- The state after erasing `nv0main`. -/
def stMain (st : ErasureState) : ErasureState :=
  { stId st with constants := (stId st).constants.insert `nv0main knMain,
                 gdecls := (knMain, .constantDecl ⟨some mainL⟩) :: (stId st).gdecls }

theorem visitMutual_main_run {n : Nat} (hc : st.constants[`nv0id]? = none) :
    (visitMutual (m := PureM) (n + 12) `nv0main).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok (((), stMain st), ⟨4⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := mainL) (st' := stId st) (ps' := ⟨4⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := mainVal) (st' := st) (ps' := ⟨0⟩) rfl ?_
    exact mainVal_run (L := L) hc
  rfl

theorem kername_main_run {n : Nat} (hm : st.constants[`nv0main]? = none)
    (hc : st.constants[`nv0id]? = none) :
    (get_constant_kername (m := PureM) (n + 13) `nv0main).runPure st ⟨L, [], F, {}, dc⟩ pc ⟨0⟩ =
      .ok ((knMain, stMain st), ⟨4⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hm]
  apply bind_ok (visitMutual_main_run hc)
  apply bind_ok rfl
  simp only [stMain, Std.HashMap.getElem?_insert_self]
  rfl

/-- The erasure of `e`. -/
def t0 : LBTerm := .const knMain

theorem e_run {n : Nat} (hm : st.constants[`nv0main]? = none)
    (hc : st.constants[`nv0id]? = none) :
    (visitExpr (m := PureM) (n + 17) e).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((t0, stMain st), ⟨4⟩) := by
  rw [e, visitExpr, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 15) _).runPure _ _ _ _ = _
  rw [visitConstApp, e, withApp_const]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo main_def)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const knMain) (st' := stMain st) (ps' := ⟨4⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    apply bind_ok (kername_main_run hm hc)
    rfl
  krfl

/-- The program `#erase` emits for NV-0. -/
def p0 : Program :=
  .untyped [(knMain, .constantDecl ⟨some mainL⟩), (knId, .constantDecl ⟨some idL⟩)] (some t0)

theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 17) + 17 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 17 + 17) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((t0, stMain {}), ⟨4⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

/-- `#erase`'s entry point on NV-0 returns `p0` and no constant to inline. -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hfrag, hpure]


/-! ## `hmark`: the eraser's decisions on `e`, by symbolic evaluation of the oracle

`e` is the constant `nv0main`: the oracle keeps it and it has no rule of its own, so `ê = e`. The
marks of NV-0 are in `nv0main`'s value, which δ (`SrcEval.delta`) marks with `MarkOf` over `P`:
the type argument of `nv0id` is frozen (`mainM`), and nothing else is marked. -/

theorem hmark : MarkOf D cfg [] e e :=
  MarkOf.constApp (c := `nv0main) (us := []) (as := []) (âs := []) (by krfl) (by krfl) rfl
    (by intro i a â h; simp at h)

/-- two fresh variables -/
def x0 : FVarId := ⟨`x0⟩
def x1 : FVarId := ⟨`x1⟩

/-- `fun (α : Sort s) (a : α) => a` is kept, at `s = u` (`nv0id`'s value) and `s = 1`, over the
program and over the closure. -/
theorem mark_idLam {decls : List ConstantInfo} (hd : decls = P ∨ decls = D) (s : Level)
    (hs : s = .param `u ∨ s = 1) : MarkOf decls cfg [] (idLam s) (idLam s) := by
  have h₀ : oracle decls [] (idLam s) = .ok false := by
    rcases hd with rfl | rfl <;> rcases hs with rfl | rfl <;> krfl
  have h₁ : oracle decls [⟨x0, `α, .sort s, none⟩] (.lam `a (.fvar x0) (.bvar 0) .default) = .ok false := by
    rcases hd with rfl | rfl <;> rcases hs with rfl | rfl <;> krfl
  have h₂ : oracle decls [⟨x1, `a, .fvar x0, none⟩, ⟨x0, `α, .sort s, none⟩] (.fvar x1) = .ok false := by
    rcases hd with rfl | rfl <;> rcases hs with rfl | rfl <;> krfl
  exact MarkOf.lam (x := x0) h₀ (by simp [Fresh, FVarsIn])
    (MarkOf.lam (x := x1) h₁ (by simp [Fresh, FVarsIn, Expr.instantiate1', x0, x1]) (MarkOf.fvar h₂))

/-- `nv0main`'s value marked: the type argument frozen. -/
def mainM : Expr := .app (.app (.const `nv0id [.succ (.succ .zero)]) (markErase tT)) idT

theorem mark_main {decls : List ConstantInfo} (hd : decls = P ∨ decls = D) :
    MarkOf decls cfg [] mainVal mainM := by
  refine MarkOf.constApp (c := `nv0id) (us := [.succ (.succ .zero)]) (as := [tT, idT])
    (âs := [markErase tT, idT]) (by rcases hd with rfl | rfl <;> krfl)
    (by rcases hd with rfl | rfl <;> krfl) rfl ?_
  intro i a â ha hâ
  rcases i with _ | _ | i <;> simp at ha hâ <;> subst ha hâ
  · exact MarkOf.erase (by rcases hd with rfl | rfl <;> krfl)
  · exact mark_idLam hd 1 (.inr rfl)

/-! ## `hcert`: con-leche certifies every mark of the emitted program

`ê = e` has no mark. The emitted environment holds bodies for `nv0id` (no mark) and `nv0main`, whose
one mark is the type argument `(α : Type) → α → α` of `nv0id`, at the top (no enclosing binder):
con-leche types it with a sort, so it is a type former (`CLVerdict`, first disjunct). -/

/-- the type of `(α : Type) → α → α` -/
def sortTT : ConLeche.Expr := .sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))

theorem cert_tT : CLCert envNV0 [] tT :=
  ⟨cTT, 0, cTT, sortTT, sortTT, by krfl, by krfl, rfl, by krfl, .inl (by krfl)⟩

/-- con-leche types the marked input and the marked bodies as wholes, at `checkFuel`. -/
theorem typedAt_e : CLTypedAt envNV0 e := ⟨.const (nm "nv0main") [], cTT, by krfl, by krfl⟩
theorem typedAt_id : CLTypedAt envNV0 (idLam (.param `u)) :=
  ⟨.lam (.sort cU) (.lam (.bvar 0) (.bvar 0)), .forallE (.sort cU) (.forallE (.bvar 0) (.bvar 1)),
    by krfl, by krfl⟩
theorem typedAt_main : CLTypedAt envNV0 mainM :=
  ⟨.app (.app (.const (nm "nv0id") [.succ (.succ .zero)]) cTT) cIdT, cTT, by krfl, by krfl⟩

theorem hcert : ProgCert envNV0 D cfg p0 e := by
  refine ⟨typedAt_e, trivial, ?_⟩
  intro lenv t _ ci hci v cb hv _ _
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl <;> cases hv
  · exact ⟨_, mark_idLam (.inr rfl) _ (.inl rfl), typedAt_id, trivial⟩
  · exact ⟨_, mark_main (.inr rfl), typedAt_main, ⟨trivial, cert_tT⟩, trivial⟩

/-! ## `hev`: an explicit derivation of `e ⇓ fun α a => a`, its certificates by the kernel at
`envNV0` -/

/-- the evaluation environment of `hev`: the closure -/
abbrev σD : EvalEnv := evalEnvOf view cfg D

theorem not_short {x : Expr} {c : Name} {us : List Level} (h : x.getAppFn = .const c us)
    (hs : specialArity σD c = none) : ¬ ShortSpine σD x := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  rw [h] at h1
  cases h1
  rw [hs] at h2
  cases h2

/-- `CLErasable` of the frozen type argument: its type is a sort (an arity of length 0). -/
theorem erasable_tT : CLErasable envNV0 tT :=
  ⟨cTT, 100, .sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))), by krfl, by krfl,
    .inl (by krfl)⟩

/-- `CLOk` of the first β-redex `(fun (α : Sort 2) (a : α) => a) □T` -/
theorem ok_beta1 : CLOk envNV0 beta1 :=
  ⟨⟨.app (.lam (.sort (.succ (.succ .zero))) (.lam (.bvar 0) (.bvar 0))) cTT, 100, .forallE cTT cTT,
    by krfl, by krfl⟩, .app (.lam (.sort (.succ (.succ .zero))) (.lam (.bvar 0) (.bvar 0))) cTT, 100, .forallE cTT cTT,
    by krfl, by krfl⟩

/-- `CLOk` of the second β-redex `(fun (a : □T) => a) (fun α a => a)` -/
theorem ok_beta2 : CLOk envNV0 beta2 := ⟨⟨.app (.lam cTT (.bvar 0)) cIdT, 100, cTT, by krfl, by krfl⟩, .app (.lam cTT (.bvar 0)) cIdT, 100, cTT, by krfl, by krfl⟩

/-- δ of `nv0id.{2}`: its value, marked (no mark) and instantiated. -/
theorem ev_id : SrcEval envNV0 σD (.const `nv0id [.succ (.succ .zero)]) id2 :=
  SrcEval.delta (ci := .defnInfo id_def) (body := idLam (.param `u)) (by krfl)
    (mark_idLam (.inr rfl) _ (.inl rfl)) (SrcEval.atom trivial)

theorem ev_beta1 : SrcEval envNV0 σD (.app (.const `nv0id [.succ (.succ .zero)]) (markErase tT)) lamA :=
  SrcEval.beta (n := `α) (A := .sort (.succ (.succ .zero))) (b := .lam `a (.bvar 0) (.bvar 0) .default)
    (bi := .default) (not_short rfl (by krfl)) ev_id (SrcEval.frozen erasable_tT) ok_beta1
    (SrcEval.atom trivial)

theorem ev_mainM : SrcEval envNV0 σD mainM idT :=
  SrcEval.beta (n := `a) (A := markErase tT) (b := .bvar 0) (bi := .default)
    (not_short rfl (by krfl)) ev_beta1 (SrcEval.atom trivial) ok_beta2 (SrcEval.atom trivial)

theorem hev : SrcEval envNV0 σD e idT :=
  SrcEval.delta (ci := .defnInfo main_def) (body := mainVal) (by krfl) (mark_main (.inr rfl)) ev_mainM

/-! ## The marks coincide with the `□`s of `hrun`'s output

`Erases` relates a term to `□` exactly at its `erase` marks (`Erases.box`; no other rule produces
`.box` from a mark). The marked term `ê = e`, `nv0main`'s marked value `mainM` and `nv0id`'s value
erase, with con-leche-certified boxes, to the λ□ terms `p0` holds: the one mark of `mainM` is the
one `□` of `mainL`. -/

theorem not_special {x : Expr} {c : Name} {us : List Level} {d : DefinitionVal}
    (h : x.getAppFn = .const c us) (hd : findDecl σ.decls c = some (.defnInfo d))
    (hc : σ.casesOn? c = none) : ¬ SpecialSpine σ x := by
  rintro ⟨c', us', h1, h2⟩
  rw [h] at h1
  cases h1
  rcases h2 with ⟨cv, h⟩ | h | ⟨qv, h, -⟩ | ⟨rv, h⟩ <;> simp_all

theorem erases_const {c : Name} {d : DefinitionVal} (hd : findDecl σ.decls c = some (.defnInfo d))
    (ha : σ.isAtom c = false) (hs : specialArity σ c = none) (us : List Level) :
    Erases (CLCert envNV0) σ [] (.const c us) (.const (toKername c)) :=
  Erases.const ha hs (fun rv h => by rw [hd] at h; cases h)

theorem coincide_e : Erases (CLCert envNV0) σ [] e t0 :=
  erases_const (d := main_def) (by krfl) (by krfl) (by krfl) []

theorem coincide_id : Erases (CLCert envNV0) σ [] (idLam (.param `u)) idL :=
  Erases.lam (Erases.lam Erases.bvar)

theorem coincide_main : Erases (CLCert envNV0) σ [] mainM mainL :=
  Erases.app (not_special (d := id_def) rfl (by krfl) (by krfl))
    (Erases.app (not_special (d := id_def) rfl (by krfl) (by krfl))
      (erases_const (d := id_def) (by krfl) (by krfl) (by krfl) _) (Erases.box cert_tT))
    (Erases.lam (Erases.lam Erases.bvar))

/-- The marking δ uses in `hev` erases, with certified boxes, to the body `p0` holds, for both
constants of `p0`: the witness half of `ErasesDecl` (its `∀` half follows with `MarkOf.det`). -/
theorem decl_id : MarkOf σ.decls σ.cfg [] (idLam (.param `u)) (idLam (.param `u)) ∧
    Erases (CLCert envNV0) σ [] (idLam (.param `u)) idL :=
  ⟨mark_idLam (.inl rfl) _ (.inl rfl), coincide_id⟩

theorem decl_main : MarkOf σ.decls σ.cfg [] mainVal mainM ∧ Erases (CLCert envNV0) σ [] mainM mainL :=
  ⟨mark_main (.inl rfl), coincide_main⟩

end EraseProof.Test.NV0
