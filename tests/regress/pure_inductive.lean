import LeanToLambdaBox

/-!
The pure backend recognizes canonical `casesOn` definitions (`Erasure.casesInfo?`) and
constructors (`Erasure.ctorArity?`) over the program's declarations, and its oracle types and
reduces Nat literals and projections. The test checks:
- by kernel evaluation (`decide`), over declarations copied from the elaboration environment:
  the recognizer's answer on `B.casesOn` (two constructors without fields) and `T.casesOn`
  (`leaf (x : B)`, recursive `node (l : T) (y : B)`), and `none` on `And.casesOn` (built from
  projections), on `B.neg` and on `B.rec`; `ctorArity?` on `T.node`; the oracle's type of
  `T.node (T.leaf B.f) B.t`, of the projection `(P2.mk B.f B.t).2` and of the literal `2`, the
  weak-head normal form `B.t` of that projection, and erasability (kept: the projection and
  `B.neg B.f`; erased: the projection `(And.intro True.intro True.intro).1`);
- on every inductive type of the environment with a `casesOn`, that the recognizer agrees with
  `getCasesInfo?` (the `Meta` path's) on each canonical one and answers `none` exactly on those
  built from projections (`isCasesOnViaProjs`), nested or unsafe; and on every constructor that
  `ctorArity?` agrees with `getCtorArity?`;
- the oracle's types (up to `Meta.isDefEq`) and erasability answers agree with `Meta`'s on
  projections, literals, constructor and `casesOn` applications, and so do its weak-head normal
  forms except where `Meta.whnf` reduces a recursor;
- `erasePure`, run over the declarations each program reads, erases `B.neg B.f`,
  `T.snd (T.node (T.leaf B.f) B.t)`, `(swap ⟨B.f, B.t⟩).a`, `isZero 2` (`nat := .peano`) and
  `Eq.casesOn (motive := fun _ _ => B) (Eq.refl B.t) B.f` to the same program as the `Meta` path
  (`Erasure.erase`); the pure programs are written to `nv1.ast`, `nv4.ast`, `nv2.ast`, `nv3.ast`,
  `eq.ast`, which peregrine validates and evaluates to `B.t`, `B.t`, `B.t`, `B.f`, `B.f`.
-/

-- peregrine: validate nv1.ast
-- peregrine: eval nv1.ast
-- peregrine: validate nv4.ast
-- peregrine: eval nv4.ast
-- peregrine: validate nv2.ast
-- peregrine: eval nv2.ast
-- peregrine: validate nv3.ast
-- peregrine: eval nv3.ast
-- peregrine: validate eq.ast
-- peregrine: eval eq.ast

open Lean Elab Command Erasure

namespace PI
inductive B | f | t
def B.neg (b : B) : B := B.casesOn (motive := fun _ => B) b B.t B.f
inductive T | leaf (x : B) | node (l : T) (y : B)
def T.snd (t : T) : B := T.casesOn (motive := fun _ => B) t (fun x => x) (fun _ y => y)
structure P2 where
  a : B
  b : B
def swap (p : P2) : P2 := ⟨p.b, p.a⟩
def isZero (n : Nat) : B := Nat.casesOn (motive := fun _ => B) n B.t (fun _ => B.f)
end PI

/-! ## Declarations as terms, for kernel evaluation -/

deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo

/-- The term that denotes an `Expr` without metavariables, free variables or metadata (those
become `.bvar 1000000`, which no test declaration contains). -/
def quoteExpr : Expr → Expr
  | .bvar i => mkApp (mkConst ``Expr.bvar) (toExpr i)
  | .sort u => mkApp (mkConst ``Expr.sort) (toExpr u)
  | .const c us => mkApp2 (mkConst ``Expr.const) (toExpr c) (toExpr us)
  | .app f a => mkApp2 (mkConst ``Expr.app) (quoteExpr f) (quoteExpr a)
  | .lam n t b bi => mkApp4 (mkConst ``Expr.lam) (toExpr n) (quoteExpr t) (quoteExpr b) (toExpr bi)
  | .forallE n t b bi =>
    mkApp4 (mkConst ``Expr.forallE) (toExpr n) (quoteExpr t) (quoteExpr b) (toExpr bi)
  | .letE n t v b nd =>
    mkApp5 (mkConst ``Expr.letE) (toExpr n) (quoteExpr t) (quoteExpr v) (quoteExpr b) (toExpr nd)
  | .lit l => mkApp (mkConst ``Expr.lit) (toExpr l)
  | .proj s i e => mkApp3 (mkConst ``Expr.proj) (toExpr s) (toExpr i) (quoteExpr e)
  | _ => mkApp (mkConst ``Expr.bvar) (toExpr 1000000)

instance : ToExpr Expr := ⟨quoteExpr, mkConst ``Expr⟩

deriving instance ToExpr for ReducibilityHints
deriving instance ToExpr for DefinitionSafety
deriving instance ToExpr for ConstantVal
deriving instance ToExpr for AxiomVal
deriving instance ToExpr for DefinitionVal
deriving instance ToExpr for TheoremVal
deriving instance ToExpr for OpaqueVal
deriving instance ToExpr for QuotKind
deriving instance ToExpr for QuotVal
deriving instance ToExpr for InductiveVal
deriving instance ToExpr for ConstructorVal
deriving instance ToExpr for RecursorRule
deriving instance ToExpr for RecursorVal
deriving instance ToExpr for ConstantInfo

/-- `#decls d := n₁ … nₖ` defines `d : List ConstantInfo` as the declarations of `n₁ … nₖ` in the
elaboration environment. -/
elab "#decls " id:ident " := " ns:ident* : command => do
  let env ← getEnv
  let cis ← ns.toList.mapM fun n => do
    let some ci := env.find? n.getId | throwError "unknown constant {n.getId}"
    pure ci
  liftCoreM <| addDecl <| .defnDecl <|
    mkDefinitionValEx id.getId [] (toTypeExpr (List ConstantInfo)) (toExpr cis) .abbrev .safe []

#decls PI.dB := PI.B.neg PI.B.casesOn PI.B.rec PI.B PI.B.f PI.B.t
#decls PI.dT := PI.T.casesOn PI.T.rec PI.T PI.T.leaf PI.T.node PI.B PI.B.f PI.B.t PI.P2 PI.P2.mk
#decls PI.dAnd := And.casesOn And.rec And And.intro True True.intro

/-- The recognizer's answer as data with a decidable equality: inductive, arity, positions of the
discriminant and the motive, range of the alternatives, and constructor and number of fields of
each alternative. -/
def ans (decls : List ConstantInfo) (n : Name) :
    Option (Name × Nat × Nat × Nat × Nat × Nat × List (Name × Nat)) :=
  (casesInfo? decls n).map fun ci => (ci.indName, ci.arity, ci.discrPos, ci.motivePos,
    ci.altsRange.lower, ci.altsRange.upper,
    ci.altNumParams.toList.map fun | .ctor c k => (c, k) | .default k => (.anonymous, k))

theorem casesInfo_B : (ans PI.dB `PI.B.casesOn ==
    some (`PI.B, 4, 1, 0, 2, 4, [(`PI.B.f, 0), (`PI.B.t, 0)])) = true := by decide

theorem casesInfo_T : (ans PI.dT `PI.T.casesOn ==
    some (`PI.T, 4, 1, 0, 2, 4, [(`PI.T.leaf, 1), (`PI.T.node, 2)])) = true := by decide

theorem casesInfo_none : ans PI.dAnd `And.casesOn = none ∧ ans PI.dB `PI.B.neg = none ∧
    ans PI.dB `PI.B.rec = none := by decide

theorem ctorArity_node : ctorArity? PI.dT `PI.T.node = some 2 ∧ ctorArity? PI.dT `PI.T = none := by
  decide

def cF : Expr := .const `PI.B.f []
def cT : Expr := .const `PI.B.t []
def tree : Expr := mkApp2 (.const `PI.T.node []) (mkApp (.const `PI.T.leaf []) cF) cT
def pair : Expr := mkApp2 (.const `PI.P2.mk []) cF cT
def andTT : Expr := mkApp4 (.const ``And.intro []) (.const ``True []) (.const ``True [])
  (.const ``True.intro []) (.const ``True.intro [])

theorem oracle_types :
    (match Pure.inferType ⟨PI.dT⟩ 64 [] [] tree with
      | .ok (.const `PI.T []) => true | _ => false) = true ∧
    (match Pure.inferType ⟨PI.dT⟩ 64 [] [] (.proj `PI.P2 1 pair) with
      | .ok (.const `PI.B []) => true | _ => false) = true ∧
    (match Pure.inferType ⟨[]⟩ 64 [] [] (.lit (.natVal 2)) with
      | .ok (.const ``Nat []) => true | _ => false) = true ∧
    (match Pure.whnf ⟨PI.dT⟩ 64 [] (.proj `PI.P2 1 pair) with
      | .ok (.const `PI.B.t []) => true | _ => false) = true := by
  decide

theorem oracle_erasable :
    (match Pure.isErasable ⟨PI.dT⟩ 64 [] (.proj `PI.P2 1 pair) with
      | .ok false => true | _ => false) = true ∧
    (match Pure.isErasable ⟨PI.dB⟩ 64 [] (.app (.const `PI.B.neg []) cF) with
      | .ok false => true | _ => false) = true ∧
    (match Pure.isErasable ⟨PI.dAnd⟩ 64 [] (.proj ``And 0 andTT) with
      | .ok true => true | _ => false) = true := by
  decide

/-! ## Agreement with the `Meta` path -/

/-- A `casesOn` recognition as text. -/
def showCases : Option CasesInfo → String
  | none => "none"
  | some ci =>
    let alts := ci.altNumParams.toList.map fun
      | .ctor c k => s!"{c}/{k}"
      | .default k => s!"default/{k}"
    s!"some {ci.declName} {ci.indName} {ci.arity} {ci.discrPos} {ci.motivePos} \
      {ci.altsRange.lower} {ci.altsRange.upper} {alts}"

/-- The declarations the recognizer reads for `T.casesOn`: it, `T.rec`, and the types and
constructors of `T`'s block. -/
def casesDecls (env : Environment) (I : InductiveVal) : List ConstantInfo :=
  let names := [I.name ++ `casesOn, mkRecName I.name] ++
    I.all.flatMap fun t => t :: (match env.find? t with
      | some (.inductInfo J) => J.ctors
      | _ => [])
  names.filterMap env.find?

/-- Counts of the inductive types with a `casesOn` that the recognizer recognizes as `Meta` does,
of those it rejects as expected (built from projections, nested, unsafe), and the names of the
others; then the number of constructors and the names of those whose arities disagree. -/
def census : MetaM String := do
  let env ← getEnv
  let mut canon := 0
  let mut other := 0
  let mut bad : Array Name := #[]
  let mut ctors := 0
  let mut badCtors : Array Name := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .inductInfo I =>
      unless env.contains (n ++ `casesOn) do continue
      let p := casesInfo? (casesDecls env I) (n ++ `casesOn)
      if (← isCasesOnViaProjs n) || I.isUnsafe || I.numNested != 0 then
        if p.isNone then other := other + 1 else bad := bad.push n
      else if showCases p == showCases (← getCasesInfo? (n ++ `casesOn)) then canon := canon + 1
      else bad := bad.push n
    | .ctorInfo _ =>
      ctors := ctors + 1
      unless ctorArity? [ci] n == (← Compiler.LCNF.getCtorArity? n) do badCtors := badCtors.push n
    | _ => pure ()
  return s!"casesOn: {canon} recognized as Meta does, {other} rejected (projections, nested, \
    unsafe), disagreeing {bad.toList}; constructors: {ctors}, disagreeing {badCtors.toList}"

/--
info: "casesOn: 2712 recognized as Meta does, 244 rejected (projections, nested, unsafe), disagreeing []; constructors: 4845, disagreeing []"
-/
#guard_msgs in
#eval census

/-- The declarations of the environment, as the pure backend reads them. -/
def allDecls : CoreM (List ConstantInfo) :=
  return (← getEnv).constants.fold (fun acc _ ci => ci :: acc) []

/-- Terms on which the oracle is compared with `Meta`. -/
def terms : List (String × Expr) :=
  [("tree", tree), ("pair.2", .proj `PI.P2 1 pair), ("pair.1", .proj `PI.P2 0 pair),
   ("and.1", .proj ``And 0 andTT), ("2", .lit (.natVal 2)),
   ("B.neg B.f", .app (.const `PI.B.neg []) cF),
   ("B.casesOn", mkApp4 (.const `PI.B.casesOn [1]) (.lam `x (.const `PI.B []) (.const `PI.B []) .default)
      cT cF cT)]

/-- `(term, types agree, normal forms agree, pure and Meta erasability)` for each of `terms`. The
normal forms of `B.neg B.f` and of the `B.casesOn` application differ: `Meta.whnf` reduces the
recursor `B.rec` to which they unfold, the oracle has no ι-rule for recursors. -/
def oracle : MetaM (List (String × Bool × Bool × String × Bool)) := do
  let cx : Pure.Ctx := ⟨← allDecls⟩
  terms.mapM fun (n, e) => do
    let ty ← match Pure.inferType cx oracleFuel [] [] e with
      | .ok t => Meta.isDefEq t (← Meta.inferType e)
      | .error _ => pure false
    let wh := match Pure.whnf cx oracleFuel [] e with
      | .ok w => w
      | .error _ => .bvar 1000000
    let er := match Pure.isErasable cx oracleFuel [] e with
      | .ok b => toString b
      | .error _ => "error"
    return (n, ty, wh == (← Meta.whnf e), er, ← Erasure.isErasable e)

/--
info: [("tree", true, true, "false", false), ("pair.2", true, true, "false", false), ("pair.1", true, true, "false", false),
  ("and.1", true, true, "true", true), ("2", true, true, "false", false), ("B.neg B.f", true, false, "false", false),
  ("B.casesOn", true, false, "false", false)]
-/
#guard_msgs in
#eval oracle

/-! ## `erasePure` on programs with inductive types -/

/-- The programs: output file, the constant whose value is the term, the configuration, and the
declarations the pure traversal reads. -/
def programs : List (String × Name × ErasureConfig × List Name) :=
  let blkB := [`PI.B, `PI.B.f, `PI.B.t]
  [("nv1.ast", `PI.ex1, {}, [`PI.B.neg, `PI.B.casesOn, `PI.B.rec] ++ blkB),
   ("nv4.ast", `PI.ex4, {},
     [`PI.T.snd, `PI.T.casesOn, `PI.T.rec, `PI.T, `PI.T.leaf, `PI.T.node] ++ blkB),
   ("nv2.ast", `PI.ex2, {}, [`PI.swap, `PI.P2.a, `PI.P2.b, `PI.P2, `PI.P2.mk] ++ blkB),
   ("nv3.ast", `PI.ex3, { nat := .peano },
     [`PI.isZero, ``Nat.casesOn, ``Nat.rec, ``Nat, ``Nat.zero, ``Nat.succ] ++ blkB),
   ("eq.ast", `PI.exEq, {}, [``Eq.casesOn, ``Eq.rec, ``Eq, ``Eq.refl] ++ blkB)]

namespace PI
def ex1 : B := B.neg B.f
def ex4 : B := T.snd (T.node (T.leaf B.f) B.t)
def ex2 : B := (swap ⟨B.f, B.t⟩).a
def ex3 : B := isZero 2
def exEq : B := Eq.casesOn (motive := fun _ _ => B) (Eq.refl B.t) B.f
end PI

/-- For each program, whether the pure and the `Meta` erasure are the same program; the pure one
is written to its file. -/
def eraseBoth : CoreM (List (String × Bool)) := do
  let env ← getEnv
  programs.mapM fun (f, c, cfg, ns) => do
    -- `ex3`'s literal is `OfNat.ofNat 2`; the term erased is the literal itself
    let e ← if c == `PI.ex3 then pure (.app (.const `PI.isZero []) (.lit (.natVal 2)))
      else do pure (← getConstInfo c).value!
    match erasePure (EnvView.ofEnvironment env) cfg (ns.filterMap env.find?) e with
    | .ok (p, inl) =>
      IO.FS.writeFile f (p |> Serialize.to_sexpr |>.toString)
      let (q, inl') ← erase e cfg
      return (f, toString (Serialize.to_sexpr p) == toString (Serialize.to_sexpr q) && inl == inl')
    | .error err => throwError "{f}: {err.describe}"

/--
info: [("nv1.ast", true), ("nv4.ast", true), ("nv2.ast", true), ("nv3.ast", true), ("eq.ast", true)]
-/
#guard_msgs in
#eval eraseBoth
