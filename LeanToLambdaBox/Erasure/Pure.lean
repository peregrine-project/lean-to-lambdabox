import LeanToLambdaBox.Erasure
import LeanToLambdaBox.Erasure.Collect

/-!
# The pure erasability oracle and the pure backend

`Erasure.casesInfo?` recognizes the canonical `casesOn` definitions of a list of declarations, and
`Erasure.ctorArity?` gives the arity of their constructors, as the `Meta` path's `getCasesInfo?`
and `getCtorArity?` read them from the environment.
`Erasure.Pure.isErasable` decides whether a term is erasable (a proof or a type former) over a list
of declarations, by infer-only retyping and weak-head reduction with the kernel's δ, with fuel.
`Erasure.PureM` is the monad of the backend without `Meta`, whose environment is the program's
closure (`collectDeps`), and `Erasure.PureM.*` are the backend operations that read it; with them,
`PureM` is an instance of `Erasure.Backend`. `Erasure.erasePure` runs the traversal of `#erase`
(`Erasure.visitExpr`) with this backend. `nameOccurs`, `isRecursiveDecl` and `axiomatized` are the
traversal's recursion and `@[extern]` tests as this backend runs them.
-/

open Lean

namespace Erasure

/-! ## The canonical `casesOn` recognizer -/

/-- Peel exactly `k` leading `λ`s. Reference: none. -/
def peelLams : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .lam _ _ b _ => peelLams k b
  | _ + 1, _ => none

/-- The domain of the `i`-th leading `Π` of a type. Reference: none. -/
def forallDom? : Nat → Expr → Option Expr
  | 0, .forallE _ t _ _ => some t
  | i + 1, .forallE _ _ b _ => forallDom? i b
  | _, _ => none

/-- Number of leading `Π`s. Reference: none. -/
def forallArity : Expr → Nat
  | .forallE _ _ b _ => forallArity b + 1
  | _ => 0

/-- Arity of the `i`-th premise of a recursor type. Reference: none. -/
def minorArity (ty : Expr) (i : Nat) : Nat := ((forallDom? i ty).map forallArity).getD 0

/-- Head and arguments of an application spine (a structural `Expr.withApp`). Reference: none. -/
def spine : Expr → Expr × List Expr
  | .app f a => match spine f with
    | (h, as) => (h, as ++ [a])
  | e => (e, [])

/-- `args[i]? = some (.bvar m)`. Reference: none. -/
def isBVarAt (args : List Expr) (i m : Nat) : Bool :=
  match args[i]? with
  | some (.bvar j) => j == m
  | _ => false

/-- `e = .const c (lps.map .param)`. Reference: none. -/
def isConstAt (e : Expr) (c : Name) (lps : List Name) : Bool :=
  match e with
  | .const c' us => c' == c && us.length == lps.length &&
      (us.zip lps).all fun | (.param a, b) => a == b | _ => false
  | _ => false

/-- `e = .bvar m` applied to `.bvar (L-1), …, .bvar (L-nf)`. Reference: none. -/
def isMinorBody (e : Expr) (m L nf : Nat) : Bool :=
  match spine e with
  | (.bvar h, as) => h == m && as.length == nf &&
      (List.range nf).all fun f => isBVarAt as f (L - 1 - f)
  | _ => false

/-- One `.ctor` alternative per constructor, with its number of fields. Reference: none. -/
def ctorAlts (decls : List ConstantInfo) : List Name → Option (List Lean.CasesAltInfo)
  | [] => some []
  | c :: cs => match findConst decls c, ctorAlts decls cs with
    | some (.ctorInfo cv), some as => some (.ctor c cv.numFields :: as)
    | _, _ => none

/-- Number of fields of the `i`-th alternative. Reference: none. -/
def altFields (alts : List Lean.CasesAltInfo) (i : Nat) : Nat :=
  match alts[i]? with
  | some (.ctor _ k) => k
  | _ => 0

/-- Total number of constructors of the given inductives. Reference: none. -/
def blockCtorCount (decls : List ConstantInfo) : List Name → Option Nat
  | [] => some 0
  | t :: ts => match findConst decls t, blockCtorCount decls ts with
    | some (.inductInfo it), some m => some (it.ctors.length + m)
    | _, _ => none

/-- The canonical-`casesOn` recognizer over the program's declarations: `some` exactly when
`n = T.casesOn`, `T` a safe, non-nested inductive of `decls` whose recursor `T.rec` (in `decls`)
has no auxiliary motives, and `n` is a definition of `decls` with the recursor's level parameters
whose value is the canonical `fun ps motive is t ms => T.rec ps motives' minors' is t` (exactly
`numParams + 1 + numIndices + 1 + numCtors` leading `λ`s; own motive the `motive` binder; own
minors `fun fs ihs => mᵢ fs` over all the binders of the recursor's minor premise; the other
sorts' motives and minors unconstrained); then the `CasesInfo` of `T` (`numParams`, `numIndices`,
one `.ctor` alternative per constructor with its `numFields`), as `getCasesInfo?` gives it. `none`
on any mismatch, so a `casesOn` built otherwise (by projections, for a large-eliminating `Prop`
structure), a sparse `casesOn` and `T.c.elim` are not recognized. Reference: `Lean.getCasesInfo?`
(`Lean/Meta/CasesInfo.lean`) on the `Meta` path, which reads the declaration's type and the
environment extensions instead; the value's shape is that of `Lean.mkCasesOn`. -/
def casesInfo? (decls : List ConstantInfo) (n : Name) : Option Lean.CasesInfo :=
  match n with
  | .str T "casesOn" =>
    match findConst decls n, findConst decls T, findConst decls (mkRecName T) with
    | some (.defnInfo d), some (.inductInfo I), some (.recInfo R) =>
      let p := I.numParams
      let k := I.numIndices
      let D := p + 1 + k + 1 + I.ctors.length
      let bv (i : Nat) : Nat := D - 1 - i
      match R.all.idxOf? T, peelLams D d.value, ctorAlts decls I.ctors,
        blockCtorCount decls (R.all.take (R.all.idxOf T)) with
      | some j, some body, some alts, some before =>
        let (hd, args) := spine body
        let off := p + R.numMotives + before
        let idx := p + R.numMotives + R.numMinors
        let ok := !I.isUnsafe && I.numNested == 0 && d.levelParams == R.levelParams &&
          R.numMotives == I.all.length && isConstAt hd R.name R.levelParams &&
          args.length == R.numParams + R.numMotives + R.numMinors + R.numIndices + 1 &&
          (List.range p).all (fun i => isBVarAt args (i) (bv i)) &&
          isBVarAt args (p + j) (bv p) &&
          (List.range alts.length).all (fun i =>
            let L := minorArity R.type (off + i)
            match args[off + i]?, peelLams L ((args[off + i]?).getD (.bvar 0)) with
            | some _, some m => isMinorBody m (L + bv (p + 1 + k + 1 + i)) L (altFields alts i)
            | _, _ => false) &&
          (List.range k).all (fun i => isBVarAt args (idx + i) (bv (p + 1 + i))) &&
          isBVarAt args (idx + k) (bv (p + 1 + k))
        if ok then
          some { declName := n, indName := T, arity := D, discrPos := p + 1 + k, motivePos := p,
                 altsRange := { lower := p + 1 + k + 1, upper := D }, altNumParams := alts.toArray }
        else none
      | _, _, _, _ => none
    | _, _, _ => none
  | _ => none

/-- The arity (`numParams + numFields`) of a constructor of `decls`. Reference:
`Compiler.LCNF.getCtorArity?` on the `Meta` path. -/
def ctorArity? (decls : List ConstantInfo) (n : Name) : Option Nat :=
  match findConst decls n with
  | some (.ctorInfo cv) => some (cv.numParams + cv.numFields)
  | _ => none

/-! ## The pure oracle -/

namespace Pure

/-- Level substitution without normalisation (kernel-reducible). Reference: PCUIC
`subst_instance` on levels (`MR common/theories/Universes.v:2480 UnivSubst`). -/
def instLevel (ps : List Name) (us : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (instLevel ps us l)
  | .max a b => .max (instLevel ps us a) (instLevel ps us b)
  | .imax a b => .imax (instLevel ps us a) (instLevel ps us b)
  | .param n => match (ps.zip us).find? (·.1 == n) with
    | some (_, u) => u
    | none => .param n
  | .mvar m => .mvar m

/-- Universe instantiation of a term, used by the oracle and by the source semantics' δ rule.
Reference: `subst_instance_constr` (`MR P/PCUICAst.v:404`); its model meaning is
`EraseProof.TrS.instLevels`. -/
def instLevels (ps : List Name) (us : List Level) : Expr → Expr
  | .sort u => .sort (instLevel ps us u)
  | .const c ls => .const c (ls.map (instLevel ps us))
  | .app f a => .app (instLevels ps us f) (instLevels ps us a)
  | .lam n t b bi => .lam n (instLevels ps us t) (instLevels ps us b) bi
  | .forallE n t b bi => .forallE n (instLevels ps us t) (instLevels ps us b) bi
  | .letE n t v b nd => .letE n (instLevels ps us t) (instLevels ps us v) (instLevels ps us b) nd
  | .mdata m e => .mdata m (instLevels ps us e)
  | .proj s i e => .proj s i (instLevels ps us e)
  | e => e

/-- What the oracle reads: the program's declarations. Every reduction of the oracle uses the
kernel's δ, which unfolds every definition and ignores the elaborator attribute `@[irreducible]`.
Reference: the abstract environment `X` passed to `MR E/ErasureFunction.v:894 is_erasableb`,
whose reductions unfold every constant with a body (`MR S/PCUICSafeReduce.v:1839 hnf` at
`RedFlags.default`, δ on: `MR P/PCUICNormal.v:26`). -/
structure Ctx where
  decls : List ConstantInfo

/-- Structural "zero under every assignment": `zero`; `max` of two; `imax` with a right one.
Reference: `Sort.is_propositional` in `MR E/ErasureFunction.v:894 is_erasableb` (Lean: level
`≈ 0`, no SProp; DV-4). -/
def alwaysZero : Level → Bool
  | .zero => true
  | .max a b => alwaysZero a && alwaysZero b
  | .imax _ b => alwaysZero b
  | _ => false

/-- Lookup of a traversal local. Reference: `nth_error Γ` on the PCUIC context (DV-13). -/
def findLocal (ls : List Local) (x : FVarId) : Option Local := ls.find? (·.fvarId == x)

/-- Weak-head normal form: head β (`instantiate1'`), ζ (`letE` and let-bound locals), δ of every
definition (the kernel's δ), `mdata`, and the ι-rule of projections: `proj S i s` whose `s` reduces
to a constructor application `C ps fs` reduces to `fs[i]` (the kernel's `reduce_proj`). Terms may
have loose bound variables. Reference: `hnf` (`MR S/PCUICSafeReduce.v:1839`, `RedFlags.default`),
as `sort_of_type` uses `reduce_to_sort` (`:1853`); projections: `red_proj`
(`MR P/PCUICReduction.v:82`). -/
def whnf (cx : Ctx) : Nat → List Local → Expr → Except EraseError Expr
  | 0, _, _ => throw (.fuel "whnf")
  | f+1, ls, .app g a => do
    match ← whnf cx f ls g with
    | .lam _ _ b _ => whnf cx f ls (b.instantiate1' a)
    | g' => pure (.app g' a)
  | f+1, ls, .letE _ _ v b _ => whnf cx f ls (b.instantiate1' v)
  | f+1, ls, .mdata _ e => whnf cx f ls e
  | f+1, ls, .fvar x => match findLocal ls x with
    | some ⟨_, _, _, some v⟩ => whnf cx f ls v
    | _ => pure (.fvar x)
  | f+1, ls, e@(.const c us) => match findConst cx.decls c with
    | some (.defnInfo v) =>
      if us.length != v.levelParams.length then pure e
      else whnf cx f ls (instLevels v.levelParams us v.value)
    | _ => pure e
  | f+1, ls, e@(.proj _ i s) => do
    match spine (← whnf cx f ls s) with
    | (.const c _, args) => match findConst cx.decls c with
      | some (.ctorInfo cv) => match args[cv.numParams + i]? with
        | some a => whnf cx f ls a
        | none => pure e
      | _ => pure e
    | _ => pure e
  | _+1, _, e => pure e

/-- Instantiate the leading `Π`s of a type with the given terms, reducing it with `whnf` before
each. Reference: the loop over the parameters in `inferProjType` (`Lean/Meta/InferType.lean`). -/
def instForalls (cx : Ctx) (f : Nat) (ls : List Local) : Expr → List Expr → Except EraseError Expr
  | r, [] => pure r
  | r, a :: as => do
    let .forallE _ _ b _ ← whnf cx f ls r | throw (.failed "not a function")
    instForalls cx f ls (b.instantiate1' a) as

/-- The `Π`-type of the fields of a structure `S`'s constructor, instantiated with the projections
`proj S j s` for the fields `j < i`: the type whose leading `Π`'s domain is the type of field `i`.
Reference: the loop over the fields in `inferProjType` (`Lean/Meta/InferType.lean`). -/
def instProjs (cx : Ctx) (f : Nat) (ls : List Local) (S : Name) (s : Expr) :
    Nat → Nat → Expr → Except EraseError Expr
  | 0, _, r => pure r
  | n+1, j, r => do
    let .forallE _ _ b _ ← whnf cx f ls r | throw (.failed "not a function")
    instProjs cx f ls S s n (j + 1) (b.instantiate1' (.proj S j s))

/-- Infer-only retyping. Binders are opened de Bruijn style: `Γ` holds the types of the binders
the oracle entered, the traversal's free variables are looked up in `ls`; no names are generated.
Where it needs a Π or a sort it reduces with `whnf`, as type inference in Lean's kernel does. A
constant's type is its declared type at the constant's levels, for inductive types, constructors,
recursors and `casesOn` as for every other constant. A Nat literal has the type `Nat`. A projection
`proj S i s` has the type of the `i`-th field of `S`'s constructor, instantiated with the
parameters of `s`'s type and with the projections of `s` for the earlier fields (Lean's
`inferProjType`). Reference: `type_of_typing` (`MR S/PCUICSafeRetyping.v:806`), as called by
`MR E/ErasureFunction.v:894 is_erasableb`; projections: `infer` on `tProj`
(`MR S/PCUICSafeRetyping.v:350`). -/
def inferType (cx : Ctx) : Nat → List Local → List Expr → Expr → Except EraseError Expr
  | 0, _, _, _ => throw (.fuel "inferType")
  | _+1, _, Γ, .bvar i => match Γ[i]? with
    | some A => pure (A.liftLooseBVars' 0 (i + 1))
    | none => throw (.outOfFragment "loose bvar")
  | _+1, ls, _, .fvar x => match findLocal ls x with
    | some l => pure l.type
    | none => throw (.outOfFragment "unknown fvar")
  | _+1, _, _, .sort u => pure (.sort (.succ u))
  | _+1, _, _, .const c us => match findConst cx.decls c with
    | some ci =>
      if us.length == ci.levelParams.length then pure (instLevels ci.levelParams us ci.type)
      else throw (.failed "universe arity")
    | none => throw (.outOfFragment "unknown constant")
  | f+1, ls, Γ, .app g a => do
    match ← whnf cx f ls (← inferType cx f ls Γ g) with
    | .forallE _ _ B _ => pure (B.instantiate1' a)
    | _ => throw (.failed "not a function")
  | f+1, ls, Γ, .lam n t b bi => do
    let B ← inferType cx f ls (t :: Γ) b
    pure (.forallE n t B bi)
  | f+1, ls, Γ, .forallE _ t b _ => do
    let .sort u ← whnf cx f ls (← inferType cx f ls Γ t) | throw (.failed "not a type")
    let .sort v ← whnf cx f ls (← inferType cx f ls (t :: Γ) b) | throw (.failed "not a type")
    pure (.sort (.imax u v))
  | f+1, ls, Γ, .letE _ _ v b _ => inferType cx f ls Γ (b.instantiate1' v)
  | f+1, ls, Γ, .mdata _ e => inferType cx f ls Γ e
  | _+1, _, _, .lit (.natVal _) => pure (.const ``Nat [])
  | f+1, ls, Γ, .proj S i s => do
    match spine (← whnf cx f ls (← inferType cx f ls Γ s)) with
    | (.const S' us, args) =>
      match S' == S, findConst cx.decls S with
      | true, some (.inductInfo I) =>
        match I.ctors, args.length == I.numParams + I.numIndices with
        | [c], true => match findConst cx.decls c with
          | some ci@(.ctorInfo _) =>
            unless us.length == ci.levelParams.length do throw (.failed "universe arity")
            let r ← instForalls cx f ls (instLevels ci.levelParams us ci.type)
              (args.take I.numParams)
            let .forallE _ d _ _ ← whnf cx f ls (← instProjs cx f ls S s i 0 r)
              | throw (.failed "invalid projection")
            pure d
          | _ => throw (.failed "invalid projection")
        | _, _ => throw (.failed "invalid projection")
      | _, _ => throw (.failed "invalid projection")
    | _ => throw (.failed "invalid projection")
  | _+1, _, _, _ => throw (.outOfFragment "string literal or metavariable")

/-- Arity test after weak-head reduction. Reference: `is_arity` (`MR E/ErasureFunction.v:784`), PCUIC `isArity` (`MR P/PCUICTyping.v:29`). -/
def isArity (cx : Ctx) : Nat → List Local → Expr → Except EraseError Bool
  | 0, _, _ => throw (.fuel "isArity")
  | f+1, ls, T => do
    match ← whnf cx f ls T with
    | .sort _ => pure true
    | .forallE _ _ B _ => isArity cx f ls B
    | _ => pure false

/-- Whether a type is `Prop` or a Π-type ending in `Prop`, after weak-head reduction: `isArity`
with the sort `Sort 0` (the level `zero`, as `Meta.isPropFormerType` compares it with `==`).
Reference: `Sort.is_propositional` of the inductive's sort in
`MR E/ErasureFunction.v:1325 erase_one_inductive_body`. -/
def isPropFormerType (cx : Ctx) : Nat → List Local → Expr → Except EraseError Bool
  | 0, _, _ => throw (.fuel "isPropFormerType")
  | f+1, ls, T => do
    match ← whnf cx f ls T with
    | .sort .zero => pure true
    | .forallE _ _ B _ => isPropFormerType cx f ls B
    | _ => pure false

/-- The level `u` of the sort `Sort u` of the type of a term: the type of its type, after weak-head
reduction. Reference: `sort_of_type` (`MR S/PCUICSafeReduce.v:1853`) of the term's type, as
`MR E/ErasureFunction.v:894 is_erasableb` computes it. -/
def typeLevel (cx : Ctx) (fuel : Nat) (ls : List Local) (e : Expr) : Except EraseError Level := do
  match ← whnf cx fuel ls (← inferType cx fuel ls [] (← inferType cx fuel ls [] e)) with
  | .sort u => pure u
  | _ => throw (.failed "not a type")

/-- The pure erasability oracle: the type is an arity, or the type's sort is always zero. Every
reduction uses the kernel's δ. Fuel exhaustion is an error, never an answer.
Reference: `MR E/ErasureFunction.v:894 is_erasableb` (`type_of_typing`, `is_arity`,
`sort_of_type`, `Sort.is_propositional`); MC §7.2, Fig. 17. -/
def isErasable (cx : Ctx) (fuel : Nat) (ls : List Local) (e : Expr) :
    Except EraseError Bool := do
  let T ← inferType cx fuel ls [] e
  if ← isArity cx fuel ls T then return true
  match ← whnf cx fuel ls (← inferType cx fuel ls [] T) with
  | .sort u => return alwaysZero u
  | _ => return false

end Pure

/-- Fuel of one oracle call on the pure path. Reference: none (DV-17). -/
def oracleFuel : Nat := 2 ^ 20

/-! ## The pure backend -/

/-- What the pure backend reads: the program's closure and the trusted view. Reference: the
abstract environment `X` of `MR E/ErasureFunction.v:989 erase`. -/
structure PureCtx where
  decls : List ConstantInfo
  view : EnvView

/-- The pure backend's state: the counter that allocates fresh free variables. Reference:
none (MetaRocq's `erase` is de Bruijn, DV-13). -/
structure PureState where
  next : Nat := 0

/-- The pure backend. Reference: none (MetaRocq's `erase` is a pure Equations function). -/
abbrev PureM := ReaderT PureCtx (StateT PureState (Except EraseError))

/-- Run a traversal action at the pure backend. Reference: none. -/
def EraseT.runPure {α} (x : EraseT PureM α) (st : ErasureState) (tc : TravCtx) (pc : PureCtx)
    (ps : PureState) : Except EraseError ((α × ErasureState) × PureState) :=
  (((x.run st).run tc).run pc).run ps

namespace PureM

/-- `findConst? := findConst decls`. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findConst? (c : Name) : PureM (Option ConstantInfo) := return findConst (← read).decls c

/-- Fresh free variables from the counter `next`. Reference: none (DV-13). -/
def freshFVarId : PureM FVarId :=
  modifyGet fun s => (⟨.num `_pure s.next⟩, { s with next := s.next + 1 })

/-- `instantiate1 := Expr.instantiate1'` (`LeanToLambdaBox/Erasure/ExprOps.lean`, a structural
definition, where Lean's `Expr.instantiate1` is `@[extern]`). Reference: none. -/
def instantiate1 (b a : Expr) : Expr := b.instantiate1' a

/-- The oracle, on the traversal's locals, with `oracleFuel`. Reference:
`MR E/ErasureFunction.v:894 is_erasableb`. -/
def isErasable (ls : List Local) (e : Expr) : PureM Bool := do
  let pc ← read
  match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
  | .ok b => pure b
  | .error err => throw err

/-- The oracle's `isPropFormerType`, with `oracleFuel`. Reference: `Sort.is_propositional`
(`MR E/ErasureFunction.v:1325 erase_one_inductive_body`). -/
def isPropFormerType (e : Expr) : PureM Bool := do
  match Pure.isPropFormerType ⟨(← read).decls⟩ oracleFuel [] e with
  | .ok b => pure b
  | .error err => throw err

/-- The oracle's `typeLevel`, on the traversal's locals, with `oracleFuel`. Reference:
`sort_of_type` (`MR S/PCUICSafeReduce.v:1853`). -/
def typeLevel (ls : List Local) (e : Expr) : PureM Level := do
  match Pure.typeLevel ⟨(← read).decls⟩ oracleFuel ls e with
  | .ok u => pure u
  | .error err => throw err

/-- `casesInfo? := Erasure.casesInfo? decls`, the canonical-`casesOn` recognizer over the
program's declarations. Reference: `Lean.getCasesInfo?` on the `Meta` path. -/
def casesInfo? (n : Name) : PureM (Option Lean.CasesInfo) :=
  return _root_.Erasure.casesInfo? (← read).decls n

/-- `ctorArity? := Erasure.ctorArity? decls`. Reference: `Compiler.LCNF.getCtorArity?` on the
`Meta` path. -/
def ctorArity? (n : Name) : PureM (Option Nat) :=
  return _root_.Erasure.ctorArity? (← read).decls n

/-- `declInfo? := findConst?` (no `LCNF.getDeclInfo?` redirect to `_unsafe_rec`). Reference:
the kernel term, as `MR E/ErasureFunction.v:1309 erase_constant_body` erases `cst_body`. -/
def declInfo? (c : Name) : PureM (Option ConstantInfo) := findConst? c

/-- No `_unsafe_rec` redirect. Reference: none. -/
def unsafeRecBase? (_ : Name) : PureM (Option Name) := pure none

/-- `prepare := id` (no `macro_inline`, matcher inlining, csimp or `_unsafe_rec` renaming).
Reference: MetaRocq's `erase` erases the kernel term. -/
def prepare (e : Expr) : PureM Expr := pure e

end PureM

/-- The pure backend: the operations of `PureM`, with `unsafeRecBase?` always `none`;
type inference is the oracle's `Pure.inferType` at `oracleFuel` on the traversal's locals, and
`isPropFormerType` and `typeLevel` are the oracle's `Pure.isPropFormerType` and `Pure.typeLevel` at
`oracleFuel`; `casesInfo?` and `ctorArity?` are `Erasure.casesInfo?` and `Erasure.ctorArity?` over
the declarations; every constructor field is kept; `isExtern` and `inlineAttr?` read the view; no constant is an instance;
`log` does nothing; a constant missing from the declarations is `outOfFragment`, and fuel
exhaustion is the error `fuel`. Reference: the environment and retyping operations that
`MR E/ErasureFunction.v:989 erase` uses. -/
instance : Backend PureM where
  findConst? := PureM.findConst?
  unknownConstant n := throw (.outOfFragment s!"unknown constant {n}")
  declInfo? := PureM.declInfo?
  unsafeRecBase? _ := none
  freshFVarId := PureM.freshFVarId
  instantiate1 := PureM.instantiate1
  isErasable _ ls e := PureM.isErasable ls e
  inferType _ ls e := do
    match Pure.inferType ⟨(← read).decls⟩ oracleFuel ls [] e with
    | .ok t => pure t
    | .error err => throw err
  isPropFormerType := PureM.isPropFormerType
  typeLevel _ ls e := PureM.typeLevel ls e
  casesInfo? := PureM.casesInfo?
  ctorArity? := PureM.ctorArity?
  argMask _ ci := pure (Array.replicate ci.numFields .keep)
  isExtern n := return (← read).view.isExtern n
  inlineAttr? n := return (← read).view.inlineAttr? n
  isInstance _ := pure false
  prepare _ e := PureM.prepare e
  log _ := pure ()
  outOfFuel site := throw (.fuel site)

/-- The traversal of `#erase` (`visitExpr`) run with the pure backend, assembling its result as
`erase` does. Reference: `MR E/ErasureFunction.v:989 erase` and
`MR E/ErasureFunction.v:1602 erase_global_deps`, the pair `(Σ', t')` of
`MR E/ErasureFunctionProperties.v:657 erase_correct`. -/
def erasePure (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (e : Expr) :
    Except EraseError (Program × List Kername) := do
  let ((t, s), _) ← (visitExpr (m := PureM) travFuel e).runPure {} { «config» := cfg } ⟨decls, view⟩ {}
  pure (.untyped s.gdecls (some t), s.inlinings)

/-! ## The recursion and `@[extern]` tests of the pure backend -/

/-- `name_occurs` as the pure backend runs it: exact names, no `_unsafe_rec` stripping.
Reference: none (Lean's environment-level recursion, DV-7). -/
def nameOccurs (name : Name) : Expr → Bool
  | .const n' _ => name == n'
  | .lam _ _ e _ | .mdata _ e | .proj _ _ e => nameOccurs name e
  | .app a b | .letE _ _ a b _ => nameOccurs name a || nameOccurs name b
  | _ => false

/-- The eraser's recursion test (`visitMutual`: `nonrecursive := single_decl && !name_occurs`),
at the pure backend. Reference: none (DV-7); pinned to `EraseProof.RecursiveDecl` by
`EraseProof.isRecursiveDecl_eq`. -/
def isRecursiveDecl (ci : ConstantInfo) : Bool :=
  ci.all.length != 1 || nameOccurs ci.name (ci.value! (allowOpaque := true))

/-- The eraser's `@[extern]` remapping test (`visitMutual`, single declarations): the declaration
becomes a λ□ axiom. Reference: the `Some`/`None` case that `MR E/Extract.v:264
erases_constant_body` excludes (DV-12). -/
def axiomatized (view : EnvView) (cfg : ErasureConfig) (ci : ConstantInfo) : Bool :=
  ci.all.length == 1 && view.isExtern ci.name && cfg.extern == .preferAxiom

end Erasure
