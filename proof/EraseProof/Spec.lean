import LeanToLambdaBox.Erasure.Entry
import EraseProof.Target
import ConLeche.Kernel.CheckDecl
import ConLeche.Kernel.CheckerBase
import ConLeche.Kernel.TypeChecker
import ConLeche.Model.Denotes

/-!
# The definitions of the statements

The definitions the statements of `Statements.lean` are about:

1. the bridge to con-leche (`Name.toCL`, `Level.toCL`, `toCL?`, `DeclsOf?`, `ConLecheAccepts`):
   con-leche's reading of the program's declarations and its pure fold;
2. the con-leche checks: `CLTyped`, `CLTypedAt`, `CLOk`, `CLErasable`, `CLProofTerm` on closed
   terms, and `CLCert`, `CLCertProof` on a marked subterm in the context of its enclosing binders,
   opened as con-leche opens binders, with the verdicts `CLFormer` (the checker's reducing
   type-former test) and `CLProof`;
3. the evaluation environment and its atoms (ports of `ML-V Spec.lean` §7);
4. the marks (`markErase`, `markEta`, `markReduced`, `unmark`) and `MarkOf`, the eraser's
   erasability decisions written on the source term, one rule per case of the traversal
   (`visitExpr`, `LeanToLambdaBox/Erasure.lean:856`);
5. the source semantics `SrcEval` on marked terms (port of `ML-V Spec.lean:908` with frozen rules
   and con-leche checks);
6. closures, the view, `NoPreDefs` and the sufficient fragment conditions (ports);
7. the erasure relation `Erases`/`ErasesAlt`, `ErasesInd`, `ErasesDecl`, `ErasesDeps` (port of
   `ML-V Spec.lean:1378-1615` without typing premises, `□` on marks, each mark asked of a
   certificate predicate), and the certificates of the emitted program (`MarksCert`, `ProgCert`);
8. `Sound` (the meaning of the source value in con-leche's model), `FirstOrderValue`, `foErase`,
   `FrozenLeaf`.

λ□ evaluation is `Target.lean` (a copy of `ML-V Target.lean`).

Citations: `CL <file>:<line>` is a file of con-leche (commit `d88e04e9b`); `ML-V <file>:<line>` is
a file of `proof/EraseProof/` in the Metalean development of this repository (#16, commit
`f3b934f`), which this development ports; `MR <file>` is a file of MetaRocq (commit `4b201296`),
`E/`, `P/` standing for `erasure/theories/`, `pcuic/theories/`; `LeanToLambdaBox/…` is the shipping
code; MC is Sozeau et al., "Correct and Complete Type Checking and Certified Erasure for Coq, in
Coq" (J. ACM 2025).
-/

open Lean Erasure

namespace EraseProof

/-! ## 1. The bridge to con-leche -/

/-- con-leche's own conversion of names, `CL ConLeche/Kernel/Name.lean:218 Name.ofLeanName`
(structural, injective; macro scopes kept). -/
def Name.toCL : Lean.Name → ConLeche.Name := ConLeche.Name.ofLeanName

/-- Levels; a level metavariable has no con-leche counterpart (`CL ConLeche/Frontend/Olean/Spec.lean:127`:
`mvar` is malformed input). -/
def Level.toCL : Lean.Level → Option ConLeche.Level
  | .zero => some .zero
  | .succ u => .succ <$> Level.toCL u
  | .max u v => return .max (← Level.toCL u) (← Level.toCL v)
  | .imax u v => return .imax (← Level.toCL u) (← Level.toCL v)
  | .param n => some (.param (Name.toCL n))
  | .mvar _ => none

/-- Expressions, as con-leche reads a stored Lean `Expr` (`CL ConLeche/Frontend/Olean/Spec.lean:162
exprNode`; the export's `CL ConLeche/Frontend/ExportC.lean:138 exprOfF`): binder names, binder infos
and `nonDep` dropped, `mdata` transparent (`Spec.lean:199`; so every mark is transparent),
`fvar`/`mvar` malformed (`Spec.lean:43`), `letE` kept. Reference: none (DV-1). -/
def toCL? : Lean.Expr → Option ConLeche.Expr
  | .bvar i => some (.bvar i)
  | .sort u => (.sort ·) <$> Level.toCL u
  | .const c us => (.const (Name.toCL c) ·) <$> us.mapM Level.toCL
  | .app f a => return .app (← toCL? f) (← toCL? a)
  | .lam _ t b _ => return .lam (← toCL? t) (← toCL? b)
  | .forallE _ t b _ => return .forallE (← toCL? t) (← toCL? b)
  | .letE _ t v b _ => return .letE (← toCL? t) (← toCL? v) (← toCL? b)
  | .lit (.natVal n) => some (.lit (.natVal n))
  | .lit (.strVal s) => some (.lit (.strVal s))
  | .mdata _ e => toCL? e
  | .proj s i e => (.proj (Name.toCL s) i ·) <$> toCL? e
  | .fvar _ | .mvar _ => none

/-- A constant's name, level parameters and type. Reference: `CL ConLeche/Frontend/ExportC.lean:216
cvOfF`. -/
def cvOf? (v : Lean.ConstantVal) : Option ConLeche.ConstantVal :=
  return ⟨Name.toCL v.name, v.levelParams.map Name.toCL, ← toCL? v.type⟩

/-- Reducibility hints, one to one. Reference: `CL ConLeche/Frontend/ExportC.lean:413`. -/
def hintOf : Lean.ReducibilityHints → ConLeche.ReducibilityHint
  | .«opaque» => .«opaque»
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- Quotient kinds. Reference: `CL ConLeche/Frontend/ExportC.lean:436`; the order is
`CL ConLeche/Kernel/Env.lean:320`. -/
def quotKindOf : Lean.QuotKind → ConLeche.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- A recursor rule with the parse placeholder `.plain` (`CL ConLeche/Frontend/ExportC.lean:233`,
`CL ConLeche/Kernel/Env.lean:137`). -/
def ruleOf? (r : Lean.RecursorRule) : Option ConLeche.RecRule :=
  return ⟨Name.toCL r.ctor, r.nfields, .plain, ← toCL? r.rhs⟩

/-- A recursor record: only the two sums stored (`CL ConLeche/Frontend/ExportC.lean:385`,
`CL ConLeche/Kernel/Env.lean:312`). -/
def recOf? (r : Lean.RecursorVal) : Option ConLeche.ConstantInfo :=
  return .recInfo (← cvOf? r.toConstantVal)
    (r.numParams + r.numMotives + r.numMinors + r.numIndices)
    (r.numParams + r.numMotives + r.numMinors) r.k (← r.rules.mapM ruleOf?)

/-- The number of leading `Π`s of a type, without reducing (`CL ConLeche/Frontend/ExportC.lean:227
indPiTeleLen`, on the reading `toCL?`, which drops `mdata`). -/
def piLen : Lean.Expr → Nat
  | .forallE _ _ b _ => piLen b + 1
  | .mdata _ e => piLen e
  | _ => 0

/-- The expression has no `mdata` node (a structural traversal, so that it reduces in the kernel).
-/
def NoMData : Lean.Expr → Bool
  | .mdata _ _ => false
  | .app f a => NoMData f && NoMData a
  | .lam _ t b _ | .forallE _ t b _ => NoMData t && NoMData b
  | .letE _ t v b _ => NoMData t && NoMData v && NoMData b
  | .proj _ _ e => NoMData e
  | _ => true

/-- Some name of `ns` occurs in the expression (a structural traversal, so that it reduces in the
kernel). -/
def mentionsAny (ns : List Name) : Lean.Expr → Bool
  | .const c _ => ns.contains c
  | .app f a => mentionsAny ns f || mentionsAny ns a
  | .lam _ t b _ | .forallE _ t b _ => mentionsAny ns t || mentionsAny ns b
  | .letE _ t v b _ => mentionsAny ns t || mentionsAny ns v || mentionsAny ns b
  | .mdata _ e | .proj _ _ e => mentionsAny ns e
  | _ => false

/-- Some `Π`-domain of the type mentions a name of `ns`: Lean's kernel test for a recursive block
(`lean4/src/kernel/inductive.cpp is_rec`), on the reading that drops `mdata`. -/
def hasDomainMentioning (ns : List Name) : Lean.Expr → Bool
  | .forallE _ t b _ => mentionsAny ns t || hasDomainMentioning ns b
  | .mdata _ e => hasDomainMentioning ns e
  | _ => false

/-- The type after `n` leading `Π`s, without reducing (`mdata` dropped). -/
def piResult : Nat → Lean.Expr → Lean.Expr
  | n + 1, .forallE _ _ b _ => piResult n b
  | n, .mdata _ e => piResult n e
  | _, e => e

/-- The head constant of an application spine (`mdata` dropped). -/
def appHeadConst : Lean.Expr → Option Name
  | .app f _ => appHeadConst f
  | .mdata _ e => appHeadConst e
  | .const c _ => some c
  | _ => none

/-- The recursor's type has one motive, whose type binds one variable (the major premise of an
inductive without indices): the motives `recShape` reads off the type (`recShape` returns them from
the binders after the parameters, whatever the minors). Reference: the recursor as Lean's kernel
builds it (`mk_rec_infos` in `src/kernel/inductive.cpp`). -/
def recMotivesOK (r : Lean.RecursorVal) : Bool :=
  match ((Erasure.piBinders r.type).1.drop r.numParams |>.take r.numMotives).map
      fun (_, d) => (Erasure.piBinders d).1.map (·.1) with
  | [[_]] => true
  | _ => false

/-- The Lean records of the block headed by `H` agree with one another as Lean's kernel generates
them: the fields con-leche's frontend checks (`CL ConLeche/Frontend/ExportC.lean:241
validateIndF`: one parameter count, a constructor's `cidx` its position in its type's `ctors`, its
`induct` that type, its `numFields` its `Π`-count past the parameters, a recursor's counts), and
the fields the traversal reads and con-leche does not: each type's `all` and `numIndices`; the
head of each constructor's result type is the type that lists it (con-leche groups the constructors
by that head, `CL ConLeche/Kernel/Inductives/BlockShape.lean:324 blockGroups`, and ignores the
record's `induct`, `:237`); and `isRec` is whether a
constructor has a `Π`-domain mentioning a member, and the recursors are exactly the `T.rec` of its
members, each eliminating the type it is named after (con-leche assigns a recursor to a member by
its major premise and checks only the set of names,
`CL ConLeche/Kernel/Inductives/BlockShape.lean:357 blockRecNameSetOk`; `collectDeps` looks the
recursors up by name). `tys` are the block's types, `cvs` their constructors, `rs` the recursors
of `P` with the block's `all`. Every recursor also has the block's parameter count, and a recursor of
a block of one type without indices has one motive binding the major premise only (`recMotivesOK`),
and every recursor's type names every member of the block (each member is the domain of a motive's
major premise; the fragment test reads a recursor's block only through its type), and every
recursor's minor premises are syntactic domains of its type without `mdata` (the traversal counts
a minor premise's binders with `Erasure.minorArity`, which stops at `mdata`, con-leche's reading
drops it); con-leche compares a recursor's type with the generated one up to definitional equality, so the syntactic
shape is a check of its own, as `RulesCanonical` is. No member has nested occurrences (`numNested = 0`: nested inductives are outside the fragment,
so a recursor's major premise names a member of its block). Reference: none (DV-3, DV-38). -/
def blockShapeOK (H : Lean.InductiveVal) (tys : List Lean.InductiveVal)
    (cvs : List (List Lean.ConstructorVal)) (rs : List Lean.RecursorVal) : Bool :=
  rs.all (fun r => r.numParams == H.numParams &&
      (H.all.length != 1 || r.numIndices != 0 || recMotivesOK r) &&
      H.all.all (fun n => mentionsAny [n] r.type) &&
      (List.range r.numMinors).all fun i =>
        ((Erasure.forallDom? (r.numParams + r.numMotives + i) r.type).map NoMData).getD false) &&
    tys.all (fun t => t.all == H.all && t.numParams == H.numParams &&
      match Erasure.arityShape t.type with
      | some (n, _) => n == H.numParams + t.numIndices
      | none => true) &&
    (tys.zip cvs).all (fun (t, cs) => cs.zipIdx.all fun (c, j) =>
      c.induct == t.name && c.cidx == j && c.numParams == H.numParams &&
        piLen c.type == H.numParams + c.numFields &&
        appHeadConst (piResult (H.numParams + c.numFields) c.type) == some t.name) &&
    tys.all (·.numNested == 0) &&
    tys.all (·.isRec == (cvs.flatten.any fun c => hasDomainMentioning H.all c.type)) &&
      rs.length == tys.length && tys.all fun t => rs.any fun r =>
        r.name == mkRecName t.name && r.numParams == H.numParams &&
          r.numMotives == tys.length && r.numMinors == (cvs.map List.length).sum &&
          r.numIndices == t.numIndices && r.getMajorInduct == t.name

/-- The block whose first member is `H`, as one `indDecl` (`CL ConLeche/Frontend/ExportC.lean:377
indBlockOfF`), if its records pass `blockShapeOK`: the formers in `all` order with `IndCaps` left
at its defaults (`:380`), then the constructors type by type in each type's `ctors` order, each
with the type that lists it (`:298`, `:382`), then the block's recursors (lean4export's
`blockRecs`, `CL ConLeche/Frontend/Olean/Emit.lean:275`; any order,
`CL ConLeche/Kernel/Inductives/StreamRecs.lean:186`), at the first former's parameter count
(`ExportC.lean:262`). `P` is read newest first, so the recursors are taken oldest first. -/
def blockOf? (P : List Lean.ConstantInfo) (H : Lean.InductiveVal) : Option ConLeche.Declaration := do
  let tys ← H.all.mapM fun n => match Erasure.findConst P n with
    | some (.inductInfo t) => some t
    | _ => none
  let cvs ← tys.mapM fun t => t.ctors.mapM fun n => match Erasure.findConst P n with
    | some (.ctorInfo c) => some c
    | _ => none
  let rs := P.reverse.filterMap fun
    | .recInfo r => if r.all == H.all then some r else none
    | _ => none
  guard (blockShapeOK H tys cvs rs = true)
  let types ← tys.mapM fun t => return ConLeche.ConstantInfo.indInfo (← cvOf? t.toConstantVal) {}
  let ctors ← (tys.zip cvs).mapM fun (t, cs) => cs.mapM fun c =>
    return .ctorInfo (← cvOf? c.toConstantVal) c.numParams c.numFields (Name.toCL t.name)
  let recs ← rs.mapM recOf?
  return .indDecl (types ++ ctors.flatten ++ recs) H.numParams

/-- One Lean constant's records (`CL ConLeche/Frontend/ExportC.lean:398 declOfF`). Unsafe and
partial constants (not inductives: an unsafe inductive rejects the program) are left out, as lean4export leaves them out
(`CL ConLeche/Frontend/Olean/Reads.lean:18 CKindF.skipped`); an inductive block is emitted at its
first member, and its other members, constructors and recursors are part of it: each must be
listed by its block (an inductive in its head's `all`, and in its own `all`, a constructor in its `induct`'s `ctors`, a
recursor's `all` that of the inductive at its head), so that every record of `P` is checked. -/
def declOf? (P : List Lean.ConstantInfo) : Lean.ConstantInfo → Option (List ConLeche.Declaration)
  | .axiomInfo v =>
    if v.isUnsafe then some [] else return [.axiomDecl (← cvOf? v.toConstantVal)]
  | .defnInfo v => match v.safety with
    | .safe => return [.defnDecl (← cvOf? v.toConstantVal) (← toCL? v.value) (hintOf v.hints)]
    | _ => some []
  | .thmInfo v => return [.thmDecl (← cvOf? v.toConstantVal) (← toCL? v.value)]
  | .opaqueInfo v =>
    if v.isUnsafe then some [] else return [.opaqueDecl (← cvOf? v.toConstantVal) (← toCL? v.value)]
  | .quotInfo v => return [.quotDecl (quotKindOf v.kind) (← cvOf? v.toConstantVal)]
  | .inductInfo v =>
    if v.isUnsafe then none
    else if v.all.head? == some v.name then return [← blockOf? P v]
    else match v.all.head?.bind (Erasure.findConst P) with
      | some (.inductInfo h) => if h.all == v.all && v.all.contains v.name then some [] else none
      | _ => none
  | .ctorInfo c => match Erasure.findConst P c.induct with
    | some (.inductInfo t) => if t.ctors.contains c.name then some [] else none
    | _ => none
  | .recInfo r => match r.all.head?.bind (Erasure.findConst P) with
    | some (.inductInfo t) => if t.all == r.all then some [] else none
    | _ => none

/-- The expression has no `mdata` node with the anonymous key, the key of the marks (`markMD`),
which elaboration never writes. -/
def NoMarkKeys : Lean.Expr → Bool
  | .mdata d e => !(d.entries.any (·.1 == .anonymous)) && NoMarkKeys e
  | .app f a => NoMarkKeys f && NoMarkKeys a
  | .lam _ t b _ | .forallE _ t b _ => NoMarkKeys t && NoMarkKeys b
  | .letE _ t v b _ => NoMarkKeys t && NoMarkKeys v && NoMarkKeys b
  | .proj _ _ e => NoMarkKeys e
  | _ => true

/-- No type and no value of the declarations has an `mdata` with the marks' key (the condition
`DeclsOf?` puts on the program). Reference: none (DV-32). -/
def NoMarkKeysDecls (ds : List ConstantInfo) : Bool :=
  ds.all fun ci => NoMarkKeys ci.type && (ci.value? true).all NoMarkKeys

/-- The expression mentions a free variable (`Expr.hasFVar`, structurally, so that the kernel
computes it). -/
def HasFVar : Lean.Expr → Bool
  | .fvar _ => true
  | .mdata _ e | .proj _ _ e => HasFVar e
  | .app f a => HasFVar f || HasFVar a
  | .lam _ t b _ | .forallE _ t b _ => HasFVar t || HasFVar b
  | .letE _ t v b _ => HasFVar t || HasFVar v || HasFVar b
  | _ => false

/-- No type and no value (definition, theorem or opaque) of the declarations mentions a free
variable: con-leche's forms of the program have none (`toCL?` is `none` on `fvar`). -/
def ClosedDecls (ds : List Lean.ConstantInfo) : Bool :=
  ds.all fun ci => !HasFVar ci.type && (ci.value? true).all (!HasFVar ·)

/-- con-leche's input for the program `P` (newest first, as `Erasure.findConst` reads it): the
records oldest first, `none` if two constants share a name, a type or value has an `mdata` with the
anonymous key (`NoMarkKeys`), a constant has no con-leche form, or
an inductive block's records disagree (`blockShapeOK`, `declOf?`). Reference: con-leche's frontend
`CL ConLeche/Frontend/ExportC.lean:398` on lean4export's output, whose `parseExportD` it equals on
the test programs and on Lean's `Eq`/`Quot`/`Nat`, with the record checks of
`CL ConLeche/Frontend/ExportC.lean:241 validateIndF` and those of the fields the traversal reads
(DV-3). -/
def DeclsOf? (P : List Lean.ConstantInfo) : Option (List ConLeche.Declaration) :=
  if (P.map (·.name)).Nodup ∧ P.all (fun ci => NoMarkKeys ci.type && (ci.value? true).all NoMarkKeys) then
    (P.reverse.mapM (declOf? P)).map List.flatten else none

/-- The head and the arguments, in order, of an application spine. -/
def clSpine : ConLeche.Expr → ConLeche.Expr × List ConLeche.Expr
  | e => go e []
where
  go : ConLeche.Expr → List ConLeche.Expr → ConLeche.Expr × List ConLeche.Expr
    | .app f a, acc => go f (a :: acc)
    | e, acc => (e, acc)

/-- The leading `λ`s of a term: their number and the body. -/
def clLams : ConLeche.Expr → Nat × ConLeche.Expr
  | .lam _ b => let r := clLams b; (r.1 + 1, r.2)
  | e => (0, e)

/-- The number of leading `Π`s of a term. -/
def clPis : ConLeche.Expr → Nat
  | .forallE _ b => clPis b + 1
  | _ => 0

/-- The index of a bound variable. -/
def clBvar? : ConLeche.Expr → Option Nat
  | .bvar i => some i
  | _ => none

/-- The leading `Π`s of a type: their number and the body. -/
def clPiBody : ConLeche.Expr → Nat × ConLeche.Expr
  | .forallE _ b => let r := clPiBody b; (r.1 + 1, r.2)
  | e => (0, e)

/-- The field that the last argument of a term names: after `k` binders and an application spine
whose last argument is a bound variable applied to the `k` binders in order, that variable's
position among the `n` field variables in scope outside the binders. -/
def clFieldOf (n k : Nat) (body : ConLeche.Expr) : Option Nat :=
  match (clSpine body).2.getLast? with
  | none => none
  | some l => match clBvar? (clSpine l).1 with
    | some b => if k ≤ b ∧ b - k < n then some (n - 1 - (b - k)) else none
    | none => none

/-- `ih` has the shape of an inductive hypothesis of a stored rule with `nF` fields and prefix
length `rP`, of a recursor with level parameters `lps`: `λ xs, rec_t.{lps} p⃗ idx⃗ (f xs)`, that is
`k` leading `λ`s over a recursor of the environment at the levels `lps` (as parameters), applied to
the `rP` prefix variables, the index arguments and the field `f` applied to the `k` bound
variables: `numIndices + rP + 1` arguments in all. -/
def IHShape (env : ConLeche.Env) (lps : List ConLeche.Name) (rP nF : Nat) (ih : ConLeche.Expr) : Bool :=
  let r := clLams ih
  let k := r.1
  let s := clSpine r.2
  (match s.1 with
   | .const n us => us == lps.map ConLeche.Level.param && env.consts.any fun
       | .recInfo v mI _ _ _ => v.name == n && s.2.length == mI + 1
       | _ => false
   | _ => false) &&
  s.2.length > rP &&
  (s.2.take rP).map clBvar? == (List.range rP).map (fun i => some (k + nF + rP - 1 - i)) &&
  (match s.2.getLast? with
   | none => false
   | some l =>
     let t := clSpine l
     (match clBvar? t.1 with
      | some j => k ≤ j && j < k + nF
      | none => false) &&
     t.2.map clBvar? == (List.range k).map (fun i => some (k - 1 - i)))

/-- The stored rule `r` of a recursor with prefix length `rP` has the generated shape: `rP + nfields`
leading `λ`s over a bound variable of the prefix (the constructor's minor premise) applied to the
`nfields` field variables, in order, and then to inductive hypotheses (`IHShape`, at the recursor's
level parameters `lps`). -/
def RuleShape (env : ConLeche.Env) (lps : List ConLeche.Name) (rP : Nat) (r : ConLeche.RecRule) : Bool :=
  let l := clLams r.rhs
  let s := clSpine l.2
  l.1 == rP + r.nfields &&
  (match clBvar? s.1 with
   | some h => r.nfields ≤ h && h < rP + r.nfields
   | none => false) &&
  (s.2.take r.nfields).map clBvar? == (List.range r.nfields).map (fun i => some (r.nfields - 1 - i)) &&
  (s.2.drop r.nfields).all (IHShape env lps rP r.nfields)

/-- The constructors of the block of a stored family with capabilities `caps`, in order: the
recorded constructors of each member of `caps.all`, the order of a recursor's minor premises. -/
def blockCtors (env : ConLeche.Env) (caps : ConLeche.IndCaps) : List ConLeche.Name :=
  caps.all.flatMap fun t => match env.find? t with
    | some (.indInfo _ c) => c.ctors
    | _ => []

/-- The field that the `j`-th binder of a minor premise `A` (an inductive hypothesis) recurses on,
among the `j` binders before it. -/
def minorIHField (A : ConLeche.Expr) (j : Nat) : Option Nat :=
  (ConLeche.Expr.binderDom j A).bind fun T => let r := clPiBody T; clFieldOf j r.1 r.2

/-- The stored rule `rl` of a recursor with type `ty` and prefix length `rP`, of the block with the
constructors `bc` and the recursors `brs`, is the rule of its own constructor: the constructor is in
the block and is stored with `rl.nfields` fields, the head of the right-hand side is the
constructor's minor premise (the prefix variable at position `rP - bc.length + g`, `g` the
constructor's position in `bc`), and the head has as many arguments as that minor premise (the
domain of `ty` at that position) has leading `Π`s: the fields, then the inductive hypotheses; each
hypothesis is a call of a recursor of the block (`brs`) under as many `λ`s as the minor premise's
binder at its position has leading `Π`s, and the hypotheses recurse, in order, on the fields that
the binders of the minor premise name (`clFieldOf`). -/
def RuleSelects (env : ConLeche.Env) (ty : ConLeche.Expr) (rP : Nat) (bc brs : List ConLeche.Name)
    (rl : ConLeche.RecRule) : Bool :=
  let q := rP - bc.length + bc.idxOf rl.ctor
  let s := clSpine (clLams rl.rhs).2
  bc.contains rl.ctor &&
  (match env.find? rl.ctor with
   | some (.ctorInfo _ _ nF _) => nF == rl.nfields
   | _ => false) &&
  clBvar? s.1 == some (rl.nfields + (rP - 1 - q)) &&
  (s.2.drop rl.nfields).all (fun ih => match (clSpine (clLams ih).2).1 with
    | .const n _ => brs.contains n
    | _ => false) &&
  (match ConLeche.Expr.binderDom q ty with
   | some A => s.2.length == clPis A &&
       (s.2.drop rl.nfields).map (fun ih => let r := clLams ih; clFieldOf rl.nfields r.1 r.2) ==
         (List.range' rl.nfields (clPis A - rl.nfields)).map (minorIHField A) &&
       (List.range' rl.nfields (clPis A - rl.nfields)).all (fun j => (minorIHField A j).isSome) &&
       (s.2.drop rl.nfields).map (fun ih => some (clLams ih).1) ==
         (List.range' rl.nfields (clPis A - rl.nfields)).map fun j =>
           (ConLeche.Expr.binderDom j A).map fun T => (clPiBody T).1
   | none => false)

/-- The K flag con-leche's block check expects of the recursor of a stored family with type `cvT`
and capabilities `caps` (`CL ConLeche/Kernel/Inductives/RecCheck.lean:463 recKExpected`, compared
with the record's flag by `CL ConLeche/Kernel/Inductives/StreamRecs.lean:199 streamKCheck`): the
block has one member, whose sort past its parameters and indices is zero at every valuation, with
one constructor, which has no fields. -/
def recKExpectedAt (env : ConLeche.Env) (cvT : ConLeche.ConstantVal) (caps : ConLeche.IndCaps) :
    Bool :=
  caps.all.length == 1 &&
  (match ConLeche.Expr.peelPis (caps.nparams + caps.nIdx) cvT.type with
   | some (.sort s) => s.isAlwaysZero
   | _ => false) &&
  (match caps.ctors with
   | [c] => match env.find? c with
     | some (.ctorInfo _ _ nF _) => nF == 0
     | _ => false
   | _ => false)

/-- The rules of the recursor named `R`, with type `ty`, prefix length `rP` and K flag `isK`, select
by constructor: for `R = T.rec`, `T` is a stored family, the rules are one per constructor of `T`, in
`T`'s order, each firing `.plain` (con-leche's installer's mode at a member major,
`CL ConLeche/Kernel/Env.lean:118 RecRuleFire`) and each the rule of its own constructor
(`RuleSelects`), whose recursive calls are of the recursors `t.rec` of the members `t` of `T`'s
block (so of `R` for a one-member block; the generator's callee `rec_t`,
`CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`), and the K flag is the expected one (`recKExpectedAt`). Other recursors (the quotient's) are not constrained. -/
def RulesSelected (env : ConLeche.Env) (R : ConLeche.Name) (ty : ConLeche.Expr) (rP : Nat)
    (isK : Bool) (rules : List ConLeche.RecRule) : Bool :=
  match R with
  | .str T "rec" => match env.find? T with
    | some (.indInfo cvT caps) =>
      rules.map (·.ctor) == caps.ctors && rules.all (·.fire == .plain) &&
        rules.all (RuleSelects env ty rP (blockCtors env caps) (caps.all.map (·.str "rec"))) &&
        isK == recKExpectedAt env cvT caps
    | _ => false
  | _ => true

/-- Every recursor stored in `env` has `majorIdx + 1` leading `Π`s in its type, every one of its
stored rules has the generated shape (`RuleShape`), and its rules select by constructor and its K
flag is the expected one (`RulesSelected`); every stored definition has distinct level parameters
(`CL ConLeche/Kernel/CheckerBase.lean:112`). It is decidable, and the kernel evaluates it on an
environment literal. con-leche stores the rules its generator writes
(`CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`, stored by `classRuleOk`, `:444`) and
proves their syntax only at install (`CL ConLeche/Model/Inductives/GenRuleSyn.lean:292
classGenRule_spec`); the facts it states of the accepted environment's rules are their scoping and
the number of their leading `λ`s (`CL ConLeche/Verify/EnvWF.lean:217`), and it checks the K flag at
install but states nothing of it at the fold, so the shape and the selection the ι step reads are
part of `ConLecheAccepts`. Reference: none (DV-38). -/
def RulesCanonical (env : ConLeche.Env) : Bool :=
  env.consts.all fun
    | .recInfo v mI rP isK rules => clPis v.type == mI + 1 && ConLeche.Name.nodup v.levelParams &&
        rules.all (RuleShape env v.levelParams rP) &&
        RulesSelected env v.name v.type rP isK rules
    | .defnInfo v _ _ => ConLeche.Name.nodup v.levelParams
    | _ => true

/-- Every stored projection table names its structure's single constructor: the structure is
stored with that constructor as its only one, and the constructor is stored with the table's
parameter and field counts, at the table's level parameters, with at least that many leading `Π`s.
con-leche installs a table only for a structure, from its constructor
(`CL ConLeche/Kernel/Env.lean:255 ProjTable`), but states of a stored table only its lookup
(`CL ConLeche/Verify/EnvWF.lean:22 Env.findProj?_some`); the structural projection rule reads its
constructor (`CL ConLeche/Rules/Rel.lean:179 Red.proj`). Decidable; the kernel evaluates it on an
environment literal. Reference: none (DV-38). -/
def TablesCanonical (env : ConLeche.Env) : Bool :=
  env.tables.all fun tbl =>
    (match env.find? tbl.structName with
     | some (.indInfo _ caps) => caps.ctors == [tbl.ctor]
     | _ => false) &&
    (match env.find? tbl.ctor with
     | some (.ctorInfo cv nP nF _) => nP == tbl.numParams && nF == tbl.numFields &&
         cv.levelParams == tbl.levelParams && (ConLeche.Expr.peelPis (nP + nF) cv.type).isSome
     | _ => false)

/-- con-leche's pure fold accepts `P` with environment `env`, at the standard fuel
(`CL ConLeche/Kernel/CheckerBase.lean:44 pureOps`) and the empty `Nat.div`/`Nat.mod` pin list
(`CL ConLeche/MainTheorem.lean:70`); the form of `CL ConLeche/Model/Fold.lean:373
checkDeclsPure_sound_of`, which gives a model `EnvModelM V env` in every `[SetTheory V]`. No
prelude: the fold starts from the empty environment (`CL ConLeche/Kernel/CheckDecl.lean:180`), so
`P` contains, in dependency order, everything its records use; basis declarations in `P` are
checked against their pins. The third and fourth conjuncts are `RulesCanonical` and
`TablesCanonical`, which con-leche's installers make true of every environment it accepts.
Reference: `wf_ext Σ` (`MR P/PCUICTyping.v:507`); DV-3, DV-38. -/
def ConLecheAccepts (P : List Lean.ConstantInfo) (env : ConLeche.Env) : Prop :=
  ∃ ds, DeclsOf? P = some ds ∧
    ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] ds = .ok env ∧
    RulesCanonical env = true ∧ TablesCanonical env = true

/-! ## 2. The con-leche checks -/

/-- con-leche's full-grade inference accepts the closed term `t` at some fuel
(`CL ConLeche/Kernel/TypeChecker.lean:39 inferTypeCore`; marks are transparent to `toCL?`).
Reference: `welltyped Σ [] t` (`MR P/PCUICTyping.v`); `InferClaim`
(`CL ConLeche/Model/Claims.lean:112`) turns it into `WellDenoted` and membership; DV-1. -/
def CLTyped (env : ConLeche.Env) (t : Lean.Expr) : Prop :=
  ∃ c F T, toCL? t = some c ∧ ConLeche.inferTypeCore .verified false env F 0 c = .ok T

/-- con-leche's full-grade inference accepts the closed term `t` at the checker's own fuel
`checkFuel` (`CLTyped` at a fixed fuel, so that it is a computation, decidable and refutable by
evaluation; marks are transparent to `toCL?`). Reference: `welltyped Σ [] t`
(`MR P/PCUICTyping.v`); DV-32. -/
def CLTypedAt (env : ConLeche.Env) (t : Lean.Expr) : Prop :=
  ∃ c T, toCL? t = some c ∧ ConLeche.inferTypeCore .verified false env ConLeche.checkFuel 0 c = .ok T

/-- con-leche's checker reduces the type `T` at depth `d` to a type-former type: at most `k`
times, its whnf is a sort (accept) or a `Π` whose body is opened at depth `d` as the free variable
`.fvar d A` and walked on; anything else rejects. The loop of con-leche's `formerSortLoop`
(`CL ConLeche/Kernel/Core.lean:537`), every codomain reduced, as the oracle's `isArity`
(`LeanToLambdaBox/Erasure/Pure.lean:376`) and MetaRocq's `isArity` (`MR P/PCUICTyping.v:29`) do. A
syntactic verdict of the checker: con-leche's model has no semantic criterion that separates a
type former from data (DV-32). -/
def CLFormer (env : ConLeche.Env) (F : Nat) : Nat → Nat → ConLeche.Expr → Bool
  | _, 0, _ => false
  | d, k + 1, T => match ConLeche.whnf .verified false env F d T with
    | .ok (.sort _) => true
    | .ok (.forallE A b) => CLFormer env F (d + 1) k (b.instantiate1 (.fvar d A))
    | _ => false

/-- The type `T` con-leche inferred at depth `d` is a proposition: its own type's whnf is a sort
that is zero at every valuation (`CL ConLeche/Kernel/Level.lean:201 isAlwaysZero`). Then a term
of type `T` denotes the proof point in every model (`clCert_proof_pt_statement`). Reference: the
proof disjunct of `isErasable` (`MR E/Extract.v:18`). -/
def CLProof (env : ConLeche.Env) (F d : Nat) (T : ConLeche.Expr) : Prop :=
  ∃ S u, ConLeche.inferTypeCore .verified false env F d T = .ok S ∧
    ConLeche.whnf .verified false env F d S = .ok (.sort u) ∧ u.isAlwaysZero

/-- con-leche's verdict on the type `T` it inferred at depth `d`: the type of a type former
(`CLFormer`, at most `F` binders) or of a proof (`CLProof`). Reference: the two disjuncts of
`isErasable` (`MR E/Extract.v:18`). -/
def CLVerdict (env : ConLeche.Env) (F d : Nat) (T : ConLeche.Expr) : Prop :=
  CLFormer env F d F T = true ∨ CLProof env F d T

/-- The closed term `t` is typed by con-leche as a type former or as a proof (`CLVerdict` at depth
`0`), at some fuel. Reference: `isErasable` (`MR E/Extract.v:18`), decided by a verified checker
instead of a typing derivation (DV-32). -/
def CLErasable (env : ConLeche.Env) (t : Lean.Expr) : Prop :=
  ∃ c F T, toCL? t = some c ∧ ConLeche.inferTypeCore .verified false env F 0 c = .ok T ∧
    CLVerdict env F 0 T

/-- The closed term `t` is typed by con-leche as a proof (`CLProof` at depth `0`), at some fuel:
`CLErasable` with the proof verdict only. Reference: the proof disjunct of `isErasable`
(`MR E/Extract.v:18`) (DV-32). -/
def CLProofTerm (env : ConLeche.Env) (t : Lean.Expr) : Prop :=
  ∃ c F T, toCL? t = some c ∧ ConLeche.inferTypeCore .verified false env F 0 c = .ok T ∧
    CLProof env F 0 T

/-- A binder around a marked position: its domain (the type of a `let`), and the value of a
`let`. Reference: none. -/
abbrev CtxBinder := Expr × Option Expr

/-- `s` under the binders `Γ` (innermost first), closed by λs and `let`s, the outermost binder
first. Reference: none. -/
def lamTele : List CtxBinder → Expr → Expr
  | [], s => s
  | (A, none) :: Γ, s => lamTele Γ (.lam .anonymous A s .default)
  | (T, some v) :: Γ, s => lamTele Γ (.letE .anonymous T v s false)

/-- con-leche's opening of the first `k` binders of `c`, from depth `d`, as its inference opens
them (`CL ConLeche/Kernel/Core.lean:1230 inferBody`): a λ at depth `d` opens as the free variable
`.fvar d A` and the next binder is at depth `d + 1` (the convention of
`CL ConLeche/Rules/Rel.lean:13`); a `let` body is instantiated with the value, at the same depth.
The result is the depth reached and the opened term. Reference: none. -/
def openLams : Nat → Nat → ConLeche.Expr → Option (Nat × ConLeche.Expr)
  | d, 0, c => some (d, c)
  | d, k + 1, .lam A b => openLams (d + 1) k (b.instantiate1 (.fvar d A))
  | d, k + 1, .letE _ v b => openLams d k (b.instantiate1 v)
  | _, _ + 1, _ => none

/-- con-leche certifies the subterm `s`, whose enclosing binders are `Γ` (innermost first), as a
proof or a type former, at the checker's own fuel `checkFuel`: the closed telescope `lamTele Γ s`
is typed by full-grade inference (so the domains are checked as types and the `let` values
against their types), and `s`, opened by con-leche's convention (`openLams`) at the depth `d` it
reaches, has an inferred type `T` with `CLVerdict`. Proof verdict: the closed telescope denotes the
proof point in every model of an accepted environment (`clCert_proof_pt_statement`). Type-former
verdict: con-leche's checker types `s` as a type former (`CLFormer`), a syntactic verdict with no
model content (con-leche's model does not separate type formers from data, DV-32). Decidable:
every component is a computation. Reference: `isErasable` of an open term (`MR E/Extract.v:18`)
(DV-32). -/
def CLCert (env : ConLeche.Env) (Γ : List CtxBinder) (s : Expr) : Prop :=
  ∃ c d c' T₀ T, toCL? (lamTele Γ s) = some c ∧
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel 0 c = .ok T₀ ∧
    openLams 0 Γ.length c = some (d, c') ∧
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d c' = .ok T ∧
    CLVerdict env ConLeche.checkFuel d T

/-- `CLCert` with the proof verdict only: con-leche certifies the subterm `s`, whose enclosing
binders are `Γ`, as a proof (`CLProof`); then the closed telescope denotes the proof point in every
model of an accepted environment (`clCert_proof_pt_statement`). Reference: the proof disjunct of
`isErasable` of an open term (`MR E/Extract.v:18`) (DV-32). -/
def CLCertProof (env : ConLeche.Env) (Γ : List CtxBinder) (s : Expr) : Prop :=
  ∃ c d c' T₀ T, toCL? (lamTele Γ s) = some c ∧
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel 0 c = .ok T₀ ∧
    openLams 0 Γ.length c = some (d, c') ∧
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d c' = .ok T ∧
    CLProof env ConLeche.checkFuel d T

/-! ## 3. The evaluation environment and its atoms (ports of `ML-V Spec.lean` §7) -/

/-- First declaration named `c`. Port of `ML-V Spec.lean:424`. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findDecl (decls : List ConstantInfo) (c : Name) : Option ConstantInfo :=
  decls.find? (·.name == c)

/-- Every free variable of `e` satisfies `p`. Port of `ML-V Bridge/Basic.lean:20`; reference:
lean4lean `FVarsIn`. -/
def FVarsIn (p : FVarId → Prop) : Expr → Prop
  | .fvar x => p x
  | .app f a => FVarsIn p f ∧ FVarsIn p a
  | .lam _ t b _ | .forallE _ t b _ => FVarsIn p t ∧ FVarsIn p b
  | .letE _ t v b _ => FVarsIn p t ∧ FVarsIn p v ∧ FVarsIn p b
  | .mdata _ e | .proj _ _ e => FVarsIn p e
  | _ => True

/-- Every constant of `e`, and the structure of every projection of `e`, satisfies `p`. Port of
`ML-V Spec.lean:566`; reference: `term_global_deps` (`MR E/EAstUtils.v:406`). -/
def ConstsIn (p : Name → Prop) : Expr → Prop
  | .const c _ => p c
  | .app f a => ConstsIn p f ∧ ConstsIn p a
  | .lam _ t b _ | .forallE _ t b _ => ConstsIn p t ∧ ConstsIn p b
  | .letE _ t v b _ => ConstsIn p t ∧ ConstsIn p v ∧ ConstsIn p b
  | .mdata _ e => ConstsIn p e
  | .proj S _ e => p S ∧ ConstsIn p e
  | _ => True

/-- The program's environment as evaluation sees it: its declarations, the configuration's
`@[extern]` remapping (DV-12) and the configuration (which `SrcEval.delta` reads to mark the
values it unfolds, as the traversal erases them). Port of `ML-V Spec.lean:648`, with the
configuration where that file has the compiled pre-definitions (none is used, `NoPreDefs`, DV-35).
Reference: the environment of `MR P/PCUICWcbvEval.v:231 eval`. -/
structure EvalEnv where
  decls : List ConstantInfo
  axiomatized : ConstantInfo → Bool
  cfg : ErasureConfig

/-- The inductive of a recognized `casesOn` constant of `decls` (the shipping recognizer
`Erasure.casesInfo?`, `LeanToLambdaBox/Erasure/Pure.lean:107`). Port of `ML-V Spec.lean:656` on a
list of declarations. Reference: none (`tCase` is syntax in PCUIC; DV-25). -/
def casesOnOf? (decls : List ConstantInfo) (c : Name) : Option InductiveVal :=
  match casesInfo? decls c with
  | some ci => match findDecl decls ci.indName with
    | some (.inductInfo iv) => some iv
    | _ => none
  | none => none

/-- `casesOnOf?` at `σ`. Port of `ML-V Spec.lean:656`. -/
def EvalEnv.casesOn? (σ : EvalEnv) (c : Name) : Option InductiveVal := casesOnOf? σ.decls c

/-- Position of the major premise of `T.casesOn` (`params, motive, indices, major, minors`). Port
of `ML-V Spec.lean:664`. -/
def casesMajor (iv : InductiveVal) : Nat := iv.numParams + 1 + iv.numIndices

/-- Arity of `T.casesOn`. Port of `ML-V Spec.lean:667`. -/
def casesArity (iv : InductiveVal) : Nat := casesMajor iv + 1 + iv.ctors.length

/-- The arity of the quotient constants erased by their own rules: `Quot.mk α r a` (3) and
`Quot.lift α r β f h q` (6), as `visitConstApp` η-expands them (`LeanToLambdaBox/Erasure.lean:958`).
Port of `ML-V Spec.lean:673`. -/
def quotEvalArity : Lean.QuotKind → Option Nat
  | .ctor => some 3
  | .lift => some 6
  | _ => none

/-- The arity of a constructor, recognized `casesOn`, erased quotient head or recursor of `σ`.
Port of `ML-V Spec.lean:682`. -/
def specialArity (σ : EvalEnv) (c : Name) : Option Nat :=
  match findDecl σ.decls c with
  | some (.ctorInfo cv) => some (cv.numParams + cv.numFields)
  | some (.quotInfo qv) => quotEvalArity qv.kind
  | some (.recInfo rv) => some (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)
  | _ => (σ.casesOn? c).map casesArity

/-- A spine with an arity (`specialArity`) and at most that many arguments: evaluated as a whole
(`SrcEval.ctor`, `casesIota`, `casesFrozen`, `casesLit*`, `quotMk`, `quotLift`, `recIota`), never by
`beta`/`appCong`. Port of `ML-V Spec.lean:723`. -/
def ShortSpine (σ : EvalEnv) (e : Expr) : Prop :=
  ∃ c us ar, e.getAppFn = .const c us ∧ specialArity σ c = some ar ∧ e.getAppNumArgs ≤ ar

/-- δ: definitions that the configuration does not remap and that are not recognized `casesOn`
constants; theorems, axioms and opaques have no δ (DV-24, DV-10). Port of `ML-V Spec.lean:730`
without the pre-definition exclusion. Reference: `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
def EvalEnv.unfold? (σ : EvalEnv) (c : Name) : Option (ConstantInfo × Expr) :=
  match findDecl σ.decls c with
  | some ci@(.defnInfo v) =>
    if σ.axiomatized ci || (σ.casesOn? c).isSome then none
    else some (ci, v.value)
  | _ => none

/-- A level that is zero under every assignment, structurally. Port of `ML-V Spec.lean:743`. -/
def EvidentZero : Level → Bool
  | .zero => true
  | .max a b => EvidentZero a && EvidentZero b
  | .imax _ b => EvidentZero b
  | _ => false

/-- Declarations without δ that may head an evident proposition. Port of `ML-V Spec.lean:751`;
reference: `tInd` heads (`MR P/PCUICWcbvEval.v:51 atom`), DV-11. -/
def DeltaFree : ConstantInfo → Bool
  | .axiomInfo _ | .opaqueInfo _ | .thmInfo _ | .inductInfo _ => true
  | _ => false

/-- An evident proposition `Π xs, h.{vs} a₁…aₙ`. Port of `ML-V Spec.lean:758`; reference:
`isPropositional` (`MR P/PCUICFirstorder.v:109`). -/
def EvidentProp (decls : List ConstantInfo) : Expr → Bool
  | .forallE _ _ b _ => EvidentProp decls b
  | .mdata _ e => EvidentProp decls e
  | e => match e.getAppFn with
    | .const h vs => match findDecl decls h with
      | some ci => DeltaFree ci && match arityShape ci.type with
        | some (n, u) => n == e.getAppNumArgs && EvidentZero (Pure.instLevel ci.levelParams vs u)
        | none => false
      | none => false
    | _ => false

/-- Declarations evaluated by their own rules. Port of `ML-V Spec.lean:772`. -/
def OwnRules : ConstantInfo → Bool
  | .ctorInfo _ | .recInfo _ => true
  | .quotInfo q => match q.kind with
    | .type => false
    | _ => true
  | _ => false

/-- Theorems. Port of `ML-V Spec.lean:780`. -/
def IsThm : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- δ-less constants that are values: evident type formers, proofs of evident propositions,
theorems. Port of `ML-V Spec.lean:787`; reference: `MR P/PCUICWcbvEval.v:51 atom`, DV-11. -/
def EvalEnv.isAtom (σ : EvalEnv) (c : Name) : Bool :=
  match findDecl σ.decls c with
  | some ci => (σ.unfold? c).isNone && (σ.casesOn? c).isNone && !OwnRules ci &&
      ((arityShape ci.type).isSome || EvidentProp σ.decls ci.type || IsThm ci)
  | none => false

/-- λ, sort, Π. Port of `ML-V Spec.lean:794`; reference: `MR P/PCUICWcbvEval.v:51 atom`. -/
def SrcAtom : Expr → Prop
  | .lam .. | .sort _ | .forallE .. => True
  | _ => False

/-- A constructor value of the inductive `T`. Port of `ML-V Spec.lean:800`; reference:
`mkApps (tConstruct ind i u) args` (`MR P/PCUICWcbvEval.v:500 value`). -/
def CtorValue (σ : EvalEnv) (T : Name) (m : Expr) (i : Nat) (fs : List Expr) : Prop :=
  ∃ C us cv ps, findDecl σ.decls C = some (.ctorInfo cv) ∧ cv.induct = T ∧ cv.cidx = i ∧
    ps.length = cv.numParams ∧ fs.length = cv.numFields ∧
    m = mkAppN (.const C us) (ps ++ fs).toArray

/-- The constructor form of a recursor's major value: a Nat literal is ``Nat.zero`` or
``Nat.succ`` applied to its predecessor literal. Port of `ML-V Spec.lean:810`. -/
def natLitCtor (e : Expr) : Expr :=
  match e.rawNatLit? with
  | some 0 => .const ``Nat.zero []
  | some (k + 1) => .app (.const ``Nat.succ []) (.lit (.natVal k))
  | none => e

/-- The inductive `T` is declared in `Prop`: its type is an arity whose sort is evidently zero.
In the fragment it coincides with the λ□ `propositional` flag the traversal computes
(`Pure.isPropFormerType`, `LeanToLambdaBox/Erasure/Pure.lean:388`; `Erasure.sortDecided`). Port
of `ML-V Spec.lean:834`; reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`). -/
def EvalEnv.propInd (σ : EvalEnv) (T : Name) : Bool :=
  match findDecl σ.decls T with
  | some (.inductInfo iv) => match arityShape iv.type with
    | some (_, u) => EvidentZero u
    | none => false
  | _ => false

/-- The inductive types of a recursor's block and their constructors, in order, as `visitRec`
reads them (`LeanToLambdaBox/Erasure.lean:1001`). Port of `ML-V Spec.lean:884` on a list of
declarations. -/
def recBlockOf? (decls : List ConstantInfo) (rv : RecursorVal) :
    Option (List InductiveVal × List ConstructorVal) := do
  let ivs ← rv.all.mapM fun t => match findDecl decls t with
    | some (.inductInfo iv) => some iv
    | _ => none
  let cvs ← (ivs.flatMap (·.ctors)).mapM fun c => match findDecl decls c with
    | some (.ctorInfo cv) => some cv
    | _ => none
  pure (ivs, cvs)

/-- `recBlockOf?` at `σ`. Port of `ML-V Spec.lean:884`. -/
def EvalEnv.recBlock? (σ : EvalEnv) (rv : RecursorVal) :
    Option (List InductiveVal × List ConstructorVal) := recBlockOf? σ.decls rv

/-! ## 4. Marks and `MarkOf` -/

/-- The metadata of a mark: one entry with the anonymous key (which elaboration never writes) and
the mark's kind, `0` erase, `1` eta, `2` reduced. Reference: none (DV-32). -/
abbrev markMD (k : Nat) : MData := ⟨[(.anonymous, .ofNat k)]⟩

/-- `s` is erased by the traversal (`visitExpr` answers `□`): a frozen subterm of the source
semantics, related to `□` only. Reference: none (DV-32). -/
abbrev markErase (s : Expr) : Expr := .mdata (markMD 0) s

/-- A λ the traversal introduced by η-expansion (`withAppEtaToMinArity`,
`LeanToLambdaBox/Erasure.lean:676`; `lambdaMonocularOrIntro`, `:638`), one mark per binder.
Reference: none (MetaRocq η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
abbrev markEta (e : Expr) : Expr := .mdata (markMD 1) e

/-- The discriminant of a `casesOn` that `visitCases` reduces at erasure time
(`LeanToLambdaBox/Erasure.lean:1130`: one constructor, the discriminant's sort may be zero); it
is not evaluated. Reference: none (`eval_iota_sing`, `MR E/EWcbvEval.v:162`, at erasure time;
DV-25). -/
abbrev markReduced (d : Expr) : Expr := .mdata (markMD 2) d

/-- Whether the loose bound variable `k` occurs, structurally. Reference: none. -/
def bvarOccurs : Nat → Expr → Bool
  | k, .bvar i => i == k
  | k, .app f a => bvarOccurs k f || bvarOccurs k a
  | k, .lam _ t b _ | k, .forallE _ t b _ => bvarOccurs k t || bvarOccurs (k + 1) b
  | k, .letE _ t v b _ => bvarOccurs k t || bvarOccurs k v || bvarOccurs (k + 1) b
  | k, .mdata _ e | k, .proj _ _ e => bvarOccurs k e
  | _, _ => false

/-- η-contraction of `λ x. f x` (`x` not in `f`) to `f`, lowered under the binder; any other term
unchanged. Reference: none (DV-23). -/
def etaContract : Expr → Expr
  | e@(.lam _ _ (.app f (.bvar 0)) _) => if bvarOccurs 0 f then e else f.instantiate1' (.bvar 0)
  | e => e

/-- Remove the marks: strip `erase` and `reduced` marks, η-contract `eta` marks; other metadata
kept. `unmark` inverts `MarkOf` up to the metadata `MarkOf` drops. Reference: none (DV-32). -/
def unmark : Expr → Expr
  | .mdata d e => match d with
    | ⟨[(.anonymous, .ofNat 0)]⟩ | ⟨[(.anonymous, .ofNat 2)]⟩ => unmark e
    | ⟨[(.anonymous, .ofNat 1)]⟩ => etaContract (unmark e)
    | _ => .mdata d (unmark e)
  | .app f a => .app (unmark f) (unmark a)
  | .lam n t b bi => .lam n (unmark t) (unmark b) bi
  | .forallE n t b bi => .forallE n (unmark t) (unmark b) bi
  | .letE n t v b nd => .letE n (unmark t) (unmark v) (unmark b) nd
  | .proj s i e => .proj s i (unmark e)
  | e => e

/-- The run-time certificate of a source evaluation rule: con-leche infers a type for the closed
redex the rule forms from evaluated parts, and for its `unmark`ed reading (the η-marks contracted,
which is the reading `Sound` speaks of); it takes the place of subject reduction, which con-leche
does not have. For a term without η-marks the two runs coincide. Reference: none (DV-33). -/
def CLOk (env : ConLeche.Env) (t : Lean.Expr) : Prop := CLTyped env t ∧ CLTyped env (unmark t)

/-- `x` becomes the bound variable `d` (under binders, `d` plus their number); loose indices from
`d` on move up by one; the inverse of `instantiate1' (.fvar x) d`. Port of
`ML-V Bridge/Abstract.lean:23 absFV`; the traversal's `abstract` on λ□ terms
(`LeanToLambdaBox/Basic.lean:149`). -/
def absFV (x : FVarId) : Nat → Expr → Expr
  | d, .bvar i => .bvar (if i < d then i else i + 1)
  | d, .fvar y => if y == x then .bvar d else .fvar y
  | d, .app f a => .app (absFV x d f) (absFV x d a)
  | d, .lam n t b bi => .lam n (absFV x d t) (absFV x (d + 1) b) bi
  | d, .forallE n t b bi => .forallE n (absFV x d t) (absFV x (d + 1) b) bi
  | d, .letE n t v b nd => .letE n (absFV x d t) (absFV x d v) (absFV x (d + 1) b) nd
  | d, .mdata m e => .mdata m (absFV x d e)
  | d, .proj s i e => .proj s i (absFV x d e)
  | _, e => e

/-- `x` is fresh for the locals and the terms: no local is `x`, and neither the locals' types and
values nor the terms mention it (the traversal's `freshFVarId` counter,
`LeanToLambdaBox/Erasure/Pure.lean:495`, gives such a variable). Reference: none (DV-13). -/
def Fresh (x : FVarId) (ls : List Local) (es : List Expr) : Prop :=
  (∀ l ∈ ls, l.fvarId ≠ x ∧ FVarsIn (· ≠ x) l.type ∧ ∀ v, l.value? = some v → FVarsIn (· ≠ x) v) ∧
  ∀ e ∈ es, FVarsIn (· ≠ x) e

/-- The oracle's answer on `e` under the locals `ls`, at the pure path's fuel
(`PureM.isErasable`, `LeanToLambdaBox/Erasure/Pure.lean:504`). Reference: none (the shipping
oracle, not verified; DV-32). -/
abbrev oracle (decls : List ConstantInfo) (ls : List Local) (e : Expr) : Except EraseError Bool :=
  Pure.isErasable ⟨decls⟩ oracleFuel ls e

/-- The leading `Π` of a type as `forallMonocular` reads it (`LeanToLambdaBox/Erasure.lean:624`):
syntactically, otherwise after the oracle's weak-head normalisation. Reference: none. -/
def forallView? (decls : List ConstantInfo) (ls : List Local) (T : Expr) :
    Option (Name × Expr × Expr × BinderInfo) :=
  match T with
  | .forallE y D C bi => some (y, D, C, bi)
  | _ => match Pure.whnf ⟨decls⟩ oracleFuel ls T with
    | .ok (.forallE y D C bi) => some (y, D, C, bi)
    | _ => none

/-- The arity to which `visitConstApp` η-expands an application of `c`
(`LeanToLambdaBox/Erasure.lean:958`), in its order of tests: a recognized `casesOn`, a
constructor, `Quot.mk` (3), `Quot.lift` (6), a recursor that `visitRec` does not leave as a
constant (`recStaysConstant`); `none` for every other head. Reference: none. -/
def markArity? (decls : List ConstantInfo) (cfg : ErasureConfig) (c : Name) : Option Nat :=
  match casesInfo? decls c with
  | some ci => some ci.arity
  | none => match ctorArity? decls c with
    | some ar => some ar
    | none => match findDecl decls c with
      | some (.quotInfo qv) => quotEvalArity qv.kind
      | some (.recInfo r) => match recBlockOf? decls r with
        | some (ivs, cvs) =>
          if recStaysConstant cfg.nat r ivs cvs then none
          else some (r.numParams + r.numMotives + r.numMinors + r.numIndices + 1)
        | none => none
      | _ => none

mutual
/-- `MarkOf decls cfg ls e ê`: `ê` is `e` with the decisions of the traversal `visitExpr`
(`LeanToLambdaBox/Erasure.lean:856`) at the pure backend over `decls` and the configuration `cfg`
written on it, under the traversal's locals `ls`: every node `visitExpr` visits is asked to the
oracle (`oracle`); an answer `true` marks it `erase` (`markErase`), an answer `false` descends as
the traversal does. Binders are opened with a fresh free variable (`Fresh`) and closed again
(`absFV`); `mdata` is dropped (`visitExpr` ignores it); types, binder domains and the arguments the
traversal drops are kept unmarked. The relation reads the shipping oracle; it neither assumes nor
proves anything about it. Reference: none (DV-32). -/
inductive MarkOf (decls : List ConstantInfo) (cfg : ErasureConfig) :
    List Local → Expr → Expr → Prop
  /-- The oracle answers `true` (`visitExpr`, `return .box`). -/
  | erase : oracle decls ls e = .ok true → MarkOf decls cfg ls e (markErase e)
  /-- A free variable (`visitExpr`, `.fvar`). -/
  | fvar : oracle decls ls (.fvar x) = .ok false → MarkOf decls cfg ls (.fvar x) (.fvar x)
  /-- Metadata is ignored (`visitExpr`, `.mdata`). -/
  | mdata : oracle decls ls (.mdata m e) = .ok false → MarkOf decls cfg ls e ê →
      MarkOf decls cfg ls (.mdata m e) ê
  /-- `visitLambda` (`:896`): the body under a fresh local of the binder's name and domain. -/
  | lam : oracle decls ls (.lam n A b bi) = .ok false → Fresh x ls [b] →
      MarkOf decls cfg (⟨x, n, A, none⟩ :: ls) (b.instantiate1' (.fvar x)) bM →
      MarkOf decls cfg ls (.lam n A b bi) (.lam n A (absFV x 0 bM) bi)
  /-- `visitLet` (`:901`): the value and the body under a fresh `let`-local. -/
  | letE : oracle decls ls (.letE n T v b nd) = .ok false → Fresh x ls [v, b] →
      MarkOf decls cfg (⟨x, n, T, some v⟩ :: ls) v vM →
      MarkOf decls cfg (⟨x, n, T, some v⟩ :: ls) (b.instantiate1' (.fvar x)) bM →
      MarkOf decls cfg ls (.letE n T v b nd) (.letE n T vM (absFV x 0 bM) nd)
  /-- `visitProj` (`:911`): the major premise. -/
  | proj : oracle decls ls (.proj S i e) = .ok false → findDecl decls S = some (.inductInfo iv) →
      MarkOf decls cfg ls e ê → MarkOf decls cfg ls (.proj S i e) (.proj S i ê)
  /-- `visitLiteral` (`:872`) under `nat := .peano`: `0` is `Nat.zero`. -/
  | litZero : oracle decls ls (.lit (.natVal 0)) = .ok false → cfg.nat = .peano →
      MarkOf decls cfg ls (.lit (.natVal 0)) (.lit (.natVal 0))
  /-- `visitLiteral` under `nat := .peano`: `k + 1` is `Nat.succ` applied to the literal `k`,
  which the traversal visits (`visitConstructor`, `:1035`). -/
  | litSucc : oracle decls ls (.lit (.natVal (k + 1))) = .ok false → cfg.nat = .peano →
      k + 1 ≤ peanoMaxLiteral → MarkOf decls cfg ls (.lit (.natVal k)) (.lit (.natVal k)) →
      MarkOf decls cfg ls (.lit (.natVal (k + 1))) (.lit (.natVal (k + 1)))
  /-- `visitApp` (`:927`) on a head that is not a constant: the head and the arguments. -/
  | app {f fM : Expr} {as âs : List Expr} :
      oracle decls ls (mkAppN f as.toArray) = .ok false → as ≠ [] → f.isApp = false →
      (∀ c us, f ≠ .const c us) → MarkOf decls cfg ls f fM → as.length = âs.length →
      (∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â) →
      MarkOf decls cfg ls (mkAppN f as.toArray) (mkAppN fM âs.toArray)
  /-- `visitConstApp` (`:958`) on a constant without its own rule (`markArity? = none`):
  `visitAppArgs (visitConst f) args`; the head is not asked to the oracle. -/
  | constApp {as âs : List Expr} :
      oracle decls ls (mkAppN (.const c us) as.toArray) = .ok false →
      markArity? decls cfg c = none → as.length = âs.length →
      (∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â) →
      MarkOf decls cfg ls (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) âs.toArray)
  /-- `visitConstApp` on a head with its own rule: `withAppEtaToMinArity` at the arity
  (`MarkEta`) on the type the oracle infers for the spine. -/
  | special {as : List Expr} :
      oracle decls ls (mkAppN (.const c us) as.toArray) = .ok false →
      markArity? decls cfg c = some ar →
      Pure.inferType ⟨decls⟩ oracleFuel ls [] (mkAppN (.const c us) as.toArray) = .ok T →
      MarkEta decls cfg ls ar T c us as ê → MarkOf decls cfg ls (mkAppN (.const c us) as.toArray) ê

/-- `withAppEtaToMinArity.go` (`LeanToLambdaBox/Erasure.lean:681`): `c.{us} as` of type `T` is
η-expanded, one `eta`-marked λ per missing argument (`forallMonocular` on `T`), until it has the
arity `ar`; then the saturated spine is marked by `MarkSat`. Reference: none (DV-23). -/
inductive MarkEta (decls : List ConstantInfo) (cfg : ErasureConfig) :
    List Local → Nat → Expr → Name → List Level → List Expr → Expr → Prop
  | sat : ar ≤ as.length → MarkSat decls cfg ls c us as ê → MarkEta decls cfg ls ar T c us as ê
  | intro : as.length < ar → forallView? decls ls T = some (y, D, C, bi) → Fresh x ls (T :: as) →
      MarkEta decls cfg (⟨x, y, D, none⟩ :: ls) ar (C.instantiate1' (.fvar x)) c us
        (as ++ [.fvar x]) ê →
      MarkEta decls cfg ls ar T c us as (markEta (.lam y D (absFV x 0 ê) bi))

/-- The saturated spines with their own rule: `visitCases` (`LeanToLambdaBox/Erasure.lean:1092`),
`visitConstructor` (`:1035`), `Quot.mk`/`Quot.lift` (`:958`), `visitRec` (`:1001`). Reference:
none (DV-32). -/
inductive MarkSat (decls : List ConstantInfo) (cfg : ErasureConfig) :
    List Local → Name → List Level → List Expr → Expr → Prop
  /-- A `casesOn` whose motive lands in `Prop` (no level parameter besides the inductive's): the
  whole spine is `□` (`:1100`), with no oracle call. -/
  | casesProp {as : List Expr} : casesOnOf? decls c = some iv →
      findDecl decls c = some (.defnInfo cd) → cd.levelParams.length = iv.levelParams.length →
      MarkSat decls cfg ls c us as (markErase (mkAppN (.const c us) as.toArray))
  /-- A `casesOn` reduced at erasure time (`:1130`): one constructor, the discriminant's sort may
  be zero (`Pure.typeLevel`, `Level.isNeverZero`); the discriminant is not visited and is marked
  `reduced`, the alternative is visited as an expression, the extra arguments are visited.
  Constructors with index fields are not modelled (`idxVals`; out of the fragment). -/
  | casesReduced {pre extra êxtra : List Expr} : casesOnOf? decls c = some iv →
      findDecl decls c = some (.defnInfo cd) → cd.levelParams.length ≠ iv.levelParams.length →
      pre.length = casesMajor iv → Pure.typeLevel ⟨decls⟩ oracleFuel ls d = .ok u →
      u.isNeverZero = false → iv.ctors = [cn] → findDecl decls cn = some (.ctorInfo cv) →
      (indexFields cv.numParams cv.type).all (·.isNone) = true →
      MarkOf decls cfg ls alt âlt → extra.length = êxtra.length →
      (∀ (i : Nat) a â, extra[i]? = some a → êxtra[i]? = some â → MarkOf decls cfg ls a â) →
      MarkSat decls cfg ls c us (pre ++ [d] ++ [alt] ++ extra)
        (mkAppN (.const c us) (pre ++ [markReduced d] ++ [âlt] ++ êxtra).toArray)
  /-- A `casesOn` erased to a λ□ `case` (`:1144`, `visitCasesOn`): the discriminant, each
  alternative under its constructor's fields (`visitAlt`, `:1249`, as `MarkAlt` on the type the
  oracle infers for it), the extra arguments. -/
  | cases {pre alts âlts extra êxtra : List Expr} : casesOnOf? decls c = some iv →
      findDecl decls c = some (.defnInfo cd) → cd.levelParams.length ≠ iv.levelParams.length →
      pre.length = casesMajor iv → alts.length = iv.ctors.length →
      Pure.typeLevel ⟨decls⟩ oracleFuel ls d = .ok u →
      (u.isNeverZero = false → iv.ctors.length ≠ 1 ∧ ∀ cn ∈ iv.ctors, ∀ cv,
        findDecl decls cn = some (.ctorInfo cv) → (indexFields cv.numParams cv.type).all (·.isNone) = true) →
      MarkOf decls cfg ls d dM → alts.length = âlts.length →
      (∀ (i : Nat) cn, iv.ctors[i]? = some cn → ∃ cv, findDecl decls cn = some (.ctorInfo cv)) →
      (∀ (i : Nat) alt, alts[i]? = some alt → ∃ T, Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T) →
      (∀ (i : Nat) cn cv alt âlt T, iv.ctors[i]? = some cn → findDecl decls cn = some (.ctorInfo cv) →
        alts[i]? = some alt → âlts[i]? = some âlt →
        Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T → MarkAlt decls cfg ls cv.numFields alt T âlt) →
      extra.length = êxtra.length →
      (∀ (i : Nat) a â, extra[i]? = some a → êxtra[i]? = some â → MarkOf decls cfg ls a â) →
      MarkSat decls cfg ls c us (pre ++ [d] ++ alts ++ extra)
        (mkAppN (.const c us) (pre ++ [dM] ++ âlts ++ êxtra).toArray)
  /-- `visitConstructor` (`:1035`): every argument is visited (the pure backend keeps every field). -/
  | ctor {as âs : List Expr} : casesInfo? decls c = none → ctorArity? decls c = some ar →
      as.length = âs.length →
      (∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â) →
      MarkSat decls cfg ls c us as (mkAppN (.const c us) âs.toArray)
  /-- `Quot.mk α r a`: the element and the extra arguments are visited. -/
  | quotMk {extra êxtra : List Expr} : casesInfo? decls c = none → ctorArity? decls c = none →
      findDecl decls c = some (.quotInfo qv) → qv.kind = .ctor → MarkOf decls cfg ls a â →
      extra.length = êxtra.length →
      (∀ (i : Nat) x xM, extra[i]? = some x → êxtra[i]? = some xM → MarkOf decls cfg ls x xM) →
      MarkSat decls cfg ls c us ([α, r, a] ++ extra) (mkAppN (.const c us) ([α, r, â] ++ êxtra).toArray)
  /-- `Quot.lift α r β f h q`: the function, the quotient and the extra arguments are visited. -/
  | quotLift {extra êxtra : List Expr} : casesInfo? decls c = none → ctorArity? decls c = none →
      findDecl decls c = some (.quotInfo qv) → qv.kind = .lift → MarkOf decls cfg ls f fM →
      MarkOf decls cfg ls q qM → extra.length = êxtra.length →
      (∀ (i : Nat) x xM, extra[i]? = some x → êxtra[i]? = some xM → MarkOf decls cfg ls x xM) →
      MarkSat decls cfg ls c us ([α, r, β, f, h, q] ++ extra)
        (mkAppN (.const c us) ([α, r, β, fM, h, qM] ++ êxtra).toArray)
  /-- `visitRec` (`:1001`): the minor premises, the indices, the major premise and the extra
  arguments are visited, the parameters and motives are dropped; the oracle's sort of the major
  (`direct`) is computed. -/
  | recr {ps ms mins minsM is îs extra êxtra : List Expr} : casesInfo? decls c = none →
      ctorArity? decls c = none → findDecl decls c = some (.recInfo r) →
      recBlockOf? decls r = some (ivs, cvs) → recStaysConstant cfg.nat r ivs cvs = false →
      (recShape r.numParams r.numMotives r.type (cvs.map (·.numFields))).isSome = true →
      ps.length = r.numParams → ms.length = r.numMotives → mins.length = r.numMinors →
      is.length = r.numIndices → (∃ u, Pure.typeLevel ⟨decls⟩ oracleFuel ls maj = .ok u) →
      mins.length = minsM.length →
      (∀ (i : Nat) x xM, mins[i]? = some x → minsM[i]? = some xM → MarkOf decls cfg ls x xM) →
      is.length = îs.length →
      (∀ (i : Nat) x xM, is[i]? = some x → îs[i]? = some xM → MarkOf decls cfg ls x xM) →
      MarkOf decls cfg ls maj majM → extra.length = êxtra.length →
      (∀ (i : Nat) x xM, extra[i]? = some x → êxtra[i]? = some xM → MarkOf decls cfg ls x xM) →
      MarkSat decls cfg ls c us (ps ++ ms ++ mins ++ is ++ [maj] ++ extra)
        (mkAppN (.const c us) (ps ++ ms ++ minsM ++ îs ++ [majM] ++ êxtra).toArray)

/-- `lambdaOrIntroToArity` (`LeanToLambdaBox/Erasure.lean:662`) and `visitAlt` (`:1249`): an
alternative of type `T` under `k` fields; a leading λ is peeled under a fresh local of the type's
`Π` (`lambdaMonocularOrIntro`, `:638`), any other term is applied to a fresh local and the binder
marked `eta`; at `0` the body is visited. Reference: the branches of `MR E/Extract.v:109
erases_tCase`. -/
inductive MarkAlt (decls : List ConstantInfo) (cfg : ErasureConfig) :
    List Local → Nat → Expr → Expr → Expr → Prop
  | done : MarkOf decls cfg ls e ê → MarkAlt decls cfg ls 0 e T ê
  | lam : forallView? decls ls T = some (y, D, C, bi') → Fresh x ls [T, b] →
      MarkAlt decls cfg (⟨x, y, D, none⟩ :: ls) k (b.instantiate1' (.fvar x))
        (C.instantiate1' (.fvar x)) bM →
      MarkAlt decls cfg ls (k + 1) (.lam n A b bi) T (.lam n A (absFV x 0 bM) bi)
  | intro : (∀ n A b bi, e ≠ .lam n A b bi) → forallView? decls ls T = some (y, D, C, bi') →
      Fresh x ls [T, e] →
      MarkAlt decls cfg (⟨x, y, D, none⟩ :: ls) k (.app e (.fvar x)) (C.instantiate1' (.fvar x)) bM →
      MarkAlt decls cfg ls (k + 1) e T (markEta (.lam y D (absFV x 0 bM) bi'))
end

/-! ## 5. Source semantics -/

/-- Heads excluded by `appCong`: λ (plain or `eta`-marked), sort, Π, literals, frozen terms,
constructor, `casesOn` and `Quot.mk` spines. Port of `ML-V Spec.lean:820` with the marked heads
added. Reference: the side condition of `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`). -/
def BlocksCong (σ : EvalEnv) : Expr → Prop
  | .lam .. | .sort _ | .forallE .. | .lit _ => True
  | .mdata ⟨[(.anonymous, .ofNat 0)]⟩ _ | .mdata ⟨[(.anonymous, .ofNat 1)]⟩ _ => True
  | e => (∃ c us cv, e.getAppFn = .const c us ∧ findDecl σ.decls c = some (.ctorInfo cv)) ∨
    (∃ c us iv, e.getAppFn = .const c us ∧ σ.casesOn? c = some iv) ∨
    (∃ c us qv, e.getAppFn = .const c us ∧ findDecl σ.decls c = some (.quotInfo qv) ∧
      qv.kind = .ctor)

/-- con-leche's ι step at the recursor `T.rec`, on a major premise whose head is the constructor at
the head of `m`, fires with no certificate by the stored records (case 2 of con-leche's ι case
split, `CL ConLeche/Kernel/CoreDefs.lean:1040 iotaNoCert`, read at the rule of `T.rec` for that
constructor): the recursor is K, or the constructor's family is never `Prop` and has as many level
parameters as the rule has comparand levels. A computation on the stored records. Reference: none
(DV-33). -/
def IotaNoCertAt (env : ConLeche.Env) (T : Name) (m : Expr) : Prop :=
  ∃ C us cvR mI rP isK rules rl cvC nP nF ind, m.getAppFn = .const C us ∧
    env.find? (Name.toCL (mkRecName T)) = some (.recInfo cvR mI rP isK rules) ∧
    rules.find? (·.ctor == Name.toCL C) = some rl ∧
    env.find? (Name.toCL C) = some (.ctorInfo cvC nP nF ind) ∧
    ConLeche.iotaNoCert env.find? isK ind (ConLeche.recFireLevelCount rl cvC.levelParams) = true

/-- con-leche certifies, at the full grade, the constructor telescope that its ι step checks in
case 3 of its case split (`CL ConLeche/Kernel/Core.lean:955 iotaCertsFull`; `iotaCertsFullFueled`
at the fuel `F`), on the major premise that stands for the proof `d` of a `casesOn` on `T`: the
constructor `C`, at the comparand levels and parameters of the rule of `T.rec` for `C` with the
recursor at the levels `us` and the parameters `ps`
(`CL ConLeche/Kernel/CoreDefs.lean:995 recFireComparands`), applied to the parameters and to the
projections of `d`, one per field.
Reference: none (DV-25, DV-33). -/
def FrozenFieldsCert (env : ConLeche.Env) (T C : Name) (us : List Level) (ps : List Expr)
    (d : Expr) : Prop :=
  ∃ cvR mI rP isK rules rl cvC nP nF ind cus cps cd F,
    env.find? (Name.toCL (mkRecName T)) = some (.recInfo cvR mI rP isK rules) ∧
    rules.find? (·.ctor == Name.toCL C) = some rl ∧
    env.find? (Name.toCL C) = some (.ctorInfo cvC nP nF ind) ∧
    us.mapM Level.toCL = some cus ∧ ps.mapM toCL? = some cps ∧ toCL? d = some cd ∧
    ConLeche.iotaCertsFull (ConLeche.pureFns .verified false env F) env 0
      (cvC.type.instantiateLevelParams cvC.levelParams
        (ConLeche.recFireComparands rl nP cvR.levelParams cus cvC.levelParams cps rP).1)
      ((ConLeche.recFireComparands rl nP cvR.levelParams cus cvC.levelParams cps rP).2 ++
        (List.range nF).map fun j => .proj (Name.toCL T) j cd) = .ok true

/-- Weak call-by-value evaluation of closed marked source terms (port of `ML-V Spec.lean:908`): a
frozen (`erase`-marked) subterm is a value once con-leche types it as a proof or a type former
(`frozen`); a frozen function applied is frozen (`frozenApp`, λ□ `eval_box`); a `casesOn` reduced
at erasure time continues with its alternative at frozen projections of the discriminant
(`casesFrozen`); a projection of a frozen proof is frozen (`projFrozen`); an `eta`-marked λ is a λ
(`etaLam`, `etaBeta`); δ marks the unfolded value as the traversal erases it (`delta`, `MarkOf` at
the value's own levels, then instantiated); the rules that form a redex or a data value from
evaluated parts carry the con-leche certificate `CLOk` of it (DV-33). No rule evaluates a
pre-definition (none is used, DV-35), an η-expansion or metadata (they are in the marks) or a
proof (proofs are frozen) (DV-32). Reference: `MR P/PCUICWcbvEval.v:231 eval`; MC §5.6. -/
inductive SrcEval (env : ConLeche.Env) (σ : EvalEnv) : Expr → Expr → Prop
  /-- `eval_beta` (`MR P/PCUICWcbvEval.v:234`). -/
  | beta : ¬ ShortSpine σ (.app f a) → SrcEval env σ f (.lam n A b bi) → SrcEval env σ a a' →
      CLOk env (.app (.lam n A b bi) a') →
      SrcEval env σ (b.instantiate1' a') v → SrcEval env σ (.app f a) v
  /-- `eval_beta` on an `eta`-marked λ. -/
  | etaBeta : ¬ ShortSpine σ (.app f a) → SrcEval env σ f (markEta (.lam n A b bi)) →
      SrcEval env σ a a' → CLOk env (.app (markEta (.lam n A b bi)) a') →
      SrcEval env σ (b.instantiate1' a') v → SrcEval env σ (.app f a) v
  /-- `eval_zeta` (`:241`). -/
  | zeta : SrcEval env σ val val' → CLOk env (.letE n T val b nd) → CLOk env (.letE n T val' b nd) →
      SrcEval env σ (b.instantiate1' val') v → SrcEval env σ (.letE n T val b nd) v
  /-- `eval_delta` (`:247`): the value marked as the traversal erases it, at its own levels. -/
  | delta : σ.unfold? c = some (ci, body) → MarkOf σ.decls σ.cfg [] body bM →
      SrcEval env σ (Pure.instLevels ci.levelParams us bM) v → SrcEval env σ (.const c us) v
  /-- `eval_atom` on `tInd`/propositional constants (`:331`, DV-11). -/
  | constAtom : σ.isAtom c = true → SrcEval env σ (.const c us) (.const c us)
  /-- `eval_construct` (`:303`): a saturated constructor spine evaluates its arguments. -/
  | ctor {as vs : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      as.length = cv.numParams + cv.numFields → as.length = vs.length →
      (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SrcEval env σ a v) →
      CLOk env (mkAppN (.const c us) vs.toArray) →
      SrcEval env σ (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray)
  /-- `eval_iota` (`:253`): the major evaluates to a constructor value; the alternative of its
  constructor is applied to its fields. -/
  | casesIota {as : List Expr} : σ.casesOn? c = some iv → as.length = casesArity iv →
      as[casesMajor iv]? = some m → SrcEval env σ m mv → CtorValue σ iv.name mv i fs →
      CLOk env (mkAppN (.const c us) (as.set (casesMajor iv) mv).toArray) →
      IotaNoCertAt env iv.name mv →
      as[casesMajor iv + 1 + i]? = some alt → SrcEval env σ (mkAppN alt fs.toArray) v →
      SrcEval env σ (mkAppN (.const c us) as.toArray) v
  /-- `eval_iota` on a Nat literal major: `0`. -/
  | casesLitZero {as : List Expr} : σ.casesOn? c = some iv → iv.name = ``Nat →
      as.length = casesArity iv → as[casesMajor iv]? = some m →
      SrcEval env σ m (.lit (.natVal 0)) →
      CLOk env (mkAppN (.const c us) (as.set (casesMajor iv) (.lit (.natVal 0))).toArray) →
      IotaNoCertAt env iv.name (.const ``Nat.zero []) → as[casesMajor iv + 1]? = some alt →
      SrcEval env σ alt v → SrcEval env σ (mkAppN (.const c us) as.toArray) v
  /-- `eval_iota` on a Nat literal major: `k + 1`. -/
  | casesLitSucc {as : List Expr} : σ.casesOn? c = some iv → iv.name = ``Nat →
      as.length = casesArity iv → as[casesMajor iv]? = some m →
      SrcEval env σ m (.lit (.natVal (k + 1))) →
      CLOk env (mkAppN (.const c us) (as.set (casesMajor iv) (.lit (.natVal (k + 1)))).toArray) →
      IotaNoCertAt env iv.name (.const ``Nat.succ []) → as[casesMajor iv + 2]? = some alt →
      SrcEval env σ (.app alt (.lit (.natVal k))) v → SrcEval env σ (mkAppN (.const c us) as.toArray) v
  /-- A `casesOn` reduced at erasure time (`markReduced` discriminant): con-leche types the
  discriminant, read unmarked, as a proof (`CLProofTerm`); if the constructor has no fields, its ι step
  fires with no certificate (`IotaNoCertAt`); if it has fields, the inductive has no
  indices and con-leche certifies the constructor telescope at the projections of the discriminant
  (`FrozenFieldsCert`, the certificate of its ι step on a proof); the alternative continues at the
  frozen projections of the discriminant, one per field (λ□: the shipping reduced form, the
  alternative applied to `□`). The fragment test admits a reduced `casesOn` only on an inductive
  whose sort is written `Prop` (`Erasure.eliminatedUndecided`,
  `LeanToLambdaBox/Erasure/Entry.lean:254`), whose fields are proofs. Reference: `eval_iota_sing`
  (`MR E/EWcbvEval.v:162`); DV-25. -/
  | casesFrozen {as : List Expr} : σ.casesOn? c = some iv → as.length = casesArity iv →
      iv.ctors = [cn] → findDecl σ.decls cn = some (.ctorInfo cv) →
      as[casesMajor iv]? = some (markReduced d) → CLProofTerm env (unmark d) →
      (cv.numFields = 0 → IotaNoCertAt env iv.name (.const cn us)) →
      (0 < cv.numFields →
        iv.numIndices = 0 ∧
          FrozenFieldsCert env iv.name cn us ((as.take iv.numParams).map unmark) (unmark d)) →
      as[casesMajor iv + 1]? = some alt →
      SrcEval env σ (mkAppN alt ((List.range cv.numFields).map fun j =>
        markErase (.proj iv.name j d)).toArray) v →
      SrcEval env σ (mkAppN (.const c us) as.toArray) v
  /-- `Quot.mk α r a` evaluates its element (as `eval_construct`; DV-29). -/
  | quotMk : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor → SrcEval env σ a a' →
      CLOk env (mkAppN (.const c us) [α, r, a'].toArray) →
      SrcEval env σ (mkAppN (.const c us) [α, r, a].toArray) (mkAppN (.const c us) [α, r, a'].toArray)
  /-- The quotient ι as `eval_beta` (DV-29). -/
  | quotLift : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .lift →
      SrcEval env σ f (.lam x A b bi) → SrcEval env σ q (mkAppN (.const c' us') [α', r', a].toArray) →
      findDecl σ.decls c' = some (.quotInfo qv') → qv'.kind = .ctor →
      CLOk env (mkAppN (.const c us)
        [α, r, β, .lam x A b bi, h, mkAppN (.const c' us') [α', r', a].toArray].toArray) →
      (∃ l F, us.head?.bind Level.toCL = some l ∧
        ConLeche.iotaCaseAt (ConLeche.pureFns .verified false env F).whnf env.find? false
          (Name.toCL ``Quot) [l] = .ok false) →
      SrcEval env σ (b.instantiate1' a) v →
      SrcEval env σ (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v
  /-- The recursor ι under call by value (port of `ML-V Spec.lean:999`; DV-30). -/
  | recIota {ps ms mins mvs fs rfs ihvs : List Expr} : findDecl σ.decls c = some (.recInfo rv) →
      rv.all = [T] → c = mkRecName T → σ.recBlock? rv = some ([iv], cvs) → rv.numIndices = 0 →
      recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) = some (motives, minors) →
      (∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
        (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, [])) →
      ps.length = rv.numParams → ms.length = rv.numMotives → mins.length = rv.numMinors →
      mins.length = mvs.length →
      (∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → SrcEval env σ m mv) →
      SrcEval env σ maj mj → CtorValue σ T (natLitCtor mj) k fs → minors[k]? = some mi →
      mvs[k]? = some mk →
      CLOk env (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [mj]).toArray) →
      IotaNoCertAt env T (natLitCtor mj) →
      (mi.ihs.mapM fun h => fs[h.field]?) = some rfs → rfs.length = ihvs.length →
      (∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
        SrcEval env σ (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w) →
      CLOk env (mkAppN mk (fs ++ ihvs).toArray) →
      SrcEval env σ (mkAppN mk (fs ++ ihvs).toArray) v →
      SrcEval env σ (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v
  /-- `eval_proj` (`:264`). -/
  | proj : SrcEval env σ e m → CtorValue σ S m 0 fs → fs[i]? = some a → CLOk env (.proj S i m) →
      SrcEval env σ (.proj S i e) a
  /-- A projection of a `Prop` structure out of a frozen proof is frozen (λ□ `eval_proj_prop`,
  `MR E/EWcbvEval.v:238`). -/
  | projFrozen : σ.propInd S = true → SrcEval env σ e (markErase d) → CLErasable env (.proj S i d) →
      SrcEval env σ (.proj S i e) (markErase (.proj S i d))
  /-- Nat literals are values, with the certificate of a data value (as `ctor`). -/
  | lit : CLOk env (.lit (.natVal k)) → SrcEval env σ (.lit (.natVal k)) (.lit (.natVal k))
  /-- `eval_app_cong` (`:311`): an atom spine applied. -/
  | appCong : ¬ ShortSpine σ (.app f a) → SrcEval env σ f f' → ¬ BlocksCong σ f' →
      SrcEval env σ a a' → CLOk env (.app f' a') → SrcEval env σ (.app f a) (.app f' a')
  /-- `eval_atom` (`:331`) on λ, sort, Π. -/
  | atom : SrcAtom e → SrcEval env σ e e
  /-- An `eta`-marked λ is a value. -/
  | etaLam : SrcEval env σ (markEta (.lam n A b bi)) (markEta (.lam n A b bi))
  /-- A frozen subterm is a value when con-leche types it as a proof or a type former. -/
  | frozen : CLErasable env s → SrcEval env σ (markErase s) (markErase s)
  /-- `eval_box` (`MR E/EWcbvEval.v:121`): a frozen function applied to a value is frozen. -/
  | frozenApp : ¬ ShortSpine σ (.app f a) → SrcEval env σ f (markErase s) → SrcEval env σ a a' →
      CLErasable env (.app s a') → CLTyped env (unmark (.app s a')) →
      SrcEval env σ (.app f a) (markErase (.app s a'))

/-! ## 6. Closures, views, the fragment -/

/-- The expressions the pure traversal reads from a closure. Port of `ML-V Spec.lean:1055`. -/
def ReadExpr (decls : List ConstantInfo) (ci : ConstantInfo) (x : Expr) : Prop :=
  x = ci.type ∨
    (∃ d, ci = .defnInfo d ∧ x = d.value ∧ (casesOnOf? decls d.name).isNone) ∨
    ∃ o, ci = .opaqueInfo o ∧ x = o.value

/-- Kernames of the program's constants are distinct. Port of `ML-V Spec.lean:1061`; reference:
none (DV-14). -/
def KernameInj (decls : List ConstantInfo) : Prop :=
  ∀ c₁ c₂, (findDecl decls c₁).isSome → (findDecl decls c₂).isSome →
    toKername c₁ = toKername c₂ → c₁ = c₂

/-- `decls` is a sub-environment of `P`. Port of `ML-V Spec.lean:1066`; reference: `extends`
(`MR common/theories/Environment.v`). -/
def SubEnv (decls P : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, findDecl P ci.name = some ci

/-- The evaluation environment of `P` under the configuration (DV-12). Port of
`ML-V Spec.lean:1085` with the configuration in place of the pre-definitions. -/
def evalEnvOf (view : EnvView) (cfg : ErasureConfig) (P : List ConstantInfo) : EvalEnv :=
  ⟨P, axiomatized view cfg, cfg⟩

/-- A Nat literal occurs. Port of `ML-V Spec.lean:1135`. -/
def HasNatLit : Expr → Bool
  | .lit (.natVal _) => true
  | .app f a => HasNatLit f || HasNatLit a
  | .lam _ t b _ | .forallE _ t b _ => HasNatLit t || HasNatLit b
  | .letE _ t v b _ => HasNatLit t || HasNatLit v || HasNatLit b
  | .mdata _ e | .proj _ _ e => HasNatLit e
  | _ => false

/-- The view `#erase` reads agrees with `P` on `P`'s names, and the compiled pre-definition the
view holds for a declaration of `P` (`Erasure.preDef?`, under any configuration) names only
constants of `P` (and `Nat` is in `P` if it has a Nat literal): what the fragment test reads
through the view, which con-leche does not check, is in `P`. Port of `ML-V Spec.lean:1106` with
the pre-definition conjunct; reference: `Σ ∼_ext X` (hypothesis of
`MR E/ErasureFunctionProperties.v:657 erase_correct`); DV-3, DV-35. -/
def ViewAgrees (view : EnvView) (P : List ConstantInfo) : Prop :=
  ∀ ci ∈ P, view.find? ci.name = some ci ∧ ∀ cfg pre, preDef? view cfg ci = some pre →
    ConstsIn (fun c => (findDecl P c).isSome) pre ∧ (HasNatLit pre → (findDecl P ``Nat).isSome)

/-- No declaration of the closure `decls` that the traversal erases by its value is erased
through a compiled pre-definition (`Erasure.preDef?`, `LeanToLambdaBox/Erasure/Pure.lean:456`:
none has a `partial` `_unsafe_rec` companion that `structural := .unsafeRec` would erase instead of
its kernel value); a remapped `@[extern]` definition (`axiomatized`) is exempt, since
`visitMutual` gives it no body (the fragment test still reads its pre-definition, whose constants
`ViewAgrees` puts in `P`). A pre-definition has no con-leche denotation, so the source semantics
has no rule for it. Decidable (`decide`). Reference: none (DV-35). -/
def NoPreDefs (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, axiomatized view cfg ci = false → (preDef? view cfg ci).isNone = true

/-- A level without metavariables. Port of `ML-V Spec.lean:1112`. -/
def LevelPlain : Level → Bool
  | .zero | .param _ => true
  | .succ l => LevelPlain l
  | .max a b | .imax a b => LevelPlain a && LevelPlain b
  | .mvar _ => false

/-- No free variable, metavariable, level metavariable or string literal; under `nat := .machine`
no Nat literal and none of the machine-integer constants. Port of `ML-V Spec.lean:1121`. -/
def PlainExpr (cfg : ErasureConfig) : Expr → Prop
  | .fvar _ | .mvar _ | .lit (.strVal _) => False
  | .lit (.natVal _) => cfg.nat = .peano
  | .sort u => LevelPlain u = true
  | .const c us => (∀ u ∈ us, LevelPlain u = true) ∧
      (cfg.nat = .machine → c ∉ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc,
        ``Nat.casesOn, ``Int.casesOn])
  | .app f a => PlainExpr cfg f ∧ PlainExpr cfg a
  | .lam _ t b _ | .forallE _ t b _ => PlainExpr cfg t ∧ PlainExpr cfg b
  | .letE _ t v b _ => PlainExpr cfg t ∧ PlainExpr cfg v ∧ PlainExpr cfg b
  | .mdata _ e | .proj _ _ e => PlainExpr cfg e
  | .bvar _ => True

/-- `decls` contains what the pure traversal reads from `e`. Port of `ML-V Spec.lean:1148`. -/
def ReadClosed (decls : List ConstantInfo) (e : Expr) : Prop :=
  let inD := fun c => (findDecl decls c).isSome = true
  ConstsIn inD e ∧ (HasNatLit e → inD ``Nat) ∧
  ∀ ci ∈ decls, (∀ x, ReadExpr decls ci x → ConstsIn inD x ∧ (HasNatLit x → inD ``Nat)) ∧
    (∀ n ∈ ci.all, inD n) ∧ (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, inD n) ∧
    (∀ cv, ci = .ctorInfo cv → inD cv.induct) ∧
    (∀ iv, casesOnOf? decls ci.name = some iv → inD iv.name ∧ inD (mkRecName iv.name)) ∧
    (∀ iv, ci = .inductInfo iv → iv.ctors.length = 1 → inD (mkRecName iv.name))

/-- An inductive of `decls` that the traversal may eliminate. Port of `ML-V Spec.lean:1160`. -/
def Eliminated (decls : List ConstantInfo) (iv : InductiveVal) : Prop :=
  (casesOnOf? decls (.str iv.name "casesOn")).isSome ∨
    ∃ cn cv, iv.ctors = [cn] ∧ findDecl decls cn = some (.ctorInfo cv) ∧ 0 < cv.numFields

/-- A recursor in the shape `SrcEval.recIota` evaluates. Port of `ML-V Spec.lean:1169`. -/
def RecInFragment (cfg : ErasureConfig) (decls : List ConstantInfo) (r : RecursorVal) : Prop :=
  ∃ T iv cvs, r.name = mkRecName T ∧ r.all = [T] ∧
    recBlockOf? decls r = some ([iv], cvs) ∧
    recShapeInFragment r [iv] cvs = true ∧ recStaysConstant cfg.nat r [iv] cvs = false

/-- `x` mentions recursors only in the shape the fragment admits. Port of `ML-V Spec.lean:1177`. -/
def RecShaped (cfg : ErasureConfig) (decls : List ConstantInfo) (x : Expr) : Prop :=
  ConstsIn (fun c => ∀ rv, findDecl decls c = some (.recInfo rv) → RecInFragment cfg decls rv) x

/-- The fragment test reads the compiled pre-definitions of the closure as it reads values. Port
of `ML-V Spec.lean:1183`. -/
def PreRead (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, ∀ pre, preDef? view cfg ci = some pre →
    ConstsIn (fun c => (findDecl decls c).isSome) pre ∧
    (HasNatLit pre → (findDecl decls ``Nat).isSome) ∧ PlainExpr cfg pre ∧ RecShaped cfg decls pre

/-- A declaration of the closure is inside the first-phase fragment; a definition, theorem or
opaque is alone in its block (`all = [name]`, which con-leche does not read and Metalean's
environment gave). Port of `ML-V Spec.lean:1198`. -/
def PhaseIDecl (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) :
    ConstantInfo → Prop
  | .quotInfo _ => True
  | .recInfo r => (∃ T iv, r.name = mkRecName T ∧
      casesOnOf? decls (.str T "casesOn") = some iv ∧
      (findDecl decls (.str T "casesOn")).isSome) ∨
    (∃ T iv, r.name = mkRecName T ∧ findDecl decls T = some (.inductInfo iv) ∧
      iv.ctors.length = 1) ∨
    RecInFragment cfg decls r
  | .defnInfo d => d.safety = .safe ∧ d.all = [d.name] ∧
      (view.find? (Compiler.mkUnsafeRecName d.name) = none ∨
      (isStructuralRecursive (.defnInfo d) &&
        (cfg.structural == .kernel || (preDef? view cfg (.defnInfo d)).isSome)) = true) ∧
      view.implementedBy? d.name = none
  | .opaqueInfo o => o.isUnsafe = false ∧ o.all = [o.name] ∧
      view.find? (Compiler.mkUnsafeRecName o.name) = none ∧ view.implementedBy? o.name = none
  | .axiomInfo a => a.isUnsafe = false ∧ view.implementedBy? a.name = none
  | .thmInfo t => t.all = [t.name]
  | .inductInfo iv => iv.isUnsafe = false ∧ iv.numNested = 0 ∧
      (∃ n u, arityShape iv.type = some (n, u) ∧ (u = .zero ∨ u.isNeverZero = true ∨
        (mayBeNonZero iv.levelParams u = true ∧ ¬ Eliminated decls iv))) ∧
      ((casesOnOf? decls (.str iv.name "casesOn")).isSome →
        ∀ cn ∈ iv.ctors, ∀ cv, findDecl decls cn = some (.ctorInfo cv) →
          (indexFields cv.numParams cv.type).all (·.isNone) = true)
  | .ctorInfo cv => cv.isUnsafe = false ∧ (cfg.1 = .preferAxiom → view.isExtern cv.name = false)

/-- Declarations the λ□ environment holds as constants. Port of `ML-V Spec.lean:1228`. -/
def EmitsConst : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- No two λ□ global declarations of the closure share a kername. Port of `ML-V Spec.lean:1237`. -/
def BlockNamesInj (decls : List ConstantInfo) : Prop :=
  ∀ iv₁ iv₂, (∃ ci ∈ decls, ci = .inductInfo iv₁) → (∃ ci ∈ decls, ci = .inductInfo iv₂) →
    (mutualBlockKername iv₁.all = mutualBlockKername iv₂.all → iv₁.all = iv₂.all) ∧
    ∀ ci ∈ decls, EmitsConst ci = true → toKername ci.name ≠ mutualBlockKername iv₁.all

/-- The declared type of every inductive of `decls` is syntactically an arity. Port of
`ML-V Spec.lean:1248`; reference: `ind_arity_eq` (`MR common/theories/EnvironmentTyping.v:1651`). -/
def ArityTypes (decls : List ConstantInfo) : Prop :=
  ∀ iv, (∃ ci ∈ decls, ci = .inductInfo iv) → (arityShape iv.type).isSome

/-! ## 7. The erasure relation -/

/-- The λ□ block name of an inductive. Port of `ML-V Spec.lean:1255`. -/
def blockKername (iv : InductiveVal) : Kername :=
  mutualBlockKername iv.all

/-- The λ□ inductive of the Lean inductive `T`. Port of `ML-V Spec.lean:1259`. -/
def IndIdOf (σ : EvalEnv) (T : Name) : Option InductiveId :=
  match findDecl σ.decls T with
  | some (.inductInfo iv) => (iv.all.idxOf? T).map fun j => ⟨blockKername iv, j⟩
  | _ => none

/-- A spine whose head is a constructor, a recognized `casesOn`, an erased quotient constant or a
recursor. Port of `ML-V Spec.lean:1266`. -/
def SpecialSpine (σ : EvalEnv) (e : Expr) : Prop :=
  ∃ c us, e.getAppFn = .const c us ∧
    ((∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ (σ.casesOn? c).isSome ∨
      (∃ qv, findDecl σ.decls c = some (.quotInfo qv) ∧ (quotEvalArity qv.kind).isSome) ∨
      ∃ rv, findDecl σ.decls c = some (.recInfo rv))

/-- The number of fields of a constructor of `σ`. Port of `ML-V Spec.lean:1273`. -/
def ctorFields (σ : EvalEnv) (c : Name) : Option Nat :=
  match findDecl σ.decls c with
  | some (.ctorInfo cv) => some cv.numFields
  | _ => none

/-- Every constructor of `decls` is listed by its inductive at its index `cidx`, with the
inductive's parameter count, as Lean's kernel generates the records. con-leche's frontend checks
these fields (`CL ConLeche/Frontend/ExportC.lean:241 validateIndF`), and so does `DeclsOf?`
(`blockShapeOK`, `declOf?`; DV-3). Reference: `declared_constructor`
(`MR common/theories/EnvironmentTyping.v:36`). -/
def CtorsListed (decls : List ConstantInfo) : Prop :=
  ∀ c cv, findDecl decls c = some (.ctorInfo cv) → ∃ iv,
    findDecl decls cv.induct = some (.inductInfo iv) ∧ iv.ctors[cv.cidx]? = some c ∧
    iv.numParams = cv.numParams

/-- The inductive `Nat` of `σ`, if there is one, has Lean's shape: no parameters, not declared in
`Prop`, and the constructors `zero`, without a field, and `succ`, with one, in that order: the
λ□ constructors `0` and `1` of the Peano numerals (`Erases.litZero`, `Erases.litSucc`) are its.
con-leche checks a program's `Nat` against this shape (`CL ConLeche/Kernel/Basis/Nat.lean:68
natBasis`). Reference: none (λ□ has no Nat literals; DV-30). -/
def NatShaped (σ : EvalEnv) : Prop :=
  ∀ iv, findDecl σ.decls ``Nat = some (.inductInfo iv) → iv.numParams = 0 ∧
    σ.propInd ``Nat = false ∧
    ∃ z s, iv.ctors = [z, s] ∧ ctorFields σ z = some 0 ∧ ctorFields σ s = some 1

/-- Lean's constructors ``Nat.zero`` and ``Nat.succ``, if `σ` has them, are the constructors `0`
and `1` of ``Nat``: the constructor forms of the Nat literals (`natLitCtor`) are the constructors of
the λ□ numerals (`Erases.litZero`, `Erases.litSucc`). con-leche checks a program's `Nat` block
against Lean's (`CL ConLeche/Kernel/Basis/Nat.lean:68 natBasis`). Reference: none (λ□ has no Nat
literals; DV-30). -/
def NatCtors (σ : EvalEnv) : Prop :=
  (∀ cv, findDecl σ.decls ``Nat.zero = some (.ctorInfo cv) → cv.induct = ``Nat ∧ cv.cidx = 0) ∧
    ∀ cv, findDecl σ.decls ``Nat.succ = some (.ctorInfo cv) → cv.induct = ``Nat ∧ cv.cidx = 1

/-- Every recursor of `decls` of one inductive without indices has the shape Lean's kernel gives
it: its inductive's parameter count, and one motive, whose type binds the major premise only (the
motives `recShape` reads off the recursor's type). The fixpoint `recFix` is then one λ over the
major premise, and its `case` has the inductive's parameter count. `DeclsOf?` checks the counts
(`blockShapeOK`); con-leche compares a recursor's type with the generated one up to definitional
equality only (`CL ConLeche/Kernel/Inductives/GenRec.lean:386 classRecTyCheck`), so the syntactic
shape of the motive is a condition of its own. Reference: the recursor as Lean's kernel builds it
(`mk_rec_infos`, `declare_recursors` in `src/kernel/inductive.cpp`). -/
def RecsShaped (decls : List ConstantInfo) : Prop :=
  ∀ c rv T iv, findDecl decls c = some (.recInfo rv) → rv.all = [T] →
    findDecl decls T = some (.inductInfo iv) → rv.numIndices = 0 →
    rv.numParams = iv.numParams ∧ ∀ ns motives minors,
      recShape rv.numParams rv.numMotives rv.type ns = some (motives, minors) → ∃ x, motives = [[x]]

/-- The members of a recursor's block as `visitRec` builds them for `recFix`. Port of
`ML-V Spec.lean:1324`. -/
def recMembers (σ : EvalEnv) (minors : List RecMinor) :
    Nat → List InductiveVal → List (List Name) → Option (List RecMember)
  | gi, iv :: ivs, xs :: xss => do
    let indid ← IndIdOf σ iv.name
    let masks ← iv.ctors.mapM fun c => (ctorFields σ c).map fun k =>
      (Array.replicate k .keep : ConstructorArgMask)
    let ms := (minors.drop gi).take iv.ctors.length
    let rest ← recMembers σ minors (gi + iv.ctors.length) ivs xss
    pure (⟨iv.name, xs, indid, (List.range ms.length).map fun c =>
      (gi + c, ms.getD c default, masks.getD c #[])⟩ :: rest)
  | _, _, _ => pure []

/-- The λ□ fixpoint that `visitRec` builds for the recursor `rv` (`recFix`,
`LeanToLambdaBox/Erasure.lean:817`). Port of `ML-V Spec.lean:1345` without the typing conjuncts:
the `direct` form (alternatives applied to `□`) is admitted only for blocks whose one-constructor
members are declared in `Prop` or have no fields (λ□ `iota` needs a non-propositional block, so a
constructor value of a `Prop` inductive is never related, `Erases.ctor`). Reference: none (DV-30). -/
def RecFixOf (σ : EvalEnv) (rv : RecursorVal) (minors : List RecMinor) (F : LBTerm) : Prop :=
  ∃ ivs cvs motives members T ivT j direct, σ.recBlock? rv = some (ivs, cvs) ∧
    recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) = some (motives, minors) ∧
    minors.length = rv.numMinors ∧ recMembers σ minors 0 ivs motives = some members ∧
    rv.getMajorInduct = T ∧ findDecl σ.decls T = some (.inductInfo ivT) ∧
    rv.all.idxOf? T = some j ∧
    (direct = true → ∀ iv ∈ ivs, iv.ctors.length = 1 →
      σ.propInd iv.name = true ∨ ∀ cn ∈ iv.ctors, ctorFields σ cn = some 0) ∧
    F = recFix rv.numMinors rv.numParams direct members j ∧
    closedn rv.numMinors F = true ∧ ∀ x, hasFVar x F = false

/-- The let-bindings of `visitRec`'s output. Port of `ML-V Spec.lean:1360`. -/
def recLets : Nat → List (LBTerm × RecMinor) → LBTerm → LBTerm
  | _, [], b => b
  | d, (m, mi) :: ms, b => .letIn (binderNameOf mi.name) (lbLift d 0 m) (recLets (d + 1) ms b)

/-- What `Erases` asks of a mark it relates to `□` (or of the discriminant of a reduced
`casesOn`), given the binders `Γ` around it (innermost first): nothing (`noCert`, the relation of
the simulation) or con-leche's certificate (`CLCert env`, the relation of the emitted program).
Reference: none (DV-32). -/
abbrev BoxCert := List CtxBinder → Expr → Prop

/-- No certificate is asked of a mark. Reference: none (DV-32). -/
def noCert : BoxCert := fun _ _ => True

mutual
/-- The erasure relation on marked terms (port of `ML-V Spec.lean:1378`): no typing premise; `Γ`
lists the binders around the position (innermost first; a `let` with its value), which only the
`□` rules read; `□` exactly for `erase`-marked terms, each asked of `cert` in its context (`box`); an
`eta`-marked λ is a λ□ λ (`etaLam`); the reduced `casesOn` has a `reduced`-marked discriminant,
asked of `cert` (`casesReduced`); a constructor of a `Prop` inductive has no rule (the λ□ block is
propositional, `ErasesInd`); pre-definitions, η and metadata have no rule of their own (none is
used, and η and metadata are in the marks; DV-32). Reference: `MR E/Extract.v:88 erases`; MC §7.3,
Fig. 18. -/
inductive Erases (cert : BoxCert) (σ : EvalEnv) : List CtxBinder → Expr → LBTerm → Prop
  /-- `erases_tRel` (`MR E/Extract.v:89`). -/
  | bvar : Erases cert σ Γ (.bvar i) (.bvar i)
  /-- `erases_tVar` (`:90`), the traversal's free variables (DV-13). -/
  | fvar : Erases cert σ Γ (.fvar x) (.fvar x)
  /-- `erases_tLambda` (`:93`). -/
  | lam : Erases cert σ ((A, none) :: Γ) b b' →
      Erases cert σ Γ (.lam x A b bi) (.lambda (binderNameOf x) b')
  /-- An `eta`-marked λ (`mkLambda`, `LeanToLambdaBox/Erasure.lean:558`). -/
  | etaLam : Erases cert σ ((A, none) :: Γ) b b' →
      Erases cert σ Γ (markEta (.lam x A b bi)) (.lambda (binderNameOf x) b')
  /-- `erases_tLetIn` (`:96`). -/
  | letE : Erases cert σ Γ v v' → Erases cert σ ((T, some v) :: Γ) b b' →
      Erases cert σ Γ (.letE x T v b nd) (.letIn (binderNameOf x) v' b')
  /-- `erases_tApp` (`:101`), heads other than constructors and `casesOn`. -/
  | app : ¬ SpecialSpine σ f → Erases cert σ Γ f f' → Erases cert σ Γ a a' →
      Erases cert σ Γ (.app f a) (.app f' a')
  /-- `erases_tConst` (`:104`). -/
  | const : σ.isAtom c = false → specialArity σ c = none →
      (∀ rv, findDecl σ.decls c ≠ some (.recInfo rv)) →
      Erases cert σ Γ (.const c us) (.const (toKername c))
  /-- `erases_tConstruct` (`:106`) under applications, parameters kept (DV-23), of an inductive
  not declared in `Prop`. -/
  | ctor {as : List Expr} {as' : List LBTerm} :
      findDecl σ.decls c = some (.ctorInfo cv) → σ.propInd cv.induct = false →
      IndIdOf σ cv.induct = some iid →
      cv.numParams + cv.numFields ≤ as.length → as.length = as'.length →
      (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → Erases cert σ Γ a a') →
      Erases cert σ Γ (mkAppN (.const c us) as.toArray) (mkApps (.construct iid cv.cidx []) as')
  /-- `erases_tCase` (`:109`): parameters, motive and indices dropped; alternatives under their
  fields' binders. -/
  | cases {pre alts extra : List Expr} {brs : List (List BinderName × LBTerm)} {extra' : List LBTerm} :
      σ.casesOn? c = some iv → IndIdOf σ iv.name = some iid →
      pre.length = casesMajor iv → alts.length = iv.ctors.length →
      Erases cert σ Γ maj maj' →
      brs.length = alts.length → (∀ (i : Nat) cn, iv.ctors[i]? = some cn → (ctorFields σ cn).isSome) →
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt → brs[i]? = some br →
        ctorFields σ cn = some k → ErasesAlt cert σ Γ k alt br) →
      extra.length = extra'.length →
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases cert σ Γ a a') →
      Erases cert σ Γ (mkAppN (.const c us) (pre ++ [maj] ++ alts ++ extra).toArray)
        (mkApps (.case (iid, iv.numParams) maj' brs) extra')
  /-- The reduced form of a `casesOn` (`visitCases`, `LeanToLambdaBox/Erasure.lean:1130`): the
  erased alternative applied to `□` for each field and to the extra arguments; the
  `reduced`-marked discriminant is dropped (`eval_iota_sing`, `MR E/EWcbvEval.v:162`, at erasure
  time; DV-25), and asked of `cert` in its context: with `CLCert env`, con-leche types it as a
  proof (its type is an inductive application, not a type-former type) of a proposition whose
  `casesOn` eliminates into every sort, so its fields are proofs (con-leche's elimination check). -/
  | casesReduced {pre extra : List Expr} {extra' : List LBTerm} : cert Γ d →
      σ.casesOn? c = some iv → iv.ctors = [cn] → findDecl σ.decls cn = some (.ctorInfo cv) →
      (indexFields cv.numParams cv.type).all (·.isNone) = true →
      pre.length = casesMajor iv → Erases cert σ Γ alt alt' →
      extra.length = extra'.length →
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases cert σ Γ a a') →
      Erases cert σ Γ (mkAppN (.const c us) (pre ++ [markReduced d] ++ [alt] ++ extra).toArray)
        (mkApps alt' (List.replicate cv.numFields .box ++ extra'))
  /-- `erases_tProj` (`:118`), on a structure declared in `Prop` or whose declared sort is never
  zero. -/
  | proj : IndIdOf σ S = some iid → findDecl σ.decls S = some (.inductInfo iv) →
      (σ.propInd S = true ∨ ∃ n u, arityShape iv.type = some (n, u) ∧ u.isNeverZero = true) →
      Erases cert σ Γ e e' → Erases cert σ Γ (.proj S i e) (.proj ⟨iid, iv.numParams, i⟩ e')
  /-- Nat literals under `nat := .peano` (`visitLiteral`). -/
  | litZero : IndIdOf σ ``Nat = some iid → Erases cert σ Γ (.lit (.natVal 0)) (.construct iid 0 [])
  | litSucc : IndIdOf σ ``Nat = some iid → Erases cert σ Γ (.lit (.natVal k)) t →
      Erases cert σ Γ (.lit (.natVal (k + 1))) (.app (.construct iid 1 []) t)
  /-- `Quot.mk α r a` (DV-29). -/
  | quotMk {extra : List Expr} {extra' : List LBTerm} :
      findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor → Erases cert σ Γ a a' →
      extra.length = extra'.length →
      (∀ (i : Nat) x x', extra[i]? = some x → extra'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ (mkAppN (.const c us) ([α, r, a] ++ extra).toArray) (mkApps a' extra')
  /-- `Quot.lift α r β f h q` (DV-29). -/
  | quotLift {extra : List Expr} {extra' : List LBTerm} :
      findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .lift → Erases cert σ Γ f f' →
      Erases cert σ Γ q q' → extra.length = extra'.length →
      (∀ (i : Nat) x x', extra[i]? = some x → extra'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ (mkAppN (.const c us) ([α, r, β, f, h, q] ++ extra).toArray)
        (mkApps f' (q' :: extra'))
  /-- A recursor application as `visitRec` erases it (DV-30). -/
  | recLet {ps ms mins is extra : List Expr} {mins' is' extra' : List LBTerm} :
      findDecl σ.decls c = some (.recInfo rv) → RecFixOf σ rv minors F →
      ps.length = rv.numParams → ms.length = rv.numMotives → mins.length = rv.numMinors →
      is.length = rv.numIndices → mins.length = mins'.length →
      (∀ (i : Nat) x x', mins[i]? = some x → mins'[i]? = some x' → Erases cert σ Γ x x') →
      is.length = is'.length →
      (∀ (i : Nat) x x', is[i]? = some x → is'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ maj maj' → extra.length = extra'.length →
      (∀ (i : Nat) x x', extra[i]? = some x → extra'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ (mkAppN (.const c us) (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).toArray)
        (mkApps (recLets 0 (mins'.zip minors)
          (mkApps F ((is' ++ [maj']).map (lbLift rv.numMinors 0)))) extra')
  /-- A recursor application with closed λ□ values substituted for the minors (DV-30). -/
  | recFix {ps ms mins is extra : List Expr} {ws is' extra' : List LBTerm} :
      findDecl σ.decls c = some (.recInfo rv) → RecFixOf σ rv minors F →
      ps.length = rv.numParams → ms.length = rv.numMotives → mins.length = rv.numMinors →
      is.length = rv.numIndices → mins.length = ws.length →
      (∀ (i : Nat) x x', mins[i]? = some x → ws[i]? = some x' → Erases cert σ Γ x x') →
      (∀ w ∈ ws, closedn 0 w = true ∧ (∀ x, hasFVar x w = false) ∧ LBFixed w) →
      is.length = is'.length →
      (∀ (i : Nat) x x', is[i]? = some x → is'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ maj maj' → extra.length = extra'.length →
      (∀ (i : Nat) x x', extra[i]? = some x → extra'[i]? = some x' → Erases cert σ Γ x x') →
      Erases cert σ Γ (mkAppN (.const c us) (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).toArray)
        (mkApps (substl ws.reverse F) (is' ++ [maj'] ++ extra'))
  /-- `erases_box` (`:140`), on the terms the traversal erases, each asked of `cert` in the
  context of its enclosing binders. -/
  | box : cert Γ s → Erases cert σ Γ (markErase s) .box

/-- A `casesOn` alternative under its `k` field binders, peeled (`lam`) or η-introduced (`etaLam`,
an `eta`-marked λ of `MarkAlt.intro`), each binder's domain added to the context. Port of
`ML-V Spec.lean:1538` without typing premises. Reference: the branches of `MR E/Extract.v:109
erases_tCase`. -/
inductive ErasesAlt (cert : BoxCert) (σ : EvalEnv) :
    List CtxBinder → Nat → Expr → List BinderName × LBTerm → Prop
  | done : Erases cert σ Γ e t → ErasesAlt cert σ Γ 0 e ([], t)
  | lam : ErasesAlt cert σ ((A, none) :: Γ) k b (ns, t) →
      ErasesAlt cert σ Γ (k + 1) (.lam x A b bi) (binderNameOf x :: ns, t)
  | etaLam : ErasesAlt cert σ ((A, none) :: Γ) k b (ns, t) →
      ErasesAlt cert σ Γ (k + 1) (markEta (.lam x A b bi)) (binderNameOf x :: ns, t)
end

/-- The λ□ environment holds the erasure of `T`'s block, `propositional` iff the type is declared
in `Prop` (`EvalEnv.propInd`). Port of `ML-V Spec.lean:1555` with `propInd` for the inductives
of `Prop`. Reference: `MR E/Extract.v:278 erases_mutual_inductive_body`. -/
def ErasesInd (σ : EvalEnv) (lenv : GlobalDeclarations) (T : Name) : Prop :=
  ∃ iv, findDecl σ.decls T = some (.inductInfo iv) ∧
    ∀ j n, iv.all[j]? = some n → ∃ iv' mib ob, findDecl σ.decls n = some (.inductInfo iv') ∧
      lookupInd lenv ⟨blockKername iv, j⟩ = some (mib, ob) ∧ mib.npars = iv.numParams ∧
      ob.ctors.length = iv'.ctors.length ∧
      (∀ (k : Nat) cn, iv'.ctors[k]? = some cn → ∃ (cv : ConstructorVal) (cb : ConstructorBody),
        findDecl σ.decls cn = some (.ctorInfo cv) ∧ ob.ctors[k]? = some cb ∧ cb.nargs = cv.numFields) ∧
      (ob.propositional = true ↔ σ.propInd n = true)

/-- A constant's λ□ body erases the marking of its Lean value (`MarkOf` at its own levels, as
`visitMutual`, `LeanToLambdaBox/Erasure.lean:1272`, erases it): the value has a marking, and the
body erases every marking of it; no body for declarations without value and for remapped externs
(DV-12). Port of `ML-V Spec.lean:1573`; pre-definitions have no case (none is used, DV-35).
Reference: `MR E/Extract.v:264 erases_constant_body`. -/
def ErasesDecl (cert : BoxCert) (σ : EvalEnv) (ci : ConstantInfo) (cb : ConstantBody) : Prop :=
  match ci.value? (allowOpaque := true) with
  | none => cb.cst_body = none
  | some v => (σ.axiomatized ci = true ∧ cb.cst_body = none) ∨
    (σ.axiomatized ci = false ∧ (∃ vM, MarkOf σ.decls σ.cfg [] v vM) ∧ ∃ b', cb.cst_body = some b' ∧
      ∀ vM, MarkOf σ.decls σ.cfg [] v vM → Erases cert σ [] vM b')

/-- The λ□ environment contains erasures of the erased term's dependencies. Port of
`ML-V Spec.lean:1592`; reference: `MR E/Extract.v:306 erases_deps`. -/
inductive ErasesDeps (cert : BoxCert) (σ : EvalEnv) (lenv : GlobalDeclarations) : LBTerm → Prop
  | box : ErasesDeps cert σ lenv .box
  | bvar : ErasesDeps cert σ lenv (.bvar i)
  | fvar : ErasesDeps cert σ lenv (.fvar x)
  | lambda : ErasesDeps cert σ lenv b → ErasesDeps cert σ lenv (.lambda na b)
  | letIn : ErasesDeps cert σ lenv v → ErasesDeps cert σ lenv b → ErasesDeps cert σ lenv (.letIn na v b)
  | app : ErasesDeps cert σ lenv f → ErasesDeps cert σ lenv a → ErasesDeps cert σ lenv (.app f a)
  /-- `erases_deps_tConst` (`:324`), indexed by the source constant (DV-14). -/
  | const : findDecl σ.decls c = some ci → lookupConst lenv (toKername c) = some cb →
      ErasesDecl cert σ ci cb → (∀ b, cb.cst_body = some b → ErasesDeps cert σ lenv b) →
      ErasesDeps cert σ lenv (.const (toKername c))
  /-- `erases_deps_tConstruct` (`:330`). -/
  | construct : IndIdOf σ T = some iid → ErasesInd σ lenv T →
      (∀ a ∈ args, ErasesDeps cert σ lenv a) → ErasesDeps cert σ lenv (.construct iid c args)
  /-- `erases_deps_tCase` (`:336`). -/
  | case : IndIdOf σ T = some iid → ErasesInd σ lenv T → ErasesDeps cert σ lenv d →
      (∀ br ∈ brs, ErasesDeps cert σ lenv br.2) → ErasesDeps cert σ lenv (.case (iid, np) d brs)
  /-- `erases_deps_tProj` (`:345`). -/
  | proj : IndIdOf σ T = some p.indType → ErasesInd σ lenv T → ErasesDeps cert σ lenv d →
      ErasesDeps cert σ lenv (.proj p d)
  /-- `erases_deps_tFix` (`:352`). -/
  | fix : (∀ d ∈ defs, ErasesDeps cert σ lenv d.body) → ErasesDeps cert σ lenv (.fix defs i)

/-- Every `erase` mark of `ê` is certified by con-leche (`CLCert`), and the discriminant of every
`reduced` mark is certified as a proof (`CLCertProof`), in the context of its enclosing binders:
`Γ` lists the binders around the position, innermost first, extended at λ, `let` (with its value)
and `eta`-marked λ bodies, the positions at which `Erases` extends its context. Reference: none
(DV-32). -/
def MarksCert (env : ConLeche.Env) : List CtxBinder → Expr → Prop
  | Γ, .mdata d e => match d with
    | ⟨[(.anonymous, .ofNat 0)]⟩ => CLCert env Γ e
    | ⟨[(.anonymous, .ofNat 2)]⟩ => CLCertProof env Γ e
    | _ => MarksCert env Γ e
  | Γ, .app f a => MarksCert env Γ f ∧ MarksCert env Γ a
  | Γ, .lam _ t b _ => MarksCert env ((t, none) :: Γ) b
  | Γ, .letE _ t v b _ => MarksCert env Γ v ∧ MarksCert env ((t, some v) :: Γ) b
  | Γ, .proj _ _ e => MarksCert env Γ e
  | _, _ => True

/-- con-leche certifies the marks of the marked input `ê` over the closure `decls`: it types `ê`
as a whole (`CLTypedAt`; marks are transparent, so every η-expansion is typed, and the domain of
each `eta`-marked binder is checked against the argument position it fills), and every mark of `ê`
in the context of its enclosing binders (`MarksCert`; the discriminant of a `reduced` mark as a
proof); the same of a marking of the value of every constant of `decls` that has one, whether or
not the emitted λ□ environment holds a body for it (DV-37). With the marking fixed (`MarkOf` is a
function of its input, `markOf_det_statement`), each conjunct is a finite list of con-leche runs at
`checkFuel`. Reference: none (DV-32). -/
def ProgCert (env : ConLeche.Env) (decls : List ConstantInfo) (cfg : ErasureConfig) (ê : Expr) :
    Prop :=
  CLTypedAt env ê ∧ MarksCert env [] ê ∧ ∀ ci ∈ decls, ∀ v,
    ci.value? (allowOpaque := true) = some v →
    ∃ vM, MarkOf decls cfg [] v vM ∧ CLTypedAt env vM ∧ MarksCert env [] vM

/-- Every value of a constant of the closure `decls` has a marking in the empty context: the
premise of `erasePure_erases_statement` that gives `ErasesDecl`'s `∃ vM` for each value the
traversal erases; the final theorem has it from `ProgCert`'s third conjunct. Reference: none
(DV-32). -/
def ValuesMarkedOf (decls : List ConstantInfo) (cfg : ErasureConfig) : Prop :=
  ∀ ci ∈ decls, ∀ v, ci.value? (allowOpaque := true) = some v → ∃ vM, MarkOf decls cfg [] v vM

/-! ## 8. The meaning of the source value; first-order values -/

/-- The source value means what the input means, in every con-leche model of `env`: `unmark v`
has a con-leche form, and for every `V : Type w` with `[SetTheory V]`, every model
`m : EnvModelM V env` (`CL ConLeche/Model/Env/EnvModelM.lean:244`), level valuation `φ` and
variable assignment `ρ`, if the con-leche form of `e` denotes `X` under `Model.ofEnvModelM m`
(`CL ConLeche/Model/Denotes.lean:330`) and `X` is not the proof point
(`CL ConLeche/SetTheory/Derive/Pt.lean:69 pt`), the con-leche form of `unmark v` denotes `X` too.
Stated over con-leche's public reading `Denotes` (`CL ConLeche/Denotes.lean:123`). The `SetTheory`
instance is a hypothesis, as in `CL ConLeche/MainTheorem.lean:102 model_exists`; the `X ≠ pt`
condition is con-leche's own (its whnf and defeq claims say nothing about proofs,
`CL ConLeche/Model/Claims.lean:52`). It is not type preservation: con-leche's model gives
`Nat.zero`, the type `Empty` and `PUnit.unit.{1}` one denotation (`∅`,
`CL ConLeche/SetModel/Value.lean:625 bval`), so a value of another type with the input's denotation
satisfies it; the value's type is pinned by `SrcEval`. Reference: none (DV-34); MetaRocq's
counterpart is subject reduction of the evaluation (`MR P/PCUICSR.v`). -/
def Sound.{w} (env : ConLeche.Env) (e v : Expr) : Prop :=
  (∃ c', toCL? (unmark v) = some c') ∧
  ∀ (V : Type w) [ConLeche.SetTheory V] (m : ConLeche.Model.EnvModelM V env)
    (φ : ConLeche.LevelParam → Nat) (ρ : ConLeche.BVarIdx → V) (X : V) (c c' : ConLeche.Expr),
    toCL? e = some c → toCL? (unmark v) = some c' →
    ConLeche.Denotes (ConLeche.Model.Model.ofEnvModelM m).cval env φ ρ c X →
    X ≠ ConLeche.SetTheory.pt →
    ConLeche.Denotes (ConLeche.Model.Model.ofEnvModelM m).cval env φ ρ c' X

/-- A con-leche type whose members are never the proof point in every model: a sort (its members
are types, `CL ConLeche/SetTheory/Derive/Univ.lean:45 ne_pt_of_mem_univ`). An inductive's carrier is
not one: `EnvModelM` does not state that it excludes the proof point (DV-34). Reference: none
(DV-34). -/
def CLStrictType (W : ConLeche.Expr) : Prop :=
  ∃ u, W = .sort u

/-- A first-order value of `σ`: a tree of saturated constructor applications whose leaves are
frozen terms or Nat literals. Port of `ML-V FirstOrder.lean:34`, whose proof and atom leaves are
frozen leaves here (a constructor node is unmarked, so it erases to a λ□ constructor). Reference:
`firstorder_value` (`MR P/PCUICFirstorder.v:115`); DV-27. -/
inductive FirstOrderValue (σ : EvalEnv) : Expr → Prop
  | ctor {c : Name} {us : List Level} {as : List Expr} {cv : ConstructorVal} :
      findDecl σ.decls c = some (.ctorInfo cv) → as.length = cv.numParams + cv.numFields →
      (∀ a ∈ as, FirstOrderValue σ a) → FirstOrderValue σ (mkAppN (.const c us) as.toArray)
  | frozen {s : Expr} : FirstOrderValue σ (markErase s)
  | lit {k : Nat} : FirstOrderValue σ (.lit (.natVal k))

/-- The Peano numeral `k` of the λ□ inductive `iid` (`Nat`), as `Erases.litZero`/`litSucc` relate
a literal. Reference: none (DV-27). -/
def peanoLB (iid : InductiveId) : Nat → LBTerm
  | 0 => .construct iid 0 []
  | k + 1 => .app (.construct iid 1 []) (peanoLB iid k)

/-- The structural erasure of a value, with the erasures `acc` of the arguments already peeled off
its spine: a constructor of an inductive not declared in `Prop` is the λ□ constructor of its block
applied to the erased arguments; a Nat literal is its Peano numeral; everything else (frozen leaves
included) is `□`. Port of `ML-V FirstOrder.lean:53` with the literal case. Reference:
`compile_value_erase` (`MR E/ErasureFunctionProperties.v:2860`). -/
def foErase (σ : EvalEnv) : Expr → List LBTerm → LBTerm
  | .app f a, acc => foErase σ f (foErase σ a [] :: acc)
  | .lit (.natVal k), acc => match IndIdOf σ ``Nat with
    | some iid => mkApps (peanoLB iid k) acc
    | none => .box
  | .const c _, acc =>
    match findDecl σ.decls c with
    | some (.ctorInfo cv) =>
      if σ.propInd cv.induct then .box
      else match IndIdOf σ cv.induct with
        | some iid => mkApps (.construct iid cv.cidx []) acc
        | none => .box
    | _ => .box
  | _, _ => .box

/-- `s` is a frozen leaf of the application tree `v`: a `□` of `foErase σ v`. Reference: none
(DV-27). -/
inductive FrozenLeaf : Expr → Expr → Prop
  | here : FrozenLeaf (markErase s) s
  | appFn : FrozenLeaf f s → FrozenLeaf (.app f a) s
  | appArg : FrozenLeaf a s → FrozenLeaf (.app f a) s

end EraseProof
