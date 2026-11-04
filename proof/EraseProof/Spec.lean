import LeanToLambdaBox.Erasure.Entry
import EraseProof.Target
import Metalean.Typing.Defs
import Metalean.Typing.TypeEq
import Metalean.Syntax.Structure
import Metalean.Frontend.Translate

/-!
# The definitions of the statements

The definitions the statements of `EraseProof/Statements.lean` are about: the bridge between Lean
terms and declarations and Metalean terms and environments (`MBinding`, `Binds`, `TrLevel`,
`MLCtx`, `SatTr`, `TrM`, `ProgEnv`), the source semantics (`EvalEnv`, atoms, `SrcEval`),
erasability (`IsArity`, `IsErasable`, `ErasableS`), the closure predicates (`ConstsIn`,
`KernameInj`, `SubEnv`, `evalEnvOf`, `ViewAgrees`), the sufficient condition for the fragment
(`ReadClosed`, `PhaseIDecl`, `PlainExpr`, `RecFree`, `BlockNamesInj`), and the erasure relation
(`Erases`, `ErasesAlt`, `ErasesInd`, `ErasesDecl`, `ErasesDeps`). λ□ evaluation is
`EraseProof/Target.lean`.

The η-terms of the saturating rules are the translator's own total term builders
`Metalean.Frontend.{indTerm, ctorTerm, recrTerm, wrapCase, quotTerm}`, which are trusted
(`doc/DIVERGENCES.md`, trust base); check C6 exempts exactly what they reach.

Citations: `ML <file>:<line>` is a file of Metalean (`Metalean/`, commit `9407ba4`); `MR <file>`
is a file of MetaRocq (commit `4b201296`), `E/`, `P/`, `S/` standing for `erasure/theories/`,
`pcuic/theories/`, `safechecker/theories/`; `L4 <file>` is a file of `proof/` in the lean4lean
experiment of this repository (commit `ca56b85`), which this development ports; MC is Sozeau et al.,
"Correct and Complete Type Checking and Certified Erasure for Coq, in Coq" (J. ACM 2025).
-/

open Lean Erasure
open Metalean (Defeq TypeEq IsType CtxWF)

namespace EraseProof

/-! ## 1. Names -/

/-- What a Lean name denotes in a Metalean environment: `Frontend.Binding`
(`ML Frontend/Table.lean:17`) with heads instead of positions. `order` is the constructor's
Metalean field order (`metaOrderOf`, `ML Frontend/Inductive.lean:135`), `orders` those of the
block's constructors. Reference: none (Lean's names vs Metalean's heads, DV-1). -/
inductive MBinding (ζ : Metalean.Sigs) where
  | const {kind : Metalean.ConstKind} {nl : Nat} (η : Metalean.Head ζ (.const kind nl))
  | ind {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
  | ctor {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (c : Fin (ι.nctors s)) (order : List Nat)
  | recr {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (orders : List (List (List Nat)))
  | quot (η : Metalean.Head ζ .quot) (kind : Metalean.Export.QuotKind)

/-- The name table: `Frontend.Table` (`ML Frontend/Table.lean:26`) as a function. -/
abbrev Binds (ζ : Metalean.Sigs) := Name → Option (MBinding ζ)

/-- Bindings that need saturation (`translateSpecial`, `ML Frontend/Translate.lean:234`). -/
def MBinding.isSpecial {ζ : Metalean.Sigs} : MBinding ζ → Bool
  | .const _ => false
  | _ => true

/-- Weakening along one new entry (heads move by `Head.there`). -/
def MBinding.wk {ζ : Metalean.Sigs} {sig : Metalean.Sig} : MBinding ζ → MBinding (ζ.snoc sig)
  | .const η => .const η.there
  | .ind η s => .ind η.there s
  | .ctor η s c o => .ctor η.there s c o
  | .recr η s os => .recr η.there s os
  | .quot η k => .quot η.there k

/-- The table after one new entry, before its own names are bound. -/
def Binds.wk {ζ : Metalean.Sigs} {sig : Metalean.Sig} (B : Binds ζ) : Binds (ζ.snoc sig) :=
  fun n => (B n).map MBinding.wk

/-- Bind one name. -/
def Binds.set {ζ : Metalean.Sigs} (B : Binds ζ) (n : Name) (b : MBinding ζ) : Binds ζ :=
  fun m => if m = n then some b else B m

/-! ## 2. Levels -/

/-- `translateLevel` (`ML Frontend/Translate.lean:42`) on Lean levels; level metavariables do not
translate. -/
def TrLevel (lps : List Name) : Lean.Level → Option (Metalean.Level lps.length)
  | .zero => some .zero
  | .succ l => (TrLevel lps l).map .succ
  | .max a b => do pure (.max (← TrLevel lps a) (← TrLevel lps b))
  | .imax a b => do pure (.imax (← TrLevel lps a) (← TrLevel lps b))
  | .param n => (lps.finIdxOf? n).map .param
  | .mvar _ => none

/-- `translateLevels` (`ML Frontend/Translate.lean:52`). -/
def TrLevels (lps : List Name) (us : List Lean.Level) (k : Nat) :
    Option (Fin k → Metalean.Level lps.length) := do
  let ls ← us.mapM (TrLevel lps)
  if h : ls.length = k then some fun i => ls[i.val]'(by omega) else none

/-! ## 3. Local contexts -/

/-- What a Lean local denotes: a Metalean variable (λ/Π binder) or, for a `let`, its translated
value (the translator inlines lets, `ML Frontend/Translate.lean:337-340`; `Ctx` has no let
entries, `ML Syntax/Ctx.lean:20`). Reference: lean4lean `VLocalDecl` (`L4 Typing/Basic.lean:19`). -/
inductive MLDecl (ζ : Metalean.Sigs) (ℓ n : Nat) where
  | vlam (v : Fin n)
  | vlet (val : Metalean.Expr ζ ℓ n)

/-- The Metalean term a local denotes. -/
def MLDecl.denote {ζ : Metalean.Sigs} {ℓ n : Nat} : MLDecl ζ ℓ n → Metalean.Expr ζ ℓ n
  | .vlam v => .var v
  | .vlet e => e

/-- Weakening by one new (last) Metalean variable. -/
def MLDecl.wk {ζ : Metalean.Sigs} {ℓ n : Nat} : MLDecl ζ ℓ n → MLDecl ζ ℓ (n + 1)
  | .vlam v => .vlam v.castSucc
  | .vlet e => .vlet e.wk

/-- The locals of a Lean term, innermost first: bound variables (`none`) and the traversal's free
variables (`some x`). Reference: lean4lean `VLCtx` (`L4 Typing/Basic.lean`), DV-13. -/
abbrev MLCtx (ζ : Metalean.Sigs) (ℓ n : Nat) := List (Option FVarId × MLDecl ζ ℓ n)

/-- Enter a λ/Π binder: every entry is weakened, the new local is the last variable. -/
def MLCtx.pushLam {ζ : Metalean.Sigs} {ℓ n : Nat} (Δ : MLCtx ζ ℓ n) (x : Option FVarId) :
    MLCtx ζ ℓ (n + 1) :=
  (x, .vlam (Fin.last n)) :: Δ.map fun (y, d) => (y, d.wk)

/-- The denotation of the bound variable `i` (entries of free variables are skipped). -/
def MLCtx.findB {ζ : Metalean.Sigs} {ℓ n : Nat} : MLCtx ζ ℓ n → Nat → Option (Metalean.Expr ζ ℓ n)
  | [], _ => none
  | (none, d) :: _, 0 => some d.denote
  | (none, _) :: Δ, i + 1 => findB Δ i
  | (some _, _) :: Δ, i => findB Δ i

/-- The denotation of the free variable `x`. -/
def MLCtx.findF {ζ : Metalean.Sigs} {ℓ n : Nat} : MLCtx ζ ℓ n → FVarId → Option (Metalean.Expr ζ ℓ n)
  | [], _ => none
  | (some y, d) :: Δ, x => if y == x then some d.denote else findF Δ x
  | (none, _) :: Δ, x => findF Δ x

/-! ## 4. Nat literals (own copy of Metalean's) -/

/-- Shape of `Nat.zero` (copy of `ML Checker/Acceleration/Literal.lean:16`). -/
abbrev natZeroSig : Metalean.CtorSig 1 :=
  { nfields := 0, nrecFields := 0, recursiveArity := ![], recursiveTarget := ![] }

/-- Shape of `Nat.succ` (copy of `ML Checker/Acceleration/Literal.lean:22`). -/
abbrev natSuccSig : Metalean.CtorSig 1 :=
  { nfields := 0, nrecFields := 1, recursiveArity := ![0], recursiveTarget := ![0] }

/-- Shape of `Nat` (copy of `ML Checker/Acceleration/Literal.lean:28 Nat.sig`). -/
abbrev natSig : Metalean.IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _
    | 0 => natZeroSig
    | 1 => natSuccSig

/-- The unary literal: copy of `Expr.natLit` (`ML Checker/Acceleration/Literal.lean:116`), what
the fast checker's `Denotes` relates `natLit k` to (`ML Checker/Fast/FExpr.lean:984`). -/
def natLitM {ζ : Metalean.Sigs} {ℓ n : Nat} (ηNat : Metalean.Head ζ (.inductive natSig)) :
    Nat → Metalean.Expr ζ ℓ n
  | 0 => .ctor ηNat 0 0 ![] ![] ![] ![]
  | k + 1 => .ctor ηNat 0 1 ![] ![] ![] ![natLitM ηNat k]

/-! ## 5. Terms: `TrM` -/

/-- The proof projection `maj.f` of a one-constructor (`c`), index-free inductive `η s` as Metalean's
translator builds it (`proofProjection`, `ML Checker/Slow/Projection.lean:54`, which is `partial`),
as a total function: a `recr` at level `0` whose minor returns the field (`fun fs => f`,
`caseOrdinary` under `caseTele`) and whose motive is `fun x => F` over the motive telescope, `F` the
type of field `f` with the parameters and, for the earlier fields, their proof projections of `x`
substituted (`ordinaryFieldExpr`; `proofProjectionType` substitutes the same terms, into the
dependent positions only). -/
def projProofTerm {ζ : Metalean.Sigs} (E : Metalean.Env ζ) {ι : Metalean.IndSig}
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) {ℓ : Nat}
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (hi : ι.nindices s = 0) {n : Nat}
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (f : Nat) (maj : Metalean.Expr ζ ℓ n) :
    Metalean.Expr ζ ℓ n :=
  let ps' : Fin ι.nparams → Metalean.Expr ζ ℓ (n + ι.nindices s + 1) :=
    fun p => (ps p).wkN (ι.nindices s + 1)
  let x : Metalean.Expr ζ ℓ (n + ι.nindices s + 1) := .var (Fin.last (n + ι.nindices s))
  let fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ (n + ι.nindices s + 1) :=
    fun j => if h : j.val < f then projProofTerm E η s c ls hi ps' j.val x else .prop
  let F : Metalean.Expr ζ ℓ (n + ι.nindices s + 1) :=
    if h : f < (ι.ctors s c).nfields then
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps' fds ⟨f, h⟩
    else .prop
  let ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n :=
    fun _ => Metalean.Ctx.lam F ((E.get η).block.motiveTele η ls ps s)
  .recr η s ls .zero ps ms
    (fun t d => if h : f < (ι.ctors t d).nfields then
      Metalean.Ctx.lam ((ι.ctors t d).caseOrdinary ⟨f, h⟩) ((E.get η).block.caseTele η ls ps ms t d)
      else .prop)
    (fun i => absurd i.isLt (by omega)) maj
termination_by f

/-- A Lean term whose head is a constant bound to a saturating binding. -/
def SpecialHead {ζ : Metalean.Sigs} (B : Binds ζ) (e : Lean.Expr) : Prop :=
  ∃ c us b, e.getAppFn = .const c us ∧ B c = some b ∧ b.isSpecial = true

/-- Metalean's field order for a constructor: ordinary fields in Lean order, then recursive fields
in Lean order (`metaOrderOf`, `ML Frontend/Inductive.lean:135`). -/
def MetaOrderOK (order : List Nat) (nf nr : Nat) : Prop :=
  ∃ ords recs, order = ords ++ recs ∧ ords.length = nf ∧ recs.length = nr ∧
    ords.Pairwise (· < ·) ∧ recs.Pairwise (· < ·) ∧ order.Perm (List.range (nf + nr))

/-- The level arguments of a recursor: the motive's universe comes first iff the block eliminates
into every sort (`translateSpecial`, leanElim mode, `ML Frontend/Translate.lean:289-296`). -/
def RecrLevels {ζ : Metalean.Sigs} {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (lps : List Name) (us : List Lean.Level) (l : Metalean.Level lps.length)
    (us' : List Lean.Level) : Prop :=
  (I.LargeElim ∧ ∃ u, us = u :: us' ∧ TrLevel lps u = some l) ∨
  (¬ I.LargeElim ∧ us' = us ∧ l = .zero)

/-- Arity of a quotient constant (`translateSpecial`, `ML Frontend/Translate.lean:240-249`). -/
def quotArity : Metalean.Export.QuotKind → Nat
  | .type => 2
  | .ctor => 3
  | .lift => 6
  | .ind => 5

/-- `saturate` (`ML Frontend/Translate.lean:226`) for each saturating binding: the translated
arguments `args` of a constant with levels `us` give the Metalean term. With at least the arity
the node takes the first arguments (constructor fields permuted by the order, recursor minors
wrapped by `wrapCase`); with fewer, the η-term applied to all of them. -/
inductive SatTr {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (lps : List Name) {n : Nat} :
    MBinding ζ → List Lean.Level → List (Metalean.Expr ζ lps.length n) →
    Metalean.Expr ζ lps.length n → Prop
  | indSat {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Metalean.Level lps.length}
      (ps : Fin ι.nparams → Metalean.Expr ζ lps.length n)
      (is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n) (rest) :
      TrLevels lps us ι.nlevels = some ls →
      SatTr E lps (.ind η s) us (List.ofFn ps ++ List.ofFn is ++ rest)
        ((Metalean.Expr.ind η s ls ps is).appList rest)
  | indEta {args : List (Metalean.Expr ζ lps.length n)} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Metalean.Level lps.length} :
      TrLevels lps us ι.nlevels = some ls → args.length < ι.nparams + ι.nindices s →
      SatTr E lps (.ind η s) us args
        ((Metalean.Frontend.indTerm (E.get η).block η s ls).wkClosed.appList args)
  | ctorSat {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      (ps : Fin ι.nparams → Metalean.Expr ζ lps.length n) (fs rest)
      (fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ lps.length n)
      (recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ lps.length n) :
      TrLevels lps us ι.nlevels = some ls →
      fs.length = (ι.ctors s c).nfields + (ι.ctors s c).nrecFields →
      order.length = (ι.ctors s c).nfields + (ι.ctors s c).nrecFields →
      (∀ o : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields),
        ∃ j a, order[o.val]? = some j ∧ fs[j]? = some a ∧ Fin.append fds recFds o = a) →
      SatTr E lps (.ctor η s c order) us (List.ofFn ps ++ fs ++ rest)
        ((Metalean.Expr.ctor η s c ls ps fds recFds).appList rest)
  | ctorEta {args : List (Metalean.Expr ζ lps.length n)} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      {t₀ : Metalean.Expr ζ lps.length 0} :
      TrLevels lps us ι.nlevels = some ls →
      args.length < ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) →
      Metalean.Frontend.ctorTerm (E.get η).block η s c ls order = .ok t₀ →
      SatTr E lps (.ctor η s c order) us args (t₀.wkClosed.appList args)
  | recrSat {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Metalean.Level lps.length} {l : Metalean.Level lps.length}
      (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat)
      (A : Fin (ι.recrEnd s) → Metalean.Expr ζ lps.length n) (rest)
      (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Metalean.Expr ζ lps.length n) :
      RecrLevels (E.get η).block lps us l us' → TrLevels lps us' ι.nlevels = some ls →
      (∀ t c, (orders[t.val]?.bind (·[c.val]?)) = some (mo t c)) →
      (∀ t c, Metalean.Frontend.wrapCase (E.get η).block η ls
        (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
        (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
        (A (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve) = .ok (mins t c)) →
      SatTr E lps (.recr η s orders) us (List.ofFn A ++ rest)
        ((Metalean.Expr.recr η s ls l
          (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
          (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve)
          (A (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve)).appList rest)
  | recrEta {args : List (Metalean.Expr ζ lps.length n)} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {ls : Fin ι.nlevels → Metalean.Level lps.length} {l : Metalean.Level lps.length}
      (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) {t₀ : Metalean.Expr ζ lps.length 0} :
      RecrLevels (E.get η).block lps us l us' → TrLevels lps us' ι.nlevels = some ls →
      (∀ t c, (orders[t.val]?.bind (·[c.val]?)) = some (mo t c)) →
      args.length < ι.recrEnd s →
      Metalean.Frontend.recrTerm (E.get η).block η s ls l mo = .ok t₀ →
      SatTr E lps (.recr η s orders) us args (t₀.wkClosed.appList args)
  | quotType {η : Metalean.Head ζ .quot} {u : Metalean.Level lps.length} :
      us.mapM (TrLevel lps) = some [u] →
      SatTr E lps (.quot η .type) us ([α, r] ++ rest) ((Metalean.Expr.quot η u α r).appList rest)
  | quotMk {η : Metalean.Head ζ .quot} {u : Metalean.Level lps.length} :
      us.mapM (TrLevel lps) = some [u] →
      SatTr E lps (.quot η .ctor) us ([α, r, a] ++ rest)
        ((Metalean.Expr.quotMk η u α r a).appList rest)
  | quotLift {η : Metalean.Head ζ .quot} {u v : Metalean.Level lps.length} :
      us.mapM (TrLevel lps) = some [u, v] →
      SatTr E lps (.quot η .lift) us ([α, r, β, f, h, a] ++ rest)
        ((Metalean.Expr.quotLift η u v α r β f h a).appList rest)
  | quotInd {η : Metalean.Head ζ .quot} {u : Metalean.Level lps.length} :
      us.mapM (TrLevel lps) = some [u] →
      SatTr E lps (.quot η .ind) us ([α, r, β, f, a] ++ rest)
        ((Metalean.Expr.quotInd η u α r β f a).appList rest)
  | quotEta {args : List (Metalean.Expr ζ lps.length n)} {η : Metalean.Head ζ .quot} {ls' : List (Metalean.Level lps.length)}
      {t₀ : Metalean.Expr ζ lps.length 0} :
      us.mapM (TrLevel lps) = some ls' → args.length < quotArity kind →
      Metalean.Frontend.quotTerm η (E.get η).eqHead kind ls' = .ok t₀ →
      SatTr E lps (.quot η kind) us args (t₀.wkClosed.appList args)

/-- `TrM E B lps Γ Δ e t`: the Lean term `e` (locally nameless; loose bound variables and the
traversal's free variables denote the locals `Δ`) is the Lean form of the Metalean term `t` in
the context `Γ`. Rule by rule after `translateWith` (`ML Frontend/Translate.lean:316-345`), as a
relation: the translator is `partial` and decides projections with an unverified `inferType`.
Reference: lean4lean `TrExprS` (`L4 Typing/Basic.lean:19`), DV-1. -/
inductive TrM {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) :
    {n : Nat} → Metalean.Ctx ζ lps.length 0 n → MLCtx ζ lps.length n → Lean.Expr →
    Metalean.Expr ζ lps.length n → Prop
  /-- `ML Frontend/Translate.lean:318`. -/
  | bvar : Δ.findB i = some t → TrM E B lps Γ Δ (.bvar i) t
  /-- The traversal's locals (no Metalean counterpart, DV-13). -/
  | fvar : Δ.findF x = some t → TrM E B lps Γ Δ (.fvar x) t
  /-- `:322`. -/
  | sort : TrLevel lps u = some l → TrM E B lps Γ Δ (.sort u) (.sort l)
  /-- `:325` with `translateConst` (`:65`). -/
  | const {kind : Metalean.ConstKind} {nl : Nat} {η : Metalean.Head ζ (.const kind nl)}
      {ls : Fin nl → Metalean.Level lps.length} :
      B c = some (.const η) → TrLevels lps us nl = some ls →
      TrM E B lps Γ Δ (.const c us) (.const η ls)
  /-- `:326` with `translateSpecial` (`:234`): the whole spine, arguments translated one by one. -/
  | special {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
      {as : List Lean.Expr} {as' : List (Metalean.Expr ζ lps.length n)}
      {b : MBinding ζ} {t : Metalean.Expr ζ lps.length n} :
      B c = some b → b.isSpecial = true → as.length = as'.length →
      (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → TrM E B lps Γ Δ a a') →
      SatTr E lps b us as' t → TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t
  /-- `:328-330`, heads that do not saturate. -/
  | app : ¬ SpecialHead B f → TrM E B lps Γ Δ f f' → TrM E B lps Γ Δ a a' →
      TrM E B lps Γ Δ (.app f a) (.app f' a')
  /-- `:331-333`. -/
  | lam : TrM E B lps Γ Δ A A' → TrM E B lps (Γ.snoc A') (Δ.pushLam none) b b' →
      TrM E B lps Γ Δ (.lam x A b bi) (.lam A' b')
  /-- `:334-336`. -/
  | forallE : TrM E B lps Γ Δ A A' → TrM E B lps (Γ.snoc A') (Δ.pushLam none) b b' →
      TrM E B lps Γ Δ (.forallE x A b bi) (.forallE A' b')
  /-- `:337-340`: the body is translated with the let-bound local denoting the value. -/
  | letE : TrM E B lps Γ Δ T T' → TrM E B lps Γ Δ v v' →
      TrM E B lps Γ ((none, .vlet v') :: Δ) b b' →
      TrM E B lps Γ Δ (.letE x T v b nd) (.letE T' v' b'.wk)
  /-- Metadata is dropped by the export. -/
  | mdata : TrM E B lps Γ Δ e t → TrM E B lps Γ Δ (.mdata d e) t
  /-- Nat literals as unary constructor chains (`ML Checker/Fast/FExpr.lean:984`). -/
  | lit {ηNat : Metalean.Head ζ (.inductive natSig)} :
      B ``Nat = some (.ind ηNat 0) → TrM E B lps Γ Δ (.lit (.natVal k)) (natLitM ηNat k)
  /-- Projections of a structure (`project`, `ML Checker/Slow/Projection.lean:96-106`). -/
  | projStruct {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
      {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n}
      (hst : (E.get η).block.IsStructure s c) (hi : i < (ι.ctors s c).nfields) :
      B S = some (.ind η s) → TrM E B lps Γ Δ e e' → E[Γ] ⊢ e' : .ind η s ls ps is →
      TrM E B lps Γ Δ (.proj S i e) (hst.projTerm η ls ps ⟨i, hi⟩ e')
  /-- Projections of a proof of a one-constructor, index-free, non-recursive inductive that is not
  a structure (`project`, `ML Checker/Slow/Projection.lean:96-113`): the translator's proof
  projection `projProofTerm` (`proofProjection`, `:54`) on the major. -/
  | projProof {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
      {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n} (hi : ι.nindices s = 0) :
      B S = some (.ind η s) → (∀ t : Fin ι.nsorts, t = s) → (∀ d : Fin (ι.nctors s), d = c) →
      (ι.ctors s c).nrecFields = 0 → i < (ι.ctors s c).nfields →
      ¬ (E.get η).block.IsStructure s c →
      TrM E B lps Γ Δ e e' → E[Γ] ⊢ e' : .ind η s ls ps is →
      TrM E B lps Γ Δ (.proj S i e) (projProofTerm E η s c ls hi ps i e')

/-! ## 6. Declarations: `ProgEnv` -/

/-- First declaration named `c`. Reference: `lookup_env` (`MR common/theories/Environment.v:483`). -/
def findDecl (decls : List ConstantInfo) (c : Name) : Option ConstantInfo :=
  decls.find? (·.name == c)

/-- A constant's Lean type translates to a type of the constant's translation (its η-term for
saturating bindings): type inference on constants is sound by lookup. Reference: `on_global_env`
typing of a declaration's type (MC §3.6). -/
def ConstTyped {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (ci : ConstantInfo) : Prop :=
  ∃ T t₀ : Metalean.Expr ζ ci.levelParams.length 0, TrM E B ci.levelParams .nil [] ci.type T ∧
    TrM E B ci.levelParams .nil [] (.const ci.name (ci.levelParams.map .param)) t₀ ∧
    E[.nil] ⊢ t₀ : T

/-- The extended table agrees with the old one, weakened, outside the new names. -/
def BindsExt {ζ : Metalean.Sigs} {sig : Metalean.Sig} (B : Binds ζ) (B' : Binds (ζ.snoc sig))
    (names : List Name) : Prop :=
  ∀ n, n ∉ names → B' n = B.wk n

/-- An inductive block of Lean declarations is the Lean form of the Metalean block at the head `η`
of `E'` (the environment after the block): the block's types (`Is`), constructors (`Cs`) and
recursors (`Rs`), their counts and positions (the recursor's parameter, motive, minor and index
counts are those of the block), the arity of every minor premise of the recursors' Lean types,
Metalean's field orders, the table entries, and the type of every constant (`ConstTyped`). Model:
`analyzeBlock` (`ML Frontend/Inductive.lean:227`) without reproducing it; recursor rules are not
related (Metalean has none). -/
structure IndBlock {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) {ι : Metalean.IndSig}
    (η : Metalean.Head ζ (.inductive ι)) (lps : List Name) (Is : Fin ι.nsorts → InductiveVal)
    (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal) (Rs : Fin ι.nsorts → RecursorVal)
    (orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat) : Prop where
  levels : lps.length = ι.nlevels
  ind : ∀ s, B (Is s).name = some (.ind η s) ∧ (Is s).levelParams = lps ∧
    (Is s).all = List.ofFn (fun t => (Is t).name) ∧ (Is s).numParams = ι.nparams ∧
    (Is s).numIndices = ι.nindices s ∧ (Is s).ctors = List.ofFn (fun c => (Cs s c).name) ∧
    (Is s).isUnsafe = false ∧ (Is s).numNested = 0
  ctor : ∀ s c, B (Cs s c).name = some (.ctor η s c (orders s c)) ∧
    (Cs s c).levelParams = lps ∧ (Cs s c).induct = (Is s).name ∧ (Cs s c).cidx = c.val ∧
    (Cs s c).numParams = ι.nparams ∧
    (Cs s c).numFields = (ι.ctors s c).nfields + (ι.ctors s c).nrecFields ∧
    (Cs s c).isUnsafe = false ∧
    MetaOrderOK (orders s c) (ι.ctors s c).nfields (ι.ctors s c).nrecFields
  recr : ∀ s, (Rs s).name = mkRecName (Is s).name ∧
    B (Rs s).name = some (.recr η s (List.ofFn fun t => List.ofFn fun c => orders t c)) ∧
    ((E.get η).block.LargeElim → ∃ u, (Rs s).levelParams = u :: lps) ∧
    (¬ (E.get η).block.LargeElim → (Rs s).levelParams = lps) ∧ (Rs s).isUnsafe = false ∧
    (Rs s).all = (Is s).all ∧ (Rs s).numParams = ι.nparams ∧ (Rs s).numMotives = ι.nsorts ∧
    (Rs s).numMinors = (List.ofFn fun t => ι.nctors t).sum ∧ (Rs s).numIndices = ι.nindices s
  /-- The minor premise of constructor `c` of sort `t` in a recursor's Lean type has
  `nfields + 2 * nrecFields` leading `Π`s, one per field and one per induction hypothesis, as
  Metalean's ι-rule applies the minor (`iotaRhs`, `ML Syntax/Inductive/Iota.lean:161`). It is the
  arity the `casesOn` recognizer reads (`Erasure.minorArity`), which `ConstTyped` does not fix:
  it relates the Lean type to Metalean's up to metadata and definitional equality. -/
  minors : ∀ s t c, minorArity (Rs s).type
      (ι.nparams + ι.nsorts + ((List.ofFn fun t => ι.nctors t).take t.val).sum + c.val) =
    (ι.ctors t c).nfields + 2 * (ι.ctors t c).nrecFields

/-- The Lean declarations of a block, in the order `ProgEnv` adds them. -/
def IndBlock.decls {ι : Metalean.IndSig} (Is : Fin ι.nsorts → InductiveVal)
    (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal) (Rs : Fin ι.nsorts → RecursorVal) :
    List ConstantInfo :=
  List.ofFn (fun s => .recInfo (Rs s)) ++
    (List.ofFn fun s => List.ofFn fun c => ConstantInfo.ctorInfo (Cs s c)).flatten ++
    List.ofFn (fun s => .inductInfo (Is s))

/-- The quotient kind of Lean's `QuotVal` in Metalean's export format. -/
def quotKindOf : Lean.QuotKind → Metalean.Export.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- `ProgEnv P ζ E B`: the newest-first list of Lean declarations `P` is the Lean form of the
Metalean environment `E` with name table `B`, one entry per declaration (block), after Metalean's
loader (`ML Checker/Slow/Loader.lean:55-139`): safe axioms, definitions (`all = [name]`: no
recursion), theorems as `opaque` (`:122-127`), opaques, inductive blocks, quotients (with `Eq`).
Names are fresh. Reference: `wf_ext Σ` (`MR P/PCUICTyping.v:507`), lean4lean `TrEnv'`
(`L4 Env.lean:39`); DV-3. -/
inductive ProgEnv : List ConstantInfo → (ζ : Metalean.Sigs) → Metalean.Env ζ → Binds ζ → Prop
  | nil : ProgEnv [] .nil .nil fun _ => none
  | «axiom» {v : AxiomVal} {t : Metalean.Expr ζ v.levelParams.length 0} :
      ProgEnv P ζ E B → findDecl P v.name = none → v.isUnsafe = false →
      TrM E B v.levelParams .nil [] v.type t →
      ProgEnv (.axiomInfo v :: P) (ζ.snoc (.const .«axiom» v.levelParams.length))
        (E.snoc (.«axiom» t)) (B.wk.set v.name (.const .here))
  | defn {v : DefinitionVal} {t e : Metalean.Expr ζ v.levelParams.length 0} :
      ProgEnv P ζ E B → findDecl P v.name = none → v.safety = .safe → v.all = [v.name] →
      TrM E B v.levelParams .nil [] v.type t → TrM E B v.levelParams .nil [] v.value e →
      ProgEnv (.defnInfo v :: P) (ζ.snoc (.const .def v.levelParams.length))
        (E.snoc (.def t e)) (B.wk.set v.name (.const .here))
  | thm {v : TheoremVal} {t : Metalean.Expr ζ v.levelParams.length 0} :
      ProgEnv P ζ E B → findDecl P v.name = none → v.all = [v.name] →
      TrM E B v.levelParams .nil [] v.type t → E[.nil] ⊢ t : .prop →
      ProgEnv (.thmInfo v :: P) (ζ.snoc (.const .«opaque» v.levelParams.length))
        (E.snoc (.«opaque» t)) (B.wk.set v.name (.const .here))
  | «opaque» {v : OpaqueVal} {t : Metalean.Expr ζ v.levelParams.length 0} :
      ProgEnv P ζ E B → findDecl P v.name = none → v.isUnsafe = false → v.all = [v.name] →
      TrM E B v.levelParams .nil [] v.type t →
      ProgEnv (.opaqueInfo v :: P) (ζ.snoc (.const .«opaque» v.levelParams.length))
        (E.snoc (.«opaque» t)) (B.wk.set v.name (.const .here))
  | induct {ι : Metalean.IndSig} {I : Metalean.Inductive ζ ι} {B' : Binds (ζ.snoc (.inductive ι))}
      {lps : List Name} {Is : Fin ι.nsorts → InductiveVal}
      {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal}
      {Rs : Fin ι.nsorts → RecursorVal} {orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat} :
      ProgEnv P ζ E B →
      ((IndBlock.decls Is Cs Rs).map (·.name)).Nodup →
      (∀ ci ∈ IndBlock.decls Is Cs Rs, findDecl P ci.name = none) →
      BindsExt B B' ((IndBlock.decls Is Cs Rs).map (·.name)) →
      IndBlock (E.snoc (.inductive I)) B' .here lps Is Cs Rs orders →
      (∀ ci ∈ IndBlock.decls Is Cs Rs, ConstTyped (E.snoc (.inductive I)) B' ci) →
      ProgEnv (IndBlock.decls Is Cs Rs ++ P) (ζ.snoc (.inductive ι)) (E.snoc (.inductive I)) B'
  | quot {ηEq : Metalean.Head ζ (.inductive Metalean.Eq.sig)} {qs : List QuotVal}
      {B' : Binds (ζ.snoc .quot)} :
      ProgEnv P ζ E B → B ``Eq = some (.ind ηEq 0) →
      qs.map (·.name) = [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] →
      (∀ q ∈ qs, findDecl P q.name = none) → BindsExt B B' (qs.map (·.name)) →
      (∀ q ∈ qs, B' q.name = some (.quot .here (quotKindOf q.kind)) ∧
        ConstTyped (E.snoc (.quot ηEq)) B' (.quotInfo q)) →
      ProgEnv (qs.reverse.map .quotInfo ++ P) (ζ.snoc .quot) (E.snoc (.quot ηEq)) B'

/-! ## 7. Source semantics -/

/-- The program's environment as evaluation sees it, with the configuration's `@[extern]`
remapping. Reference: the environment of `MR P/PCUICWcbvEval.v:231 eval`, DV-12. -/
structure EvalEnv where
  decls : List ConstantInfo
  axiomatized : ConstantInfo → Bool

/-- The inductive of a recognized `casesOn` constant (the shipping recognizer `Erasure.casesInfo?`).
Reference: none (`tCase` is syntax in PCUIC; DV-25). -/
def EvalEnv.casesOn? (σ : EvalEnv) (c : Name) : Option InductiveVal :=
  match casesInfo? σ.decls c with
  | some ci => match findDecl σ.decls ci.indName with
    | some (.inductInfo iv) => some iv
    | _ => none
  | none => none

/-- Position of the major premise of `T.casesOn` (`params, motive, indices, major, minors`). -/
def casesMajor (iv : InductiveVal) : Nat := iv.numParams + 1 + iv.numIndices

/-- Arity of `T.casesOn`. -/
def casesArity (iv : InductiveVal) : Nat := casesMajor iv + 1 + iv.ctors.length

/-- The arity of a constructor or recognized `casesOn` head, if it is one (the `arity` that
`visitConstApp` η-expands to, `LeanToLambdaBox/Erasure.lean:753`). -/
def specialArity (σ : EvalEnv) (c : Name) : Option Nat :=
  match findDecl σ.decls c with
  | some (.ctorInfo cv) => some (cv.numParams + cv.numFields)
  | _ => (σ.casesOn? c).map casesArity

/-- Instantiate the leading Π-binders of a type with the arguments, in order (the type of the
application, as the oracle's `inferType` computes it, `LeanToLambdaBox/Erasure/Pure.lean:97`). -/
def piInst : List Expr → Expr → Option Expr
  | [], ty => some ty
  | a :: as, .forallE _ _ b _ => piInst as (b.instantiate1' a)
  | _ :: _, _ => none

/-- `body` under λ-binders with the names, domains and binder infos of the first `k` Π-binders of
the type. -/
def lamsOf : Nat → Expr → Expr → Option Expr
  | 0, _, body => some body
  | k + 1, .forallE n d b bi, body => (lamsOf k b body).map fun e => .lam n d e bi
  | _ + 1, _, _ => none

/-- The η-expansion of a constructor or recognized `casesOn` spine `c.{us} as` with fewer arguments
than its arity `ar`: `fun xs => c.{us} as xs` over the remaining `ar - |as|` binders of its type, the
arguments `as` unevaluated under the new binders. This is the term `withAppEtaToMinArity`
(`LeanToLambdaBox/Erasure.lean:606`) erases: binders from the Π-binders of the spine's type,
`visitConstructor`/`visitCases` on the saturated spine. Reference: none (MetaRocq η-expands in λ□,
`MR E/EEtaExpanded.v`; DV-23). -/
def EvalEnv.etaSpine? (σ : EvalEnv) (c : Name) (us : List Level) (as : List Expr) : Option Expr :=
  match findDecl σ.decls c, specialArity σ c with
  | some ci, some ar =>
    if as.length < ar then
      (piInst as (Pure.instLevels ci.levelParams us ci.type)).bind fun ty =>
        lamsOf (ar - as.length) ty (mkAppN (.const c us)
          (as.map (·.liftLooseBVars' 0 (ar - as.length)) ++
            (List.range (ar - as.length)).reverse.map Expr.bvar).toArray)
    else none
  | _, _ => none

/-- A constructor or recognized `casesOn` spine with at most its arity of arguments: such spines are
evaluated as a whole (`SrcEval.eta`, `ctor`, `casesIota`, `casesLit*`), never by `beta`/`appCong`. -/
def ShortSpine (σ : EvalEnv) (e : Expr) : Prop :=
  ∃ c us ar, e.getAppFn = .const c us ∧ specialArity σ c = some ar ∧ e.getAppNumArgs ≤ ar

/-- δ: definitions that the configuration does not remap and that are not recognized `casesOn`
constants; theorems, axioms and opaques have no δ (Metalean loads theorems as opaque, DV-24;
DV-10). Reference: `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
def EvalEnv.unfold? (σ : EvalEnv) (c : Name) : Option (ConstantInfo × Expr) :=
  match findDecl σ.decls c with
  | some ci@(.defnInfo v) =>
    if σ.axiomatized ci || (σ.casesOn? c).isSome then none else some (ci, v.value)
  | _ => none

/-- A level that is zero under every assignment, structurally (port of `L4 Atoms.lean`). -/
def EvidentZero : Level → Bool
  | .zero => true
  | .max a b => EvidentZero a && EvidentZero b
  | .imax _ b => EvidentZero b
  | _ => false

/-- Declarations without δ that may head an evident proposition: axioms, opaques, theorems and
inductive type formers. Reference: `tInd` heads (`MR P/PCUICWcbvEval.v:51 atom`), DV-11. -/
def DeltaFree : ConstantInfo → Bool
  | .axiomInfo _ | .opaqueInfo _ | .thmInfo _ | .inductInfo _ => true
  | _ => false

/-- An evident proposition `Π xs, h.{vs} a₁…aₙ` with `h` `DeltaFree`, of declared arity type with
exactly `n` binders, evidently in `Prop` (port of `L4 Atoms.lean`). Reference: `isPropositional`
(`MR P/PCUICFirstorder.v:109`). -/
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

/-- Declarations that are evaluated by their own rules: constructors, recursors (outside Phase I),
quotient constants (outside Phase I). -/
def OwnRules : ConstantInfo → Bool
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
  | _ => false

/-- Theorems: δ-less (DV-24), their statements are propositions (`ProgEnv.thm`). -/
def IsThm : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- δ-less constants that are values: evident type formers (incl. inductive types), proofs of
evident propositions, and theorems. Reference: `tInd` in `MR P/PCUICWcbvEval.v:51 atom`, DV-11,
DV-24. -/
def EvalEnv.isAtom (σ : EvalEnv) (c : Name) : Bool :=
  match findDecl σ.decls c with
  | some ci => (σ.unfold? c).isNone && (σ.casesOn? c).isNone && !OwnRules ci &&
      ((arityShape ci.type).isSome || EvidentProp σ.decls ci.type || IsThm ci)
  | none => false

/-- λ, sort, Π. Reference: `MR P/PCUICWcbvEval.v:51 atom`. -/
def SrcAtom : Expr → Prop
  | .lam .. | .sort _ | .forallE .. => True
  | _ => False

/-- A constructor value of the inductive `T`: the `i`-th constructor applied to its parameters and
fields. Reference: `mkApps (tConstruct ind i u) args` (`MR P/PCUICWcbvEval.v:500 value`). -/
def CtorValue (σ : EvalEnv) (T : Name) (m : Expr) (i : Nat) (fs : List Expr) : Prop :=
  ∃ C us cv ps, findDecl σ.decls C = some (.ctorInfo cv) ∧ cv.induct = T ∧ cv.cidx = i ∧
    ps.length = cv.numParams ∧ fs.length = cv.numFields ∧
    m = mkAppN (.const C us) (ps ++ fs).toArray

/-- Heads excluded by `appCong`: λ, sort, Π, literals, constructor and `casesOn` spines. Reference:
the side condition of `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`: `~~ (isLambda f' || isFixApp f' ||
isArityHead f' || isConstructApp f' || isPrimApp f')`; literals are values, `isPrimApp`). -/
def BlocksCong (σ : EvalEnv) : Expr → Prop
  | .lam .. | .sort _ | .forallE .. | .lit _ => True
  | e => (∃ c us cv, e.getAppFn = .const c us ∧ findDecl σ.decls c = some (.ctorInfo cv)) ∨
    (∃ c us iv, e.getAppFn = .const c us ∧ σ.casesOn? c = some iv)

/-- Spines headed by an atom constant (port of `L4 Source/Eval.lean`). -/
inductive AtomSpine (σ : EvalEnv) : Expr → Prop
  | const : σ.isAtom c = true → AtomSpine σ (.const c us)
  | app : AtomSpine σ f → AtomSpine σ (.app f a)

/-- The inductive `T` is declared in `Prop`: its type is an arity whose sort is evidently zero.
Reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`), on the declared sort. -/
def EvalEnv.propInd (σ : EvalEnv) (T : Name) : Bool :=
  match findDecl σ.decls T with
  | some (.inductInfo iv) => match arityShape iv.type with
    | some (_, u) => EvidentZero u
    | none => false
  | _ => false

/-- The statement of a constant spine `h.{us} as`: the declared type of `h` instantiated at the
levels and the arguments (`piInst`). -/
def EvalEnv.spineType? (σ : EvalEnv) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const h us => (findDecl σ.decls h).bind fun ci =>
    piInst e.getAppArgs.toList (Pure.instLevels ci.levelParams us ci.type)
  | _ => none

/-- The sort level of the discriminant's type of `T.casesOn.{us}`: `T`'s declared sort at the last
levels of `us` (a large-eliminating `casesOn` has the motive's level first), what `visitCases` reads
with `Backend.typeLevel` (`LeanToLambdaBox/Erasure.lean:843`) on a typed discriminant. -/
def casesSortLevel (iv : InductiveVal) (us : List Level) : Option Level :=
  (arityShape iv.type).map fun (_, u) =>
    Pure.instLevel iv.levelParams (us.drop (us.length - iv.levelParams.length)) u

/-- `visitCases` reduces `T.casesOn.{us}` at erasure time, without a λ□ `case`: `T` has one
constructor and the discriminant's sort may be zero (`Level.isNeverZero` fails,
`LeanToLambdaBox/Erasure.lean:843,870`). -/
def CasesReduced (iv : InductiveVal) (us : List Level) : Prop :=
  iv.ctors.length = 1 ∧ ∃ l, casesSortLevel iv us = some l ∧ l.isNeverZero = false

/-- Neutral proofs built by projections: a projection of a `Prop` inductive out of an atom spine or
out of such a projection, applied to arguments. Reference: none (PCUIC evaluates proofs to
constructors, `MR P/PCUICWcbvEval.v:264 eval_proj`; theorems have no δ here, DV-24). -/
inductive PropProj (σ : EvalEnv) : Expr → Prop
  | proj : σ.propInd S = true → AtomSpine σ e → PropProj σ (.proj S i e)
  | projProj : σ.propInd S = true → PropProj σ e → PropProj σ (.proj S i e)
  | app : PropProj σ f → PropProj σ (.app f a)

/-- Weak call-by-value evaluation of closed source terms. Constructor and recognized `casesOn`
spines are evaluated as a whole: with fewer arguments than their arity they are η-expanded, the
arguments unevaluated under the new binders (`eta`; the eraser's `withAppEtaToMinArity`, DV-23), so
that later arguments arrive by `beta`, evaluated, as in λ□; a saturated constructor evaluates its
arguments (`eval_construct`); a saturated `casesOn` evaluates only its major premise and continues
with the alternative of the major's constructor (`eval_iota`; DV-25). Theorems have no δ, so a proof
may evaluate to an atom spine instead of a constructor: a `casesOn` of a field-less `Prop`
constructor and a `Prop` projection then proceed as λ□'s `eval_iota_sing` and `eval_proj_prop` do
(`casesProof`, `projProp`; DV-24). Reference: `MR P/PCUICWcbvEval.v:231 eval`; MC §5.6. -/
inductive SrcEval (σ : EvalEnv) : Expr → Expr → Prop
  /-- `eval_beta` (`MR P/PCUICWcbvEval.v:234`). -/
  | beta : ¬ ShortSpine σ (.app f a) → SrcEval σ f (.lam n A b bi) → SrcEval σ a a' →
      SrcEval σ (b.instantiate1' a') v → SrcEval σ (.app f a) v
  /-- `eval_zeta` (`:241`). -/
  | zeta : SrcEval σ val val' → SrcEval σ (b.instantiate1' val') v →
      SrcEval σ (.letE n T val b nd) v
  /-- `eval_delta` (`:247`). -/
  | delta : σ.unfold? c = some (ci, body) →
      SrcEval σ (Pure.instLevels ci.levelParams us body) v → SrcEval σ (.const c us) v
  /-- `eval_atom` on `tInd`/propositional constants (`:331`, DV-11). -/
  | constAtom : σ.isAtom c = true → SrcEval σ (.const c us) (.const c us)
  /-- A constructor or recognized `casesOn` spine with missing arguments is its η-expansion, a λ
  (DV-23). -/
  | eta {as : List Expr} : σ.etaSpine? c us as = some e' →
      SrcEval σ (mkAppN (.const c us) as.toArray) e'
  /-- `eval_construct` (`:303`): a saturated constructor spine evaluates its arguments. -/
  | ctor {as vs : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      as.length = cv.numParams + cv.numFields → as.length = vs.length →
      (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SrcEval σ a v) →
      SrcEval σ (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray)
  /-- `eval_iota` (`:253`): a saturated recognized `casesOn`; the major evaluates to a constructor
  value; the alternative of its constructor is applied to its fields. -/
  | casesIota {as : List Expr} : σ.casesOn? c = some iv → as.length = casesArity iv →
      as[casesMajor iv]? = some m → SrcEval σ m mv → CtorValue σ iv.name mv i fs →
      as[casesMajor iv + 1 + i]? = some alt → SrcEval σ (mkAppN alt fs.toArray) v →
      SrcEval σ (mkAppN (.const c us) as.toArray) v
  /-- `eval_iota` on a Nat literal major (`casesOnLit`): `0` and `k+1`. -/
  | casesLitZero {as : List Expr} : σ.casesOn? c = some iv → iv.name = ``Nat →
      as.length = casesArity iv → as[casesMajor iv]? = some m →
      SrcEval σ m (.lit (.natVal 0)) → as[casesMajor iv + 1]? = some alt → SrcEval σ alt v →
      SrcEval σ (mkAppN (.const c us) as.toArray) v
  | casesLitSucc {as : List Expr} : σ.casesOn? c = some iv → iv.name = ``Nat →
      as.length = casesArity iv → as[casesMajor iv]? = some m →
      SrcEval σ m (.lit (.natVal (k + 1))) → as[casesMajor iv + 2]? = some alt →
      SrcEval σ (.app alt (.lit (.natVal k))) v → SrcEval σ (mkAppN (.const c us) as.toArray) v
  /-- `eval_iota` on a proof that is not a constructor (as λ□ `eval_iota_sing`,
  `MR E/EWcbvEval.v:162`, which the eraser applies at erasure time, `Erases.casesReduced`): a
  saturated recognized `casesOn` whose discriminant's sort is zero at its levels and whose inductive's
  only constructor `cn` has no field, on a major that evaluates to an atom spine (a theorem, an
  axiom, an opaque proof) whose declared statement is the type of `cn` at some parameters, continues
  with the alternative. Metalean: proof irrelevance at the statement makes the major `cn ps`, then
  ι. -/
  | casesProof {as ps : List Expr} : σ.casesOn? c = some iv → as.length = casesArity iv →
      as[casesMajor iv]? = some m → SrcEval σ m mv → AtomSpine σ mv →
      casesSortLevel iv us = some l → EvidentZero l = true → iv.ctors = [cn] → findDecl σ.decls cn = some (.ctorInfo cv) → cv.numFields = 0 →
      σ.spineType? mv = some st → ps.length = cv.numParams →
      piInst ps (Pure.instLevels cv.levelParams vs cv.type) = some st →
      as[casesMajor iv + 1]? = some alt → SrcEval σ alt v →
      SrcEval σ (mkAppN (.const c us) as.toArray) v
  /-- `eval_proj` (`:264`). -/
  | proj : SrcEval σ e m → CtorValue σ S m 0 fs → fs[i]? = some a → SrcEval σ (.proj S i e) a
  /-- `eval_proj` on a proof that is not a constructor (λ□ `eval_proj_prop`, `MR E/EWcbvEval.v:238`):
  the projection of a `Prop` inductive out of a neutral proof is a neutral proof (`PropProj`). -/
  | projProp : σ.propInd S = true → SrcEval σ e m → (AtomSpine σ m ∨ PropProj σ m) →
      SrcEval σ (.proj S i e) (.proj S i m)
  /-- Nat literals are values (`eval_atom` on primitive values). -/
  | lit : SrcEval σ (.lit (.natVal k)) (.lit (.natVal k))
  /-- `eval_app_cong` (`:311`). -/
  | appCong : ¬ ShortSpine σ (.app f a) → SrcEval σ f f' → ¬ BlocksCong σ f' → SrcEval σ a a' →
      SrcEval σ (.app f a) (.app f' a')
  /-- Metadata is transparent. -/
  | mdata : SrcEval σ e v → SrcEval σ (.mdata d e) v
  /-- `eval_atom` (`:331`) on λ, sort, Π. -/
  | atom : SrcAtom e → SrcEval σ e e

/-! ## 8. Erasability -/

/-- `T` is convertible to `Π Δ, Sort u`. Reference: `isArity` (`MR P/PCUICTyping.v:29`), up to
conversion as in `MR E/Extract.v:18 isErasable`. -/
def IsArity {ζ : Metalean.Sigs} {ℓ n : Nat} (E : Metalean.Env ζ) (Γ : Metalean.Ctx ζ ℓ 0 n)
    (T : Metalean.Expr ζ ℓ n) : Prop :=
  ∃ (k : Nat) (Δ : Metalean.Ctx ζ ℓ n (n + k)) (u : Metalean.Level ℓ), E[Γ] ⊢ T ≡ Metalean.Ctx.pi (.sort u) Δ typ

/-- A type former or a proof. Reference: `MR E/Extract.v:18 isErasable`. -/
def IsErasable {ζ : Metalean.Sigs} {ℓ n : Nat} (E : Metalean.Env ζ) (Γ : Metalean.Ctx ζ ℓ 0 n)
    (t : Metalean.Expr ζ ℓ n) : Prop :=
  ∃ T, E[Γ] ⊢ t : T ∧ (IsArity E Γ T ∨ E[Γ] ⊢ T : .prop)

/-- Erasability of a Lean term through its translation. Reference: `isErasable` on the PCUIC
term of a source term. -/
def ErasableS {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) {n : Nat}
    (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n) (e : Expr) : Prop :=
  ∃ t, TrM E B lps Γ Δ e t ∧ IsErasable E Γ t

/-! ## 9. Closures, views (ports of `L4 Source/Restrict.lean`, `L4 Core/Scope.lean`) -/

/-- Every constant of `e` satisfies `p`. Reference: `term_global_deps` (`MR E/EAstUtils.v:406`). -/
def ConstsIn (p : Name → Prop) : Expr → Prop
  | .const c _ => p c
  | .app f a => ConstsIn p f ∧ ConstsIn p a
  | .lam _ t b _ | .forallE _ t b _ => ConstsIn p t ∧ ConstsIn p b
  | .letE _ t v b _ => ConstsIn p t ∧ ConstsIn p v ∧ ConstsIn p b
  | .mdata _ e | .proj _ _ e => ConstsIn p e
  | _ => True

/-- The expressions the pure traversal reads from a closure `decls`: every type, and the values of
the definitions that are not recognized `casesOn` constants and of the opaques (not of theorems,
which are erased as proofs; not of recognized `casesOn` constants, which the traversal turns into λ□
`case`). -/
def ReadExpr (decls : List ConstantInfo) (ci : ConstantInfo) (x : Expr) : Prop :=
  x = ci.type ∨
    (∃ d, ci = .defnInfo d ∧ x = d.value ∧ (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isNone) ∨
    ∃ o, ci = .opaqueInfo o ∧ x = o.value

/-- Kernames of the program's constants are distinct. Reference: none (DV-14). -/
def KernameInj (decls : List ConstantInfo) : Prop :=
  ∀ c₁ c₂, (findDecl decls c₁).isSome → (findDecl decls c₂).isSome →
    toKername c₁ = toKername c₂ → c₁ = c₂

/-- `decls` is a sub-environment of `P`. Reference: `extends` (`MR common/theories/Environment.v`). -/
def SubEnv (decls P : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, findDecl P ci.name = some ci

/-- `decls` is closed under what the pure traversal and the recognizer read: the constants of the
expressions the traversal reads (`ReadExpr`: types; values of definitions other than recognized
`casesOn` constants, and of opaques; not theorem values), the block members (`ConstantInfo.all`),
the constructors of an inductive, the inductive of a constructor, and the block of a recursor
(`RecursorVal.all`, which `Erasure.casesInfo?` reads). Reference: the closure property of
`MR E/ErasureFunction.v:1602 erase_global_deps`. -/
def DepClosed (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, (∀ x, ReadExpr decls ci x → ConstsIn (fun c => (findDecl decls c).isSome) x) ∧
    (∀ n ∈ ci.all, (findDecl decls n).isSome) ∧
    (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, (findDecl decls n).isSome) ∧
    (∀ cv, ci = .ctorInfo cv → (findDecl decls cv.induct).isSome) ∧
    (∀ r, ci = .recInfo r → ∀ n ∈ r.all, (findDecl decls n).isSome)

/-- The evaluation environment of `P` under the configuration's remapping (DV-12). -/
def evalEnvOf (view : EnvView) (cfg : ErasureConfig) (P : List ConstantInfo) : EvalEnv :=
  ⟨P, axiomatized view cfg⟩

/-- The view `#erase` reads agrees with `P` on `P`'s names. Reference: `Σ ∼_ext X`
(`abstract_env_ext_rel`, hypothesis of `MR E/ErasureFunctionProperties.v:657 erase_correct`). -/
def ViewAgrees (view : EnvView) (P : List ConstantInfo) : Prop :=
  ∀ ci ∈ P, view.find? ci.name = some ci

/-! ### The Phase I fragment, as a sufficient condition (lower bound of `hfrag`) -/

/-- A level without metavariables. -/
def LevelPlain : Level → Bool
  | .zero | .param _ => true
  | .succ l => LevelPlain l
  | .max a b | .imax a b => LevelPlain a && LevelPlain b
  | .mvar _ => false

/-- No free variable, metavariable, level metavariable or string literal; under `cfg.nat = .machine`
no Nat literal and none of `Nat.zero`, `Nat.succ`, `Int.ofNat`, `Int.negSucc`, `Nat.casesOn`,
`Int.casesOn`. -/
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

/-- A Nat literal occurs. -/
def HasNatLit : Expr → Bool
  | .lit (.natVal _) => true
  | .app f a => HasNatLit f || HasNatLit a
  | .lam _ t b _ | .forallE _ t b _ => HasNatLit t || HasNatLit b
  | .letE _ t v b _ => HasNatLit t || HasNatLit v || HasNatLit b
  | .mdata _ e | .proj _ _ e => HasNatLit e
  | _ => false

/-- `decls` contains what the pure traversal reads from `e`: the constants of `e` and of every read
expression, the members and constructors of every inductive block, the inductive of every
constructor, `T` and `T.rec` for every recognized `T.casesOn` (whose value is not read), and `Nat`
if a Nat literal is read. -/
def ReadClosed (decls : List ConstantInfo) (e : Expr) : Prop :=
  let inD := fun c => (findDecl decls c).isSome = true
  ConstsIn inD e ∧ (HasNatLit e → inD ``Nat) ∧
  ∀ ci ∈ decls, (∀ x, ReadExpr decls ci x → ConstsIn inD x ∧ (HasNatLit x → inD ``Nat)) ∧
    (∀ n ∈ ci.all, inD n) ∧ (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, inD n) ∧
    (∀ cv, ci = .ctorInfo cv → inD cv.induct) ∧
    (∀ iv, EvalEnv.casesOn? ⟨decls, fun _ => false⟩ ci.name = some iv →
      inD iv.name ∧ inD (mkRecName iv.name))

/-- A recursor of `decls`. -/
def IsRecursorIn (decls : List ConstantInfo) (c : Name) : Bool :=
  match findDecl decls c with
  | some (.recInfo _) => true
  | _ => false

/-- `x` mentions no recursor of `decls`: the pure traversal reaches a recursor only as the `T.rec`
of a recognized `T.casesOn`, whose value it does not read. -/
def RecFree (decls : List ConstantInfo) (x : Expr) : Prop :=
  ConstsIn (fun c => IsRecursorIn decls c = false) x

/-- An inductive of `decls` that the traversal may eliminate: its `casesOn` is recognized, or it has
one constructor with a field (so it may be projected). -/
def Eliminated (decls : List ConstantInfo) (iv : InductiveVal) : Prop :=
  (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ (.str iv.name "casesOn")).isSome ∨
    ∃ cn cv, iv.ctors = [cn] ∧ findDecl decls cn = some (.ctorInfo cv) ∧ 0 < cv.numFields

/-- A declaration of the closure is inside the first-phase fragment (Phase I): no quotient; a
recursor only as `T.rec` of a recognized `T.casesOn` of the closure (and never in a read
expression, `RecFree`); safe, with no `_unsafe_rec` companion (definitions and opaques: a `partial def` is an opaque with
one) and no `implemented_by` target;
inductives not nested, of a sort that is syntactically `Prop`, never zero, or, when the traversal
cannot eliminate them (`Eliminated`), not zero under every assignment (`PUnit`); when their
`casesOn` is recognized, without a constructor field that is an index of the constructor's type
(`indexFields`); no `@[extern]` constructor under `preferAxiom`. -/
def PhaseIDecl (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) :
    ConstantInfo → Prop
  | .quotInfo _ => False
  | .recInfo r => ∃ T iv, r.name = mkRecName T ∧
      EvalEnv.casesOn? ⟨decls, fun _ => false⟩ (.str T "casesOn") = some iv ∧
      (findDecl decls (.str T "casesOn")).isSome
  | .defnInfo d => d.safety = .safe ∧ view.find? (Compiler.mkUnsafeRecName d.name) = none ∧
      view.implementedBy? d.name = none
  | .opaqueInfo o => o.isUnsafe = false ∧ view.find? (Compiler.mkUnsafeRecName o.name) = none ∧
      view.implementedBy? o.name = none
  | .axiomInfo a => a.isUnsafe = false ∧ view.implementedBy? a.name = none
  | .thmInfo _ => True
  | .inductInfo iv => iv.isUnsafe = false ∧ iv.numNested = 0 ∧
      (∃ n u, arityShape iv.type = some (n, u) ∧ (u = .zero ∨ u.isNeverZero = true ∨
        (mayBeNonZero iv.levelParams u = true ∧ ¬ Eliminated decls iv))) ∧
      ((EvalEnv.casesOn? ⟨decls, fun _ => false⟩ (.str iv.name "casesOn")).isSome →
        ∀ cn ∈ iv.ctors, ∀ cv, findDecl decls cn = some (.ctorInfo cv) →
          (indexFields cv.numParams cv.type).all (·.isNone) = true)
  | .ctorInfo cv => cv.isUnsafe = false ∧ (cfg.1 = .preferAxiom → view.isExtern cv.name = false)

/-- Declarations that the λ□ environment holds as constants under their kername: definitions,
theorems, opaques and axioms (inductive types, constructors and recursors are inductive blocks or
are not emitted; quotients are outside Phase I). -/
def EmitsConst : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- No two λ□ global declarations of the closure share a kername (the block-name half of the
collision check of `Erasure.collectDeps`): distinct inductive blocks have distinct block names
(`mutualBlockKername`), and no block name is the kername of a closure constant held as a λ□
constant (`EmitsConst`). An inductive type's own kername is not a λ□ declaration, so a root-level
`T` with `toKername T = mutualBlockKername [T]` is no collision. -/
def BlockNamesInj (decls : List ConstantInfo) : Prop :=
  ∀ iv₁ iv₂, (∃ ci ∈ decls, ci = .inductInfo iv₁) → (∃ ci ∈ decls, ci = .inductInfo iv₂) →
    (mutualBlockKername iv₁.all = mutualBlockKername iv₂.all → iv₁.all = iv₂.all) ∧
    ∀ ci ∈ decls, EmitsConst ci = true → toKername ci.name ≠ mutualBlockKername iv₁.all

/-! ## 10. The erasure relation -/

/-- The λ□ block name of an inductive (`register_inductive`, `LeanToLambdaBox/Erasure.lean:447`,
`mutualBlockKername`, `LeanToLambdaBox/Basic.lean:47`). -/
def blockKername (iv : InductiveVal) : Kername :=
  mutualBlockKername iv.all

/-- The λ□ inductive of the Lean inductive `T`. -/
def IndIdOf (σ : EvalEnv) (T : Name) : Option InductiveId :=
  match findDecl σ.decls T with
  | some (.inductInfo iv) => (iv.all.idxOf? T).map fun j => ⟨blockKername iv, j⟩
  | _ => none

/-- A spine whose head is a constructor or a recognized `casesOn` constant. -/
def SpecialSpine (σ : EvalEnv) (e : Expr) : Prop :=
  ∃ c us, e.getAppFn = .const c us ∧
    ((∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ (σ.casesOn? c).isSome)

/-- The number of fields of a constructor of `σ`. -/
def ctorFields (σ : EvalEnv) (c : Name) : Option Nat :=
  match findDecl σ.decls c with
  | some (.ctorInfo cv) => some cv.numFields
  | _ => none

/-- The inductive `T` is in `Prop` in the Metalean environment. Reference: `isPropositional`
(`MR P/PCUICFirstorder.v:109`), on Metalean's level of the block. -/
def PropInductive {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (T : Name) : Prop :=
  ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts),
    B T = some (.ind η s) ∧ (E.get η).block.level = .zero

/-- `t` is a proof. Reference: `Is_proof` (`MR P/PCUICElimination.v:22`). -/
def IsProof {ζ : Metalean.Sigs} {ℓ n : Nat} (E : Metalean.Env ζ) (Γ : Metalean.Ctx ζ ℓ 0 n)
    (t : Metalean.Expr ζ ℓ n) : Prop :=
  ∃ T, E[Γ] ⊢ t : T ∧ E[Γ] ⊢ T : .prop

/-- Elimination of `T` is informative only through a subsingleton: whenever a constructor
application of `T` is a proof, `T` has at most one constructor and every field of the application
is a proof. Reference: `Subsingleton` (`MR P/PCUICElimination.v:45`), with Metalean's saturated
constructor nodes (fields `fds`, `recFds` after the parameters `ps`) in place of `mkApps (tConstruct
ind n u) args` and `skipn (ind_npars mdecl) args`, in the well-formed environment `E` and context
`Γ` (MetaRocq quantifies over well-formed extensions, which `E` is a fixed one of here; PCUIC typing
in `Γ` implies `wf_local Σ Γ`). -/
def Subsingleton {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (T : Name) : Prop :=
  ∀ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts),
    B T = some (.ind η s) →
    ∀ {ℓ n : Nat} (Γ : Metalean.Ctx ζ ℓ 0 n) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
      (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n)
      (fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n)
      (recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n),
      Metalean.EnvWF E → E[Γ] ⊢ ok → IsProof E Γ (.ctor η s c ls ps fds recFds) →
      ι.nctors s ≤ 1 ∧ (∀ f, IsProof E Γ (fds f)) ∧ ∀ f, IsProof E Γ (recFds f)

/-- Every field of a typed constructor node of `T` is erasable: the fields a reduced `casesOn`
(`Erases.casesReduced`) replaces by `□`. Reference: none (MetaRocq reduces `case` on proofs at run
time, `MR E/EWcbvEval.v:162`; DV-25). -/
def FieldsErasable {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (T : Name) : Prop :=
  ∀ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts),
    B T = some (.ind η s) →
    ∀ {ℓ n : Nat} (Γ : Metalean.Ctx ζ ℓ 0 n) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
      (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n)
      (fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n)
      (recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n),
      Metalean.EnvWF E → E[Γ] ⊢ ok → (∃ U, E[Γ] ⊢ .ctor η s c ls ps fds recFds : U) →
      (∀ f, IsErasable E Γ (fds f)) ∧ ∀ f, IsErasable E Γ (recFds f)

mutual
/-- The erasure relation. `σ` gives the atoms (erased only to `□`), the constructors and the
recognized `casesOn` constants. Constructor and `casesOn` spines are erased as a whole (λ□
`construct` applied to parameters, fields and extra arguments; λ□ `case` on the major with one
alternative per constructor, applied to the extra arguments); spines with fewer arguments than
the arity erase as their η-expansion (DV-23); a `casesOn` on a one-constructor inductive with
erasable fields may erase as its reduced form (`casesReduced`, as the eraser emits it when the
discriminant's sort may be zero).
Constructors of `Prop` inductives and eliminations of
inductives that are not subsingletons have no rule but `box`, as in MetaRocq. Reference: `MR E/Extract.v:88 erases`; MC §7.3, Fig. 18. -/
inductive Erases {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name)
    (σ : EvalEnv) : {n : Nat} → Metalean.Ctx ζ lps.length 0 n → MLCtx ζ lps.length n → Expr →
    LBTerm → Prop
  /-- `erases_tRel` (`MR E/Extract.v:89`). -/
  | bvar : Erases E B lps σ Γ Δ (.bvar i) (.bvar i)
  /-- `erases_tVar` (`:90`), the traversal's free variables (DV-13). -/
  | fvar : Erases E B lps σ Γ Δ (.fvar x) (.fvar x)
  /-- `erases_tLambda` (`:93`). -/
  | lam : TrM E B lps Γ Δ A A' → Erases E B lps σ (Γ.snoc A') (Δ.pushLam none) b b' →
      Erases E B lps σ Γ Δ (.lam x A b bi) (.lambda (binderNameOf x) b')
  /-- `erases_tLetIn` (`:96`). -/
  | letE : TrM E B lps Γ Δ v v₀ → Erases E B lps σ Γ Δ v v' →
      Erases E B lps σ Γ ((none, .vlet v₀) :: Δ) b b' →
      Erases E B lps σ Γ Δ (.letE x T v b nd) (.letIn (binderNameOf x) v' b')
  /-- `erases_tApp` (`:101`), heads other than constructors and `casesOn`. -/
  | app : ¬ SpecialSpine σ f → Erases E B lps σ Γ Δ f f' → Erases E B lps σ Γ Δ a a' →
      Erases E B lps σ Γ Δ (.app f a) (.app f' a')
  /-- `erases_tConst` (`:104`), for constants that are neither atoms nor special. -/
  | const : σ.isAtom c = false → specialArity σ c = none →
      Erases E B lps σ Γ Δ (.const c us) (.const (toKername c))
  /-- `erases_tConstruct` (`:106`, `~~ isPropositional`) under applications, parameters kept
  (DV-23). -/
  | ctor {as : List Expr} {as' : List LBTerm} :
      findDecl σ.decls c = some (.ctorInfo cv) → ¬ PropInductive E B cv.induct →
      IndIdOf σ cv.induct = some iid →
      cv.numParams + cv.numFields ≤ as.length → as.length = as'.length →
      (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → Erases E B lps σ Γ Δ a a') →
      Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) (mkApps (.construct iid cv.cidx []) as')
  /-- `erases_tCase` (`:111`, `Subsingleton`): `casesOn` with at least its arity, not reduced at
  erasure time (`CasesReduced`); parameters, motive and indices are dropped; alternatives under their
  fields' binders. -/
  | cases {pre alts extra : List Expr} {brs : List (List BinderName × LBTerm)} {extra' : List LBTerm} :
      σ.casesOn? c = some iv → ¬ CasesReduced iv us → Subsingleton E B iv.name →
      IndIdOf σ iv.name = some iid →
      pre.length = casesMajor iv → alts.length = iv.ctors.length →
      Erases E B lps σ Γ Δ maj maj' →
      brs.length = alts.length → (∀ (i : Nat) cn, iv.ctors[i]? = some cn → (ctorFields σ cn).isSome) →
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt → brs[i]? = some br →
        ctorFields σ cn = some k → ErasesAlt E B lps σ Γ Δ k alt br) →
      extra.length = extra'.length →
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases E B lps σ Γ Δ a a') →
      Erases E B lps σ Γ Δ (mkAppN (.const c us) (pre ++ [maj] ++ alts ++ extra).toArray)
        (mkApps (.case (iid, iv.numParams) maj' brs) extra')
  /-- The reduced form of a `casesOn` on a one-constructor inductive whose fields are erasable
  (`FieldsErasable`): the erased alternative applied to `□` for each field and to the extra
  arguments; the discriminant is not erased (`visitCases`, `LeanToLambdaBox/Erasure.lean:870`;
  `eval_iota_sing`, `MR E/EWcbvEval.v:162`, at erasure time; DV-25). The eraser emits it exactly when
  `CasesReduced` (the discriminant's sort may be zero); the rule does not read the `casesOn`'s
  levels, so it is stable under universe instantiation (`Erases.instLevels`). Constructors with
  index fields are not modelled (excluded from the fragment by `Erasure.collectDeps`). -/
  | casesReduced {pre extra : List Expr} {extra' : List LBTerm} :
      σ.casesOn? c = some iv → FieldsErasable E B iv.name →
      iv.ctors = [cn] → findDecl σ.decls cn = some (.ctorInfo cv) →
      (indexFields cv.numParams cv.type).all (·.isNone) = true →
      pre.length = casesMajor iv → Erases E B lps σ Γ Δ alt alt' →
      extra.length = extra'.length →
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases E B lps σ Γ Δ a a') →
      Erases E B lps σ Γ Δ (mkAppN (.const c us) (pre ++ [maj] ++ [alt] ++ extra).toArray)
        (mkApps alt' (List.replicate cv.numFields .box ++ extra'))
  /-- A constructor or `casesOn` spine with missing arguments erases as its η-expansion
  (`EvalEnv.etaSpine?`; `withAppEtaToMinArity`, DV-23). -/
  | eta {as : List Expr} : σ.etaSpine? c us as = some e' → Erases E B lps σ Γ Δ e' t →
      Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) t
  /-- `erases_tProj` (`:118`, `Subsingleton`), on a structure whose block is in `Prop` or whose
  declared sort is never zero: a block whose level may be both `0` and not `0` (sort `Sort u`) is
  not propositional in λ□, while its projection out of a proof erased to `□` would need λ□'s
  `projProp` (the `casesOn` counterpart is `¬ CasesReduced`). -/
  | proj : Subsingleton E B S → IndIdOf σ S = some iid → findDecl σ.decls S = some (.inductInfo iv) →
      (PropInductive E B S ∨ ∃ n u, arityShape iv.type = some (n, u) ∧ u.isNeverZero = true) →
      Erases E B lps σ Γ Δ e e' →
      Erases E B lps σ Γ Δ (.proj S i e) (.proj ⟨iid, iv.numParams, i⟩ e')
  /-- Nat literals under `cfg.nat = .peano` (`visitLiteral`). -/
  | litZero : IndIdOf σ ``Nat = some iid → Erases E B lps σ Γ Δ (.lit (.natVal 0)) (.construct iid 0 [])
  | litSucc : IndIdOf σ ``Nat = some iid → Erases E B lps σ Γ Δ (.lit (.natVal k)) t →
      Erases E B lps σ Γ Δ (.lit (.natVal (k + 1))) (.app (.construct iid 1 []) t)
  /-- Metadata is transparent. -/
  | mdata : Erases E B lps σ Γ Δ e e' → Erases E B lps σ Γ Δ (.mdata d e) e'
  /-- `erases_box` (`:140`). -/
  | box : ErasableS E B lps Γ Δ e → Erases E B lps σ Γ Δ e .box

/-- A `casesOn` alternative erased under its `k` field binders: leading λs are peeled, missing
ones η-introduced (`lambdaOrIntroToArity`, `LeanToLambdaBox/Erasure.lean:592`). Reference: the
branches of `MR E/Extract.v:111 erases_tCase`. -/
inductive ErasesAlt {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name)
    (σ : EvalEnv) : {n : Nat} → Metalean.Ctx ζ lps.length 0 n → MLCtx ζ lps.length n → Nat →
    Expr → List BinderName × LBTerm → Prop
  | done : Erases E B lps σ Γ Δ e t → ErasesAlt E B lps σ Γ Δ 0 e ([], t)
  | lam : TrM E B lps Γ Δ A A' → ErasesAlt E B lps σ (Γ.snoc A') (Δ.pushLam none) k b (ns, t) →
      ErasesAlt E B lps σ Γ Δ (k + 1) (.lam x A b bi) (binderNameOf x :: ns, t)
  | intro : (∀ x A b bi, e ≠ .lam x A b bi) → TrM E B lps Γ Δ e e' →
      E[Γ] ⊢ e' : .forallE A' B'' →
      ErasesAlt E B lps σ (Γ.snoc A') (Δ.pushLam none) k (.app (e.liftLooseBVars' 0 1) (.bvar 0))
        (ns, t) →
      ErasesAlt E B lps σ Γ Δ (k + 1) e (nm :: ns, t)
end

/-- The λ□ environment holds the erasure of `T`'s block: parameters, one body per type in `all`
order, constructors in order with their field counts, `propositional` iff the type is in `Prop`.
Reference: `MR E/Extract.v:282 erases_mutual_inductive_body`, `:276 erases_one_inductive_body`. -/
def ErasesInd {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (σ : EvalEnv)
    (lenv : GlobalDeclarations) (T : Name) : Prop :=
  ∃ iv, findDecl σ.decls T = some (.inductInfo iv) ∧
    ∀ j n, iv.all[j]? = some n → ∃ iv' mib ob, findDecl σ.decls n = some (.inductInfo iv') ∧
      lookupInd lenv ⟨blockKername iv, j⟩ = some (mib, ob) ∧ mib.npars = iv.numParams ∧
      ob.ctors.length = iv'.ctors.length ∧
      (∀ (k : Nat) cn, iv'.ctors[k]? = some cn → ∃ (cv : ConstructorVal) (cb : ConstructorBody), findDecl σ.decls cn = some (.ctorInfo cv) ∧
        ob.ctors[k]? = some cb ∧ cb.nargs = cv.numFields) ∧
      (ob.propositional = true ↔ PropInductive E B n)

/-- A constant's λ□ body erases its Lean value: none for declarations without value and for
remapped externs (DV-12), an erasure otherwise (no recursive constants in Metalean's fragment).
Reference: `MR E/Extract.v:264 erases_constant_body`. -/
def ErasesDecl {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (σ : EvalEnv)
    (ci : ConstantInfo) (cb : ConstantBody) : Prop :=
  match ci.value? (allowOpaque := true) with
  | none => cb.cst_body = none
  | some v => (σ.axiomatized ci = true ∧ cb.cst_body = none) ∨
    (σ.axiomatized ci = false ∧ ∃ b', cb.cst_body = some b' ∧
      Erases E B ci.levelParams σ .nil [] v b')

/-- The λ□ environment contains erasures of the erased term's dependencies, transitively, incl.
the inductive blocks of its constructors, cases and projections. Reference:
`MR E/Extract.v:306 erases_deps`. -/
inductive ErasesDeps {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (σ : EvalEnv)
    (lenv : GlobalDeclarations) : LBTerm → Prop
  | box : ErasesDeps E B σ lenv .box
  | bvar : ErasesDeps E B σ lenv (.bvar i)
  | fvar : ErasesDeps E B σ lenv (.fvar x)
  | lambda : ErasesDeps E B σ lenv b → ErasesDeps E B σ lenv (.lambda na b)
  | letIn : ErasesDeps E B σ lenv v → ErasesDeps E B σ lenv b →
      ErasesDeps E B σ lenv (.letIn na v b)
  | app : ErasesDeps E B σ lenv f → ErasesDeps E B σ lenv a → ErasesDeps E B σ lenv (.app f a)
  /-- `erases_deps_tConst` (`:324`), indexed by the source constant (DV-14). -/
  | const : findDecl σ.decls c = some ci → lookupConst lenv (toKername c) = some cb →
      ErasesDecl E B σ ci cb → (∀ b, cb.cst_body = some b → ErasesDeps E B σ lenv b) →
      ErasesDeps E B σ lenv (.const (toKername c))
  /-- `erases_deps_tConstruct` (`:329`). -/
  | construct : IndIdOf σ T = some iid → ErasesInd E B σ lenv T →
      (∀ a ∈ args, ErasesDeps E B σ lenv a) → ErasesDeps E B σ lenv (.construct iid c args)
  /-- `erases_deps_tCase` (`:334`). -/
  | case : IndIdOf σ T = some iid → ErasesInd E B σ lenv T → ErasesDeps E B σ lenv d →
      (∀ br ∈ brs, ErasesDeps E B σ lenv br.2) → ErasesDeps E B σ lenv (.case (iid, np) d brs)
  /-- `erases_deps_tProj` (`:343`). -/
  | proj : IndIdOf σ T = some p.indType → ErasesInd E B σ lenv T → ErasesDeps E B σ lenv d →
      ErasesDeps E B σ lenv (.proj p d)

end EraseProof
