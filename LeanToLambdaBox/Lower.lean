import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.FixMetatheory
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.ElimBody
import LeanToLambdaBox.Output

/-!
# `Lower` — the term-level λ□ → λ□ pass relation

`Lower Γ t t'` relates a term over the *specification* environment `Γ` to the term the
shipping eraser emits for it. It carries the compilation steps the source-level erasure
relation cannot state: the eliminator-to-`case` translation and the block-level fixpoint.

Fifteen arms: eleven congruence, `elimApp`, `fixConst`, `fixBody`, `fixEta`. The relation is indexed
by `Γ` and by nothing else — no source term, no typing context, no run state — which is what
keeps it a statement about λ□ alone; `doc/rules-Lower.md` carries the arm-by-arm anchors.

It is a relation and **not a function**: at a block member the constant has two images
(`const`, `fixConst`) and so does the member's body (`fixBody`, `fixEta`, the wrapper F-ETA
registers). `LowerFixFixture.lower_not_functional` checks the second pair; no consumer reads
`Lower` as functional, and the inversion kit is keyed on the target's shape rather than on
uniqueness.

Constructor introduction is **not** here: a constructor constant erases to `.construct iid k
[]` by `Erases.ctor` and its arguments arrive through `Erases.app`, so the pass sees a
`.construct` node already and the `construct`/`app` congruence arms relate it. Neither
η-expansion is here either; what they covered is a coverage restriction of the fragment, and
the eraser-side finding is `F-ETA2` in `doc/rework/03-DEV-FIX.md`.

Block premises are inlined into the three fix arms (the kernel rejects a structure premise
that mentions the inductive) and packaged afterwards as `LowerBlock`, read through
`Lower.fixConst'`/`Lower.fixBody'`/`Lower.fixEta'`. List premises are in the indexed form `hlen` plus
`∀ i, i < …`, since `List.Forall₂` as a premise is a nested-inductive occurrence.

`SpecGrow` is here too: the growth of the specification environment the pass survives, with
`Lower.specGrow` its monotonicity law. The law needs more than the term's own references —
`SpecGrowFixture.specGrow_needs_declaredEnv` is the counterexample — so it asks for
`ConstsDeclaredEnv`, λ□ well-formedness of the environment's δ column.

`ConstToFVar` and `CloseConstAt` are here because `LowerBlock.hcl` needs them; the rest of
the fixpoint closure is `LowerFix.lean`. Box-freedom (`NoBox`), the λ-headedness transports
off `LowerBlock.hfl` and the source-side inversion kit are here because they are facts about
`Lower` and its targets. The inversion kit takes **no** environment-side guard: what excludes
a `.fix` image at a non-λ source is the block's own `hfl`.

Two refutations are deleted with their subjects. `lower_correct_needs_ctorEta_guard`
exhibited a `ctorEta` pair whose source evaluates to a value the target cannot reach;
`lower_correct_needs_elimBody_head` refuted the pass simulation at an `elimEta` derivation
with an `ElimBody`-shaped head, at the empty environment and with every design guard proved.
Both arms and `ElimHeadOf`'s second disjunct are deleted, so neither statement has a
subject.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Environment queries -/

/-- The λ□ inductive body the eraser emits for the block of `iid`, at the resolution the
target semantics reads it: `constructorArity` reads `npars` and the per-constructor field
counts.

The `propositional` flag is **not** here. `Erasure.register_inductive` sets it to
`isPropositionalArity inf.type` (`Erasure.lean:389`), and `Erasure.recursorRealizer`
(`Erasure.lean:430`) reaches that call at `Eq`/`And`/`False`, so `= false` is not a fact about
emitted output. MetaRocq states the flag as an equality against the declared arity
(`erases_one_inductive_body`, `../metarocq/erasure/theories/Extract.v:276`); that equation
needs the model environment, which this relation does not carry, so it is stated at
`ErasesEnv.blocks` and `IndCovered.block`, and the `= false` the ι and projection arms read is
`IndNotPropositional`, derived there from `InformativeInd`. -/
def IndBodyOf (iid : InductiveId) (np : Nat) (nfs : List Nat)
    (mib : MutualInductiveBody) : Prop :=
  mib.npars = np ∧ ∃ oib, mib.bodies[iid.idx]? = some oib ∧
    oib.ctors.map (·.nargs) = nfs

/-- The body `iid` selects in `mib` is not propositional: what `isPropositionalInductive`
reads before `WcbvEval.iota` and `WcbvEval.proj` fire (`Semantics/Eval.lean:147`, `:183`).
Carried beside `IndBodyOf` rather than inside it, because it holds of the inductives an
elimination is *at*, not of every inductive a run registers —
`Erasability.propositional_false_of_informative` is what its producers discharge it with. -/
def IndNotPropositional (iid : InductiveId) (mib : MutualInductiveBody) : Prop :=
  ∃ oib, mib.bodies[iid.idx]? = some oib ∧ oib.propositional = false

/-- `kn` is declared in `Γ` as an eliminator constant, **together with its block**: its body
is one of the two canonical `ElimBody` shapes for `iid` at `np` parameters, `dp` dropped
arguments and field arities `nfs`, and `iid`'s block is declared with those same numbers and
is not propositional. The second conjunct is what puts the emitted `.case` node's arity data
in scope on the target, where `constructorArity` and `isPropositionalInductive` read it. -/
def ElimDecl (Γ : GlobalDeclarations) (kn : Kername) (iid : InductiveId) (np dp : Nat)
    (nfs : List Nat) : Prop :=
  (∃ body, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) ∧
    ElimBody iid np dp nfs body) ∧
  (∃ mib, LBTerm.envLookup Γ iid.mutualBlockName = some (.inductiveDecl mib) ∧
    IndBodyOf iid np nfs mib ∧ IndNotPropositional iid mib)

/-- `kn` is declared in `Γ` with body `b`. -/
def DefnDecl (Γ : GlobalDeclarations) (kn : Kername) (b : LBTerm) : Prop :=
  LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩)

/-- `kn` is a key the pass consumes rather than emits: an eliminator constant, whose
occurrences become `.case` nodes and whose declaration is pruned. It guards `const` and
`fixConst`, since a pruned key would leave the target with a dangling reference and
`ElimDecl` implies `DefnDecl`. A constructor constant is **not** a runtime key: the pass
never sees one, because `Erases.ctor` already emits the `.construct` node. -/
def RuntimeKey (Γ : GlobalDeclarations) (kn : Kername) : Prop :=
  ∃ iid np dp nfs, ElimDecl Γ kn iid np dp nfs

/-- Every constant declared in `Γ` has a closed body. The specification environment holds
top-level bodies, so this is a fact about it, and it is what makes the two fix arms
commute with `shift` and `subst`. -/
def ClosedBodies (Γ : GlobalDeclarations) : Prop :=
  ∀ kn b, DefnDecl Γ kn b → LBClosed b 0

/-- Every constant declared in `Γ` has a body free of free variables. Independent of
`ClosedBodies`, whose `LBClosed` clause at an `.fvar` node is `True`
(`noFVar_needs_fvarFree`), and it is what makes the pass commute with abstraction: the two
fix arms build their target out of `Γ`'s declared bodies, so a stray variable there would be
abstracted on the target and nowhere on the source. -/
def FVarFreeBodies (Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (b : LBTerm) (x : FVarId), DefnDecl Γ kn b → ¬ hasFVar x b

/-- Closedness survives one new entry, given it of whatever body the entry carries. A
body-less entry and a block entry discharge the premise vacuously. -/
theorem closedBodies_cons {Γ : GlobalDeclarations} {k : Kername} {d : GlobalDecl}
    (h : ClosedBodies Γ) (hnew : ∀ b, d = .constantDecl ⟨some b⟩ → LBClosed b 0) :
    ClosedBodies ((k, d) :: Γ) := by
  intro kn b hb
  rw [DefnDecl, LBTerm.envLookup] at hb
  split at hb
  · exact hnew b (Option.some.inj hb)
  · exact h kn b hb

/-- `closedBodies_cons`' twin for the free-variable clause. -/
theorem fvarFreeBodies_cons {Γ : GlobalDeclarations} {k : Kername} {d : GlobalDecl}
    (h : FVarFreeBodies Γ)
    (hnew : ∀ (b : LBTerm) (x : FVarId), d = .constantDecl ⟨some b⟩ → ¬ hasFVar x b) :
    FVarFreeBodies ((k, d) :: Γ) := by
  intro kn b x hb
  rw [DefnDecl, LBTerm.envLookup] at hb
  split at hb
  · exact hnew b x (Option.some.inj hb)
  · exact h kn b x hb

/-- **Two eliminator declarations at one key agree.** `LBTerm.envLookup` is a function, so
both readings hold one body, and that body fixes the data: `mkElimBody` and `mkElimBodyRec`
are each injective in `(iid, np, dp, nfs)` and are never equal to one another — one is a
`.case` under a λ-telescope, the other a `.fix`. -/
theorem ElimDecl.uniq {Γ : GlobalDeclarations} {kn : Kername} {iid iid' : InductiveId}
    {np dp np' dp' : Nat} {nfs nfs' : List Nat}
    (h : ElimDecl Γ kn iid np dp nfs) (h' : ElimDecl Γ kn iid' np' dp' nfs') :
    iid = iid' ∧ np = np' ∧ dp = dp' ∧ nfs = nfs' := by
  -- a λ-telescope of anonymous binders over a non-λ body determines its length and body
  have hlam : ∀ (n n' : Nat) (b b' : LBTerm), isLambda b = false → isLambda b' = false →
      mkLambdas (List.replicate n .anon) b = mkLambdas (List.replicate n' .anon) b' →
      n = n' ∧ b = b' := by
    intro n
    induction n with
    | zero =>
        intro n' b b' hb hb' he
        cases n' with
        | zero => exact ⟨rfl, he⟩
        | succ m =>
            rw [List.replicate_succ] at he
            rw [show mkLambdas (BinderName.anon :: List.replicate m .anon) b'
              = .lambda .anon (mkLambdas (List.replicate m .anon) b') from rfl] at he
            have he₀ : b = LBTerm.lambda .anon (mkLambdas (List.replicate m .anon) b') := he
            rw [he₀] at hb
            exact Bool.noConfusion hb
    | succ n ih =>
        intro n' b b' hb hb' he
        cases n' with
        | zero =>
            rw [List.replicate_succ] at he
            rw [show mkLambdas (BinderName.anon :: List.replicate n .anon) b
              = .lambda .anon (mkLambdas (List.replicate n .anon) b) from rfl] at he
            have he₀ : LBTerm.lambda .anon (mkLambdas (List.replicate n .anon) b) = b' := he
            rw [← he₀] at hb'
            exact Bool.noConfusion hb'
        | succ m =>
            rw [List.replicate_succ, List.replicate_succ] at he
            injection he with _ he
            obtain ⟨hn, hbb⟩ := ih m b b' hb hb' he
            exact ⟨by omega, hbb⟩
  -- the alternative list determines the field arities
  have halts : ∀ (ms ms' : List Nat), elimAlts ms = elimAlts ms' → ms = ms' := by
    intro ms
    induction ms with
    | nil =>
        intro ms' he
        cases ms' with
        | nil => rfl
        | cons m ms' => exact absurd he (by simp [elimAlts])
    | cons m ms ih =>
        intro ms' he
        cases ms' with
        | nil => exact absurd he (by simp [elimAlts])
        | cons m' ms' =>
            rw [elimAlts, elimAlts] at he
            injection he with hhd htl
            injection hhd with hns _
            have hm : m = m' := by simpa using congrArg List.length hns
            subst hm; rw [ih ms' htl]
  have hml : ∀ (i : InductiveId) (p d : Nat) (fs : List Nat),
      isLambda (mkElimBody i p d fs) = true := by
    intro i p d fs
    rw [mkElimBody, show d + 1 + fs.length = (d + fs.length) + 1 by omega,
      List.replicate_succ]
    rfl
  have hcases : ∀ (i i' : InductiveId) (p p' d d' : Nat) (fs fs' : List Nat),
      mkElimBody i p d fs = mkElimBody i' p' d' fs' →
      i = i' ∧ p = p' ∧ d = d' ∧ fs = fs' := by
    intro i i' p p' d d' fs fs' he
    obtain ⟨hn, hb⟩ := hlam _ _ _ _ rfl rfl he
    injection hb with hip _ halt
    have hfs := halts _ _ halt
    subst hfs
    injection hip with hi hp
    exact ⟨hi, hp, by omega, rfl⟩
  obtain ⟨⟨body, hlk, hb⟩, -⟩ := h
  obtain ⟨⟨body', hlk', hb'⟩, -⟩ := h'
  have hbody : body = body' := by
    have he := hlk.symm.trans hlk'
    injection he with he; injection he with he; injection he with he
    exact Option.some.inj he
  subst hbody
  rcases hb.shape with he | he <;> rcases hb'.shape with he' | he'
  · exact hcases _ _ _ _ _ _ _ _ (he.symm.trans he')
  · exact absurd (he.symm.trans he' ▸ hml iid np dp nfs) (by rw [mkElimBodyRec]; simp [isLambda])
  · exact absurd (he'.symm.trans he ▸ hml iid' np' dp' nfs')
      (by rw [mkElimBodyRec]; simp [isLambda])
  · have hee := he.symm.trans he'
    rw [mkElimBodyRec, mkElimBodyRec] at hee
    injection hee with hdefs _
    injection hdefs with hfd _
    exact hcases _ _ _ _ _ _ _ _ (congrArg FixDef.body hfd)

/-! ## Spine and telescope helpers -/

/-- The `n` de Bruijn indices of a freshly pushed telescope, outermost first:
`bvarsDesc n = [.bvar (n-1), …, .bvar 0]`. `ElimBody.fieldArgs` is the same run, written by
recursion; `fieldArgs_eq` is the bridge. -/
def bvarsDesc (n : Nat) : List LBTerm := (List.range n).reverse.map LBTerm.bvar

/-! ## `ConstToFVar` — block constants as fix variables -/

/-- Replace `.const kns[j]` by `.fvar ids[j]`, a congruence everywhere else. A `.fix`
node maps to itself: the source side of `Lower` declares no block member as a `.fix`, and
a nested one comes from another block, whose members are none of `kns`. -/
inductive ConstToFVar (kns : List Kername) (ids : List FVarId) : LBTerm → LBTerm → Prop where
  | box : ConstToFVar kns ids .box .box
  | bvar (i : Nat) : ConstToFVar kns ids (.bvar i) (.bvar i)
  | fvar (x : FVarId) : ConstToFVar kns ids (.fvar x) (.fvar x)
  | prim (p : PrimVal) : ConstToFVar kns ids (.prim p) (.prim p)
  | hit {j : Nat} {kn : Kername} {x : FVarId} (hkn : kns[j]? = some kn) (hx : ids[j]? = some x) :
      ConstToFVar kns ids (.const kn) (.fvar x)
  | miss {kn : Kername} (h : kn ∉ kns) : ConstToFVar kns ids (.const kn) (.const kn)
  | lambda {n n' : BinderName} {b b' : LBTerm} (h : ConstToFVar kns ids b b') :
      ConstToFVar kns ids (.lambda n b) (.lambda n' b')
  | letIn {n n' : BinderName} {v v' b b' : LBTerm} (hv : ConstToFVar kns ids v v')
      (hb : ConstToFVar kns ids b b') :
      ConstToFVar kns ids (.letIn n v b) (.letIn n' v' b')
  | app {f f' a a' : LBTerm} (hf : ConstToFVar kns ids f f') (ha : ConstToFVar kns ids a a') :
      ConstToFVar kns ids (.app f a) (.app f' a')
  | proj {p : ProjectionInfo} {e e' : LBTerm} (h : ConstToFVar kns ids e e') :
      ConstToFVar kns ids (.proj p e) (.proj p e')
  | construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → ConstToFVar kns ids args[i]! args'[i]!) :
      ConstToFVar kns ids (.construct iid k args) (.construct iid k args')
  | «case» {ip : InductiveId × Nat} {d d' : LBTerm}
      {alts alts' : List (List BinderName × LBTerm)}
      (hd : ConstToFVar kns ids d d')
      (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → ConstToFVar kns ids (alts[i]!).2 (alts'[i]!).2) :
      ConstToFVar kns ids (.case ip d alts) (.case ip d' alts')
  | fix (defs : List (@FixDef LBTerm)) (i : Nat) :
      ConstToFVar kns ids (.fix defs i) (.fix defs i)

/-- The block closure of one body: rewrite the block's constants to its fix variables,
then abstract those variables with `closeFix`, which is exactly `mkDef`'s fold. -/
def CloseConstAt (kns : List Kername) (ids : List FVarId) (t u : LBTerm) : Prop :=
  ∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'

/-! ### The block closure has no free variable

`ConstToFVar` introduces only the block's own identifiers and `closeFix` abstracts exactly
those, so a block body built from a variable-free declaration is variable-free at **every**
variable. That is what makes the two fix arms of `Lower` replay under abstraction. -/

/-- `ConstToFVar` introduces only the block's own identifiers. -/
theorem constToFVar_not_hasFVar {kns : List Kername} {ids : List FVarId} {x : FVarId} :
    ∀ {b u : LBTerm}, ConstToFVar kns ids b u → ¬ hasFVar x b → x ∉ ids → ¬ hasFVar x u := by
  intro b u h
  induction h with
  | box | bvar | prim | miss => exact fun hb _ => hb
  | fvar y => exact fun hb _ => hb
  | @hit j kn y hkn hy =>
      intro _ hx hc
      simp only [hasFVar_fvar] at hc
      subst hc
      exact hx (List.mem_of_getElem? hy)
  | lambda _ ih => exact fun hb hx => ih hb hx
  | letIn _ _ ihv ihb =>
      intro hb hx
      simp only [hasFVar_letIn, not_or] at hb ⊢
      exact ⟨ihv hb.1 hx, ihb hb.2 hx⟩
  | app _ _ ihf iha =>
      intro hb hx
      simp only [hasFVar_app, not_or] at hb ⊢
      exact ⟨ihf hb.1 hx, iha hb.2 hx⟩
  | proj _ ih => exact fun hb hx => ih hb hx
  | @construct iid k args args' hlen _ ih =>
      intro hb hx
      simp only [hasFVar_construct, hasFVarArgs_iff, not_exists, not_and] at hb ⊢
      intro t ht hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      have hi' : i < args.length := by omega
      refine ih i hi' ?_ hx ?_
      · rw [getElem!_pos args i hi']
        exact fun hcc => hb args[i] (List.getElem_mem hi') hcc
      · rw [getElem!_pos args' i hi]
        exact hc
  | @«case» ip d d' alts alts' _ hlen hn _ ihd ihb =>
      intro hb hx
      simp only [hasFVar_case, not_or] at hb ⊢
      refine ⟨ihd hb.1 hx, ?_⟩
      simp only [hasFVarAlts_iff, not_exists, not_and] at hb ⊢
      intro a ha hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' : i < alts.length := by omega
      refine ihb i hi' ?_ hx ?_
      · rw [getElem!_pos alts i hi']
        exact fun hcc => hb.2 alts[i] (List.getElem_mem hi') hcc
      · rw [getElem!_pos alts' i hi]
        exact hc
  | fix defs i => exact fun hb _ => hb

/-- The block closure of a variable-free body is variable-free at every variable, the
block's own identifiers included, since `closeFix` abstracts exactly those. -/
theorem closeConstAt_not_hasFVar {kns : List Kername} {ids : List FVarId} {b u : LBTerm}
    {x : FVarId} (h : CloseConstAt kns ids b u) (hb : ¬ hasFVar x b) : ¬ hasFVar x u := by
  obtain ⟨t', hc, rfl⟩ := h
  intro hocc
  obtain ⟨hx, hocc'⟩ := hasFVar_closeFix_of hocc
  exact constToFVar_not_hasFVar hc hb hx hocc'

/-- The `.fix` node a block builds has no free variable at all, given variable-free
declared bodies for its members. -/
theorem fixNode_not_hasFVar {kns : List Kername} {bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {x : FVarId} {j : Nat}
    (hd : defs.length = kns.length)
    (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
    (hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!) :
    ¬ hasFVar x (LBTerm.fix defs j) := by
  simp only [hasFVar_fix, hasFVarDefs_iff, not_exists, not_and]
  intro d hdm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdm
  have hik : i < kns.length := by omega
  rw [show defs[i] = defs[i]! from (getElem!_pos defs i hi).symm]
  exact closeConstAt_not_hasFVar (hcl i hik) (hnf i hik)

/-- Abstraction is therefore the identity on a block's `.fix` node. -/
theorem toBvar_fixNode {kns : List Kername} {bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {x : FVarId} {j lvl : Nat}
    (hd : defs.length = kns.length)
    (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
    (hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!) :
    toBvar x lvl (LBTerm.fix defs j) = LBTerm.fix defs j :=
  toBvar_eq_of_not_hasFVar x lvl _ (fixNode_not_hasFVar hd hcl hnf)

/-! ## The relation -/

mutual

/-- The pass relation, fifteen arms. `Lower Γ t t'` says `t'` is a λ□ term the eraser
may emit for the specification term `t` over `Γ`. Deliberately non-deterministic at a block
member, twice over: at the member's constant, where `const` and `fixConst` both apply, and
at the member's body, where `fixBody` and `fixEta` both apply. `LowerFixFixture`'s
`lower_not_functional` is the second one machine-checked. -/
inductive Lower (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop where
  | box : Lower Γ .box .box
  | bvar (i : Nat) : Lower Γ (.bvar i) (.bvar i)
  | fvar (x : FVarId) : Lower Γ (.fvar x) (.fvar x)
  | prim (p : PrimVal) : Lower Γ (.prim p) (.prim p)
  /-- A constant that is not a runtime key survives. Non-deterministic at a block member,
      where `fixConst` relates the same constant to the block's `.fix` node. -/
  | const {kn : Kername} (h : ¬ RuntimeKey Γ kn) : Lower Γ (.const kn) (.const kn)
  | lambda {n n' : BinderName} {b b' : LBTerm} (h : Lower Γ b b') :
      Lower Γ (.lambda n b) (.lambda n' b')
  | letIn {n n' : BinderName} {v v' b b' : LBTerm} (hv : Lower Γ v v') (hb : Lower Γ b b') :
      Lower Γ (.letIn n v b) (.letIn n' v' b')
  | app {f f' a a' : LBTerm} (hf : Lower Γ f f') (ha : Lower Γ a a') :
      Lower Γ (.app f a) (.app f' a')
  | proj {p : ProjectionInfo} {e e' : LBTerm} (h : Lower Γ e e') :
      Lower Γ (.proj p e) (.proj p e')
  | construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
      Lower Γ (.construct iid k args) (.construct iid k args')
  /-- Branch arities are preserved: `iota_red` reads an alternative's binder count. -/
  | «case» {ip : InductiveId × Nat} {d d' : LBTerm}
      {alts alts' : List (List BinderName × LBTerm)}
      (hd : Lower Γ d d')
      (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → Lower Γ (alts[i]!).2 (alts'[i]!).2) :
      Lower Γ (.case ip d alts) (.case ip d' alts')
  /-- A saturated eliminator application becomes a `.case` node. The `dp` arguments before
      the discriminant are dropped, the minors are peeled into alternatives, and any
      over-application rides outside the node. The head is a `.const kn` whose declaration
      `ElimDecl` exhibits together with `iid`'s block. -/
  | elimApp {kn : Kername} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
      {pre : List LBTerm} {disc disc' : LBTerm} {minors : List LBTerm}
      {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
      (hh : ElimDecl Γ kn iid np dp nfs)
      (hlen : pre.length = dp)
      (hmlen : minors.length = nfs.length)
      (halen : alts.length = nfs.length)
      (hmin : ∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!)
      (hdisc : Lower Γ disc disc')
      (hxlen : extra'.length = extra.length)
      (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
      Lower Γ (LBTerm.mkApps (.const kn) (pre ++ disc :: minors ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')
  /-- A block member's constant relates to the block's `.fix` node: the call site.
      `hnk` is what keeps a `.fix` image off an eliminator constant — `ElimDecl` implies
      `DefnDecl`, so nothing else does. The remaining premises are `LowerBlock`'s fields,
      inlined; read them through `Lower.fixConst'`. -/
  | fixConst {kn : Kername} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hids : ids.Nodup) (hilen : ids.length = kns.length)
      (hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!)
      (hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true)
      (hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!)
      (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hnk : ¬ RuntimeKey Γ kn) (hj : kns[j]? = some kn) :
      Lower Γ (.const kn) (.fix defs j)
  /-- The member's specification body relates to the same `.fix` node: the value side,
      which the δ step needs once the environment has unfolded the constant. Read it
      through `Lower.fixBody'`. -/
  | fixBody {b : LBTerm} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hids : ids.Nodup) (hilen : ids.length = kns.length)
      (hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!)
      (hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true)
      (hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!)
      (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hj : bs[j]? = some b) (hjl : j < defs.length) :
      Lower Γ b (.fix defs j)
  /-- The member's specification body relates to the **η-expansion** of the same `.fix`
      node, beside `fixBody`'s bare one: `Erasure.visitMutual` registers
      `Erasure.etaExpandFix defs j` (`Erasure.lean:1316`), and `Erasure.mkDef` pins
      `principalArgIdx = 0`, so the wrapper is one binder — MetaRocq's `eta_fixpoint` at
      `1 + rarg = 1`. The premises are `fixBody`'s verbatim. Read it through
      `Lower.fixEta'`, whose target is the closed shape `LBTerm.etaFix defs j`.

      The binder name is free, as it is at `lambda`: every λ the relation targets must
      survive the renaming `ConstToFVar.lambda` performs, and pinning it to `.anon` here
      falsifies `Lower.constToFix`. -/
  | fixEta {b : LBTerm} {n : BinderName} {kns : List Kername} {bs bs' : List LBTerm}
      {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hids : ids.Nodup) (hilen : ids.length = kns.length)
      (hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!)
      (hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true)
      (hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!)
      (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hj : bs[j]? = some b) (hjl : j < defs.length) :
      Lower Γ b (.lambda n (.app (.fix defs j) (.bvar 0)))

/-- Branch peeling: a minor's λ-chain becomes an alternative's binder list. Names are
free; only their number — the field arity `iota_red` reads — is pinned. -/
inductive LowerAlt (Γ : GlobalDeclarations) :
    Nat → LBTerm → (List BinderName × LBTerm) → Prop where
  | done {m b : LBTerm} (h : Lower Γ m b) : LowerAlt Γ 0 m ([], b)
  | lam {nf : Nat} {n n' : BinderName} {m : LBTerm} {alt : List BinderName × LBTerm}
      (h : LowerAlt Γ nf m alt) :
      LowerAlt Γ (nf + 1) (.lambda n m) (n' :: alt.1, alt.2)

end

/-- The pointwise lift of `LowerAlt` over a block's field arities. -/
def LowerAlts (Γ : GlobalDeclarations) (nfs : List Nat) (minors : List LBTerm)
    (alts : List (List BinderName × LBTerm)) : Prop :=
  minors.length = nfs.length ∧ alts.length = nfs.length ∧
    ∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!

/-- The premises the two fix arms share, packaged. `ids` is **block-shared** — one list
for the whole block, as `visitMutual` mints it — because the freshness clause the fix
unfolding needs is against every `.fix defs j`. `hrarg` pins the emitted principal
argument index to `0`, which is the only value `mkDef` produces. -/
structure LowerBlock (Γ : GlobalDeclarations) (kns : List Kername) (bs bs' : List LBTerm)
    (ids : List FVarId) (defs : List (@FixDef LBTerm)) : Prop where
  hb : bs.length = kns.length
  hb' : bs'.length = kns.length
  hd : defs.length = kns.length
  hnd : kns.Nodup
  hids : ids.Nodup
  hilen : ids.length = kns.length
  hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!
  hrarg : ∀ d ∈ defs, d.principalArgIdx = 0
  hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!
  /-- Every emitted definition's body is a λ. This is `LBWfPeregrine.fixLambda`'s clause
      at this block: `visitMutual` erases each member's compiler value and closes it with
      `mkDef`, and λ□'s own `tFix` well-formedness rejects anything else. The source side
      is not asserted twice — it is `LowerBlock.lambda_of_fixLambda`, which reads this
      field. -/
  hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true
  hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!
  hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body

/-- `Lower.fixConst` read through `LowerBlock`. -/
theorem Lower.fixConst' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {kn : Kername}
    (h : LowerBlock Γ kns bs bs' ids defs) (hnk : ¬ RuntimeKey Γ kn)
    (hj : kns[j]? = some kn) :
    Lower Γ (.const kn) (.fix defs j) :=
  .fixConst h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hfl h.hlow
    h.hcl hnk hj

/-- `Lower.fixBody` read through `LowerBlock`. -/
theorem Lower.fixBody' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {b : LBTerm}
    (h : LowerBlock Γ kns bs bs' ids defs) (hj : bs[j]? = some b) (hjl : j < defs.length) :
    Lower Γ b (.fix defs j) :=
  .fixBody h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hfl h.hlow
    h.hcl hj hjl

/-- `Lower.fixEta` read through `LowerBlock`, at the emitted binder name: the target is the
closed shape `LBTerm.etaFix defs j`, which is what `Erasure.visitMutual` registers. -/
theorem Lower.fixEta' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {b : LBTerm}
    (h : LowerBlock Γ kns bs bs' ids defs) (hj : bs[j]? = some b) (hjl : j < defs.length) :
    Lower Γ b (LBTerm.etaFix defs j) :=
  .fixEta h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hfl h.hlow
    h.hcl hj hjl

/-- `Lower.elimApp` read through `LowerAlts`. -/
theorem Lower.elimApp' {Γ : GlobalDeclarations} {kn : Kername} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {pre : List LBTerm} {disc disc' : LBTerm}
    {minors : List LBTerm} {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
    (hh : ElimDecl Γ kn iid np dp nfs) (hlen : pre.length = dp)
    (hmin : LowerAlts Γ nfs minors alts) (hdisc : Lower Γ disc disc')
    (hxlen : extra'.length = extra.length)
    (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
    Lower Γ (LBTerm.mkApps (.const kn) (pre ++ disc :: minors ++ extra))
            (LBTerm.mkApps (.case (iid, np) disc' alts) extra') :=
  .elimApp hh hlen hmin.1 hmin.2.1 hmin.2.2 hdisc hxlen hx


/-! ## Indexed-list plumbing

The list premises are indexed (`hlen` plus `∀ i, i < …`), so the proofs move between
`l[i]!` and `∈ l` constantly; these four lemmas are that move. -/

/-- A `getElem!` at a valid index is a member. -/
theorem Lower.getElem!_mem {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! ∈ l := by
  rw [getElem!_pos l i h]; exact List.getElem_mem h

/-- A member is a `getElem!` at a valid index. -/
theorem Lower.mem_getElem! {α : Type} [Inhabited α] {l : List α} {a : α} (h : a ∈ l) :
    ∃ i, i < l.length ∧ l[i]! = a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, getElem!_pos l i hi⟩

/-- `getElem!` commutes with `List.map` at a valid index. -/
theorem Lower.getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β)
    (l : List α) (i : Nat) (h : i < l.length) : (l.map f)[i]! = f l[i]! := by
  rw [getElem!_pos (l.map f) i (by simpa using h), getElem!_pos l i h, List.getElem_map]

/-- An index-wise property of a mapped list, read as a membership property. -/
theorem Lower.forall_mem_map {α β : Type} [Inhabited α] [Inhabited β] {f : α → β}
    {l : List α} {P : β → Prop} (h : ∀ i, i < l.length → P (f l[i]!)) :
    ∀ b ∈ l.map f, P b := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
  exact h i hi

/-! ## Spine, telescope and `bvarsDesc` laws -/

/-- `shift` distributes over an application spine. -/
theorem LBTerm.shift_mkApps (d c : Nat) (f : LBTerm) (args : List LBTerm) :
    LBTerm.shift d c (LBTerm.mkApps f args)
      = LBTerm.mkApps (LBTerm.shift d c f) (args.map (LBTerm.shift d c)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simpa [LBTerm.mkApps, LBTerm.shift] using ih (.app f a)

/-- `subst` distributes over an application spine. -/
theorem LBTerm.subst_mkApps (s : LBTerm) (d : Nat) (f : LBTerm) (args : List LBTerm) :
    LBTerm.subst s d (LBTerm.mkApps f args)
      = LBTerm.mkApps (LBTerm.subst s d f) (args.map (LBTerm.subst s d)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simpa [LBTerm.mkApps, LBTerm.subst] using ih (.app f a)

/-- Abstraction distributes over an application spine, which is what the `elimApp` arm of
`Lower.abstract` needs. -/
theorem toBvar_mkApps (x : FVarId) (lvl : Nat) :
    ∀ (l : List LBTerm) (f : LBTerm),
      toBvar x lvl (LBTerm.mkApps f l) = LBTerm.mkApps (toBvar x lvl f) (l.map (toBvar x lvl))
  | [], f => rfl
  | a :: as, f => by
      simpa [LBTerm.mkApps, toBvar] using toBvar_mkApps x lvl as (.app f a)

/-- Two shifts with disjoint roles commute: pushing `n` binders in at `b` moves the outer
cutoff `c` up by `n`. -/
theorem LBTerm.shift_shift_comm (d n b c : Nat) (h : b ≤ c) (t : LBTerm) :
    LBTerm.shift d (c + n) (LBTerm.shift n b t) = LBTerm.shift n b (LBTerm.shift d c t) := by
  induction t using LBTerm.recData generalizing b c with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      rw [LBTerm.shift_bvar n b i]
      by_cases hib : i ≥ b
      · rw [if_pos hib, LBTerm.shift_bvar, LBTerm.shift_bvar]
        by_cases hic : i ≥ c
        · rw [if_pos (by omega), if_pos hic, LBTerm.shift_bvar, if_pos (by omega)]
          exact congrArg LBTerm.bvar (by omega)
        · rw [if_neg (by omega), if_neg hic, LBTerm.shift_bvar, if_pos hib]
      · rw [if_neg hib, LBTerm.shift_bvar, LBTerm.shift_bvar, if_neg (by omega),
          if_neg (by omega), LBTerm.shift_bvar, if_neg hib]
  | hlam nm b' ih =>
      have e : c + n + 1 = (c + 1) + n := by omega
      simp only [LBTerm.shift, e, ih (b + 1) (c + 1) (by omega)]
  | hletIn nm v b' ihv ihb =>
      have e : c + n + 1 = (c + 1) + n := by omega
      simp only [LBTerm.shift, e, ihv b c h, ihb (b + 1) (c + 1) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.shift, ihf b c h, iha b c h]
  | hproj p e ih => simp only [LBTerm.shift, ih b c h]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha b c h
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map, List.map_map, ihd b c h]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      have e : c + n + a.1.length = (c + a.1.length) + n := by omega
      rw [e, iha a ha (b + a.1.length) (c + a.1.length) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.shift, LBTerm.shiftDefs_eq_map, List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      have e : c + n + defs.length = (c + defs.length) + n := by omega
      rw [e, ih a ha (b + defs.length) (c + defs.length) (by omega)]

/-- `bvarsDesc n` has `n` entries. -/
@[simp] theorem bvarsDesc_length (n : Nat) : (bvarsDesc n).length = n := by
  simp [bvarsDesc]

/-- Every entry of `bvarsDesc n` is a de Bruijn index below `n`. -/
theorem bvarsDesc_mem {n : Nat} {t : LBTerm} (h : t ∈ bvarsDesc n) :
    ∃ i, i < n ∧ t = .bvar i := by
  simp only [bvarsDesc, List.mem_map, List.mem_reverse, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

/-- A telescope's own arguments are closed at its length. -/
theorem lbClosed_bvarsDesc {n : Nat} : ∀ t ∈ bvarsDesc n, LBClosed t n := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simpa using hi

/-- Shifting above a telescope leaves its own arguments alone. -/
theorem shift_bvarsDesc {n c : Nat} (h : n ≤ c) (d : Nat) :
    (bvarsDesc n).map (LBTerm.shift d c) = bvarsDesc n := by
  refine List.map_congr_left ?_ |>.trans (List.map_id _)
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simp only [id, LBTerm.shift]
  rw [if_neg (by omega)]

/-- Substituting above a telescope leaves its own arguments alone. -/
theorem subst_bvarsDesc {n d : Nat} (h : n ≤ d) (s : LBTerm) :
    (bvarsDesc n).map (LBTerm.subst s d) = bvarsDesc n := by
  refine List.map_congr_left ?_ |>.trans (List.map_id _)
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simp only [id, LBTerm.subst]
  rw [if_pos (by omega)]

/-- `closeFix` at base `0` abstracts a closed body into one closed at the block's width. -/
theorem lbClosed_closeFix {t : LBTerm} (ids : List FVarId) (h : LBClosed t 0) :
    LBClosed (closeFix ids 0 t) ids.length := by
  rw [closeFix, closeFixFold_eq_foldl]
  exact lbClosed_foldl_zipIdx ids h

/-- Rewriting block constants to fix variables preserves closedness: both `.const` and
`.fvar` bind no index. -/
theorem ConstToFVar.closed {kns : List Kername} {ids : List FVarId} {t t' : LBTerm}
    (h : ConstToFVar kns ids t t') {k : Nat} (hc : LBClosed t k) : LBClosed t' k := by
  induction h generalizing k with
  | box | bvar | fvar | prim | hit | miss | fix => exact hc
  | lambda _ ih => exact ih hc
  | letIn _ _ ihv ihb => exact ⟨ihv hc.1, ihb hc.2⟩
  | app _ _ ihf iha => exact ⟨ihf hc.1, iha hc.2⟩
  | proj _ ih => exact ih hc
  | construct hlen _ ih =>
      rw [LBClosed_construct, LBClosedArgs_iff] at *
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) (hc _ (Lower.getElem!_mem (by omega)))
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      rw [LBClosed_case, LBClosedAlts_iff] at *
      refine ⟨ihd hc.1, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hi' : i < alts.length := by omega
      rw [hn i hi']
      exact ihb i hi' (hc.2 _ (Lower.getElem!_mem hi'))


/-! ## Closedness -/

/-- A block's `.fix` node is closed once every lowered body is: `hcl` writes each
definition body as `closeFix ids 0` of a `ConstToFVar` image, and `closeFix` at base `0`
closes exactly the block's own width. -/
theorem lbClosed_fix_of_block {kns : List Kername} {bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat}
    (hd : defs.length = kns.length) (hilen : ids.length = kns.length)
    (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
    (hbs : ∀ i, i < kns.length → LBClosed bs'[i]! 0) (k : Nat) :
    LBClosed (LBTerm.fix defs j) k := by
  rw [LBClosed_fix, LBClosedDefs_iff]
  intro fd hfd
  obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hfd
  have hik : i < kns.length := by omega
  obtain ⟨t', hct, heq⟩ := hcl i hik
  rw [heq]
  exact (lbClosed_closeFix ids (hct.closed (hbs i hik))).mono (by omega)

/-- The η-expansion of a closed `.fix` node is closed: its only extra content is the binder
its own `.bvar 0` fills. Stated at a free binder name, since `Lower.fixEta`'s is free and
`LBTerm.etaFix defs j` is the `.anon` instance. -/
theorem lbClosed_etaFix {defs : List (@FixDef LBTerm)} {j k : Nat} {nm : BinderName}
    (h : ∀ m, LBClosed (LBTerm.fix defs j) m) :
    LBClosed (.lambda nm (.app (.fix defs j) (.bvar 0))) k :=
  ⟨h (k + 1), Nat.succ_pos k⟩

/-- The η-expansion of a block's node has no free variable either, and abstraction is
therefore the identity on it. -/
theorem etaFix_not_hasFVar {kns : List Kername} {bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {x : FVarId} {j : Nat} {nm : BinderName}
    (hd : defs.length = kns.length)
    (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
    (hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!) :
    ¬ hasFVar x (.lambda nm (.app (.fix defs j) (.bvar 0))) := by
  simp only [hasFVar_lambda, hasFVar_app, hasFVar_bvar, or_false]
  exact fixNode_not_hasFVar hd hcl hnf

/-- `Lower` preserves closedness at every bound, given closed specification bodies: the
three fix arms read their definitions off `Γ`, and nothing else in the relation invents an
index. -/
theorem Lower.closed {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) {s t : LBTerm}
    (h : Lower Γ s t) : ∀ k, LBClosed s k → LBClosed t k := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ k, LBClosed m k → LBClosed alt.2 (k + alt.1.length)) with
  | box | bvar | fvar | prim | const => exact fun _ hc => hc
  | lambda _ ih => exact fun k hc => ih (k + 1) hc
  | letIn _ _ ihv ihb => exact fun k hc => ⟨ihv k hc.1, ihb (k + 1) hc.2⟩
  | app _ _ ihf iha => exact fun k hc => ⟨ihf k hc.1, iha k hc.2⟩
  | proj _ ih => exact fun k hc => ih k hc
  | @construct iid ci args args' hlen _ ih =>
      intro k hc
      rw [LBClosed_construct, LBClosedArgs_iff] at *
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) k (hc _ (Lower.getElem!_mem (by omega)))
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro k hc
      rw [LBClosed_case, LBClosedAlts_iff] at *
      refine ⟨ihd k hc.1, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hi' : i < alts.length := by omega
      rw [hn i hi']
      exact ihb i hi' _ (hc.2 _ (Lower.getElem!_mem hi'))
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      _ hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro k hc
      have hargs := LBClosed.mkApps_inv hc
      have halts : LBClosedAlts alts k := by
        rw [LBClosedAlts_iff]
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
        have hi' : i < nfs.length := by omega
        have hm : minors[i]! ∈ minors := Lower.getElem!_mem (by omega)
        exact ihmin i hi' k (hargs _ (List.mem_append_left extra
          (List.mem_append_right pre (List.mem_cons_of_mem _ hm))))
      have hhead : LBClosed (LBTerm.case (iid, np) disc' alts) k :=
        ⟨ihd k (hargs disc (by simp)), halts⟩
      refine LBClosed.mkApps hhead ?_
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hm : extra[i]! ∈ extra := Lower.getElem!_mem (by omega)
      exact ihx i (by omega) k (hargs _ (List.mem_append_right _ hm))
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ _ hcl _ hj ih =>
      intro k _
      exact lbClosed_fix_of_block hdl hilen hcl
        (fun i hi => ih i hi 0 (hΓ _ _ (hdecl i hi))) k
  | @fixBody b kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ _ hcl hj hjl ih =>
      intro k _
      exact lbClosed_fix_of_block hdl hilen hcl
        (fun i hi => ih i hi 0 (hΓ _ _ (hdecl i hi))) k
  | @fixEta b n kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ _ hcl hj hjl ih =>
      intro k _
      exact lbClosed_etaFix (fun m => lbClosed_fix_of_block hdl hilen hcl
        (fun i hi => ih i hi 0 (hΓ _ _ (hdecl i hi))) m)
  | done _ ih =>
      rename_i k hc
      simpa using ih k hc
  | @lam nf n n' m alt _ ih =>
      rename_i k hc
      have hb := ih (k + 1) hc
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb


/-! ## Commutation with the de Bruijn operations -/

/-- `getElem?` pins both the index and the `getElem!`. -/
theorem Lower.getElem!_of_getElem? {α : Type} [Inhabited α] {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length ∧ l[i]! = a := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · refine ⟨hi, ?_⟩
    rw [getElem!_pos l i hi]
    rw [List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  · rw [List.getElem?_eq_none hi] at h
    exact absurd h (by simp)

/-- Pushing a telescope's shift past an outer one, on a whole argument list. -/
theorem map_shift_shift_comm (d n c : Nat) (l : List LBTerm) :
    (l.map (LBTerm.shift n 0)).map (LBTerm.shift d (c + n))
      = (l.map (LBTerm.shift d c)).map (LBTerm.shift n 0) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  exact LBTerm.shift_shift_comm d n 0 c (Nat.zero_le c) a

/-- `Lower` commutes with `shift`: the pass never reads a de Bruijn index, and its two
fix arms rest on declarations that are closed. -/
theorem Lower.shift_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {s t : LBTerm} (h : Lower Γ s t) :
    ∀ d c, Lower Γ (LBTerm.shift d c s) (LBTerm.shift d c t) := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ d c,
      LowerAlt Γ nf (LBTerm.shift d c m) (alt.1, LBTerm.shift d (c + alt.1.length) alt.2)) with
  | box => exact fun _ _ => .box
  | bvar i => intro d c; simp only [LBTerm.shift]; split <;> exact .bvar _
  | fvar x => exact fun _ _ => .fvar x
  | prim p => exact fun _ _ => .prim p
  | const hk => exact fun _ _ => .const hk
  | lambda _ ih => exact fun d c => .lambda (ih d (c + 1))
  | letIn _ _ ihv ihb => exact fun d c => .letIn (ihv d c) (ihb d (c + 1))
  | app _ _ ihf iha => exact fun d c => .app (ihf d c) (iha d c)
  | proj _ ih => exact fun d c => .proj (ih d c)
  | @construct iid ci args args' hlen _ ih =>
      intro d c
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
      refine .construct (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d c
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro d c
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map]
      refine .case (ihd d c) (by simp [hlen]) ?_ ?_
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi d (c + (alts[i]!).1.length)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d c
      rw [LBTerm.shift_mkApps, LBTerm.shift_mkApps]
      simp only [List.map_append, List.map_cons, LBTerm.shift, LBTerm.shiftAlts_eq_map]
      refine .elimApp hh (by simp [hlen]) (by simp [hmlen]) (by simp [halen]) ?_ (ihd d c)
        (by simp [hxlen]) ?_
      · intro i hi
        rw [Lower.getElem!_map _ _ i (by omega), Lower.getElem!_map _ _ i (by omega)]
        exact ihmin i hi d c
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
        exact ihx i hi d c
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hnk hj ih =>
      intro d c
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.shift d c (LBTerm.const kn) = .const kn from rfl,
        hfx.shift_eq (Nat.zero_le c) d]
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hnk hj
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro d c
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at this
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [hbcl.shift_eq (Nat.zero_le c) d, hfx.shift_eq (Nat.zero_le c) d]
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro d c
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at this
      have hfx : LBClosed (LBTerm.lambda nm (.app (.fix defs j) (.bvar 0))) 0 :=
        lbClosed_etaFix (fun m => lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) m)
      rw [hbcl.shift_eq (Nat.zero_le c) d, hfx.shift_eq (Nat.zero_le c) d]
      exact .fixEta hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | done _ ih =>
      rename_i d c
      simpa using LowerAlt.done (ih d c)
  | @lam nf n n' m alt _ ih =>
      rename_i d c
      have hih := ih d (c + 1)
      simp only [LBTerm.shift, List.length_cons]
      have e : c + (alt.1.length + 1) = (c + 1) + alt.1.length := by omega
      rw [e]
      exact .lam hih


/-- Pushing a telescope's shift past a substitution, on a whole argument list. -/
theorem map_subst_shift_comm (a : LBTerm) (d n : Nat) (l : List LBTerm) :
    (l.map (LBTerm.shift n 0)).map (LBTerm.subst a (d + n))
      = (l.map (LBTerm.subst a d)).map (LBTerm.shift n 0) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  exact LBTerm.subst_shift_comm a 0 d n (d + n) (Nat.zero_le d) rfl x

/-- `Lower` commutes with substitution, the substituted terms being related themselves.
This is the law the β, ζ and ι steps of a forward simulation consume. -/
theorem Lower.subst_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {a a' : LBTerm} (ha : Lower Γ a a') {s t : LBTerm} (h : Lower Γ s t) :
    ∀ d, Lower Γ (LBTerm.subst a d s) (LBTerm.subst a' d t) := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ d,
      LowerAlt Γ nf (LBTerm.subst a d m)
        (alt.1, LBTerm.subst a' (d + alt.1.length) alt.2)) with
  | box => exact fun _ => .box
  | bvar i =>
      intro d
      simp only [LBTerm.subst]
      split
      · exact .bvar _
      · split
        · exact Lower.shift_comm hΓ ha d 0
        · exact .bvar _
  | fvar x => exact fun _ => .fvar x
  | prim p => exact fun _ => .prim p
  | const hk => exact fun _ => .const hk
  | lambda _ ih => exact fun d => .lambda (ih (d + 1))
  | letIn _ _ ihv ihb => exact fun d => .letIn (ihv d) (ihb (d + 1))
  | app _ _ ihf iha => exact fun d => .app (ihf d) (iha d)
  | proj _ ih => exact fun d => .proj (ih d)
  | @construct iid ci args args' hlen _ ih =>
      intro d
      simp only [LBTerm.subst, LBTerm.substArgs_eq_map]
      refine .construct (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro d
      simp only [LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .case (ihd d) (by simp [hlen]) ?_ ?_
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a' (d + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a (d + x.1.length) x.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a' (d + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a (d + x.1.length) x.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi (d + (alts[i]!).1.length)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d
      rw [LBTerm.subst_mkApps, LBTerm.subst_mkApps]
      simp only [List.map_append, List.map_cons, LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .elimApp hh (by simp [hlen]) (by simp [hmlen]) (by simp [halen]) ?_ (ihd d)
        (by simp [hxlen]) ?_
      · intro i hi
        rw [Lower.getElem!_map _ _ i (by omega), Lower.getElem!_map _ _ i (by omega)]
        exact ihmin i hi d
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
        exact ihx i hi d
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hnk hj ih =>
      intro d
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.subst a d (LBTerm.const kn) = .const kn from rfl,
        hfx.subst_eq (Nat.zero_le d) a']
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hnk hj
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro d
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have hb0 := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at hb0
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [hbcl.subst_eq (Nat.zero_le d) a, hfx.subst_eq (Nat.zero_le d) a']
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro d
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have hb0 := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at hb0
      have hfx : LBClosed (LBTerm.lambda nm (.app (.fix defs j) (.bvar 0))) 0 :=
        lbClosed_etaFix (fun m => lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) m)
      rw [hbcl.subst_eq (Nat.zero_le d) a, hfx.subst_eq (Nat.zero_le d) a']
      exact .fixEta hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | done _ ih =>
      rename_i d
      simpa using LowerAlt.done (ih d)
  | @lam nf n n' m alt _ ih =>
      rename_i d
      have hih := ih (d + 1)
      simp only [LBTerm.subst, List.length_cons]
      have e : d + (alt.1.length + 1) = (d + 1) + alt.1.length := by omega
      rw [e]
      exact .lam hih


/-! ## The pass commutes with abstraction

`Erasure.mkLambda`, `mkLetIn` and `mkAlt` close a binder with `abstract x = toBvar x 0`, and
`Erases.uninstantiate` closes the erasure image with the same operator, so the pass factor
has to follow. It does at twelve of the fourteen arms by congruence; at `fixConst` and
`fixBody` the target is built out of `Γ`'s own declared bodies, and abstracting a variable
occurring in one of them would demand a block the declaration does not declare. The side
condition is therefore `FVarFreeBodies`, and it is necessary: `noFVar_needs_fvarFree` and
`abstract_needs_fvarFree` refute both laws with `ClosedBodies` granted. -/

/-- **`Lower` introduces no free variable**, given variable-free declared bodies. Both fix
arms go through `fixNode_not_hasFVar`, so neither uses its induction hypothesis on the
block; that is why this is proved before, and independently of, `Lower.abstract`. -/
theorem Lower.noFVar {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {x : FVarId}
    {s t : LBTerm} (h : Lower Γ s t) : ¬ hasFVar x s → ¬ hasFVar x t := by
  have hma : ∀ (l : List LBTerm) (f : LBTerm),
      hasFVar x (LBTerm.mkApps f l) ↔ hasFVar x f ∨ ∃ a ∈ l, hasFVar x a := by
    intro l
    induction l with
    | nil => intro f; simp [LBTerm.mkApps]
    | cons a as ih =>
        intro f
        rw [show LBTerm.mkApps f (a :: as) = LBTerm.mkApps (.app f a) as from rfl, ih]
        simp only [hasFVar_app, List.mem_cons]
        constructor
        · rintro ((hf | ha) | ⟨y, hy, hxy⟩)
          · exact .inl hf
          · exact .inr ⟨a, .inl rfl, ha⟩
          · exact .inr ⟨y, .inr hy, hxy⟩
        · rintro (hf | ⟨y, (rfl | hy), hxy⟩)
          · exact .inl (.inl hf)
          · exact .inl (.inr hxy)
          · exact .inr ⟨y, hy, hxy⟩
  induction h using Lower.rec
    (motive_2 := fun _nf m alt _ => ¬ hasFVar x m → ¬ hasFVar x alt.2) with
  | box | bvar | fvar | prim | const => exact id
  | lambda _ ih => exact ih
  | letIn _ _ ihv ihb =>
      intro hh
      simp only [hasFVar_letIn, not_or] at hh ⊢
      exact ⟨ihv hh.1, ihb hh.2⟩
  | app _ _ ihf iha =>
      intro hh
      simp only [hasFVar_app, not_or] at hh ⊢
      exact ⟨ihf hh.1, iha hh.2⟩
  | proj _ ih => exact ih
  | @construct iid k args args' hlen _ ih =>
      intro hh
      simp only [hasFVar_construct, hasFVarArgs_iff, not_exists, not_and] at hh ⊢
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) (hh _ (Lower.getElem!_mem (by omega)))
  | @«case» ip d d' alts alts' _ hlen hn _ ihd ihb =>
      intro hh
      simp only [hasFVar_case, not_or, hasFVarAlts_iff, not_exists, not_and] at hh ⊢
      refine ⟨ihd hh.1, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ihb i (by omega) (hh.2 _ (Lower.getElem!_mem (by omega)))
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro hnf hc
      have hargs : ∀ a ∈ pre ++ disc :: minors ++ extra, ¬ hasFVar x a := by
        intro a ha hca
        exact hnf ((hma _ _).mpr (.inr ⟨a, ha, hca⟩))
      rcases (hma extra' _).mp hc with hcc | ⟨a, ha, hca⟩
      · rw [hasFVar_case] at hcc
        rcases hcc with hcc | hcc
        · exact ihd (hargs disc (by simp)) hcc
        · rw [hasFVarAlts_iff] at hcc
          obtain ⟨a, ha, hca⟩ := hcc
          obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
          exact ihmin i (by omega) (hargs _ (List.mem_append_left extra
            (List.mem_append_right pre
              (List.mem_cons_of_mem _ (Lower.getElem!_mem (by omega)))))) hca
      · obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
        exact ihx i (by omega)
          (hargs _ (List.mem_append_right _ (Lower.getElem!_mem (by omega)))) hca
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hnk hj ih =>
      intro _
      exact fixNode_not_hasFVar hdl hcl (fun i hi => ih i hi (hfv _ _ _ (hdecl i hi)))
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro _
      exact fixNode_not_hasFVar hdl hcl (fun i hi => ih i hi (hfv _ _ _ (hdecl i hi)))
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro _
      exact etaFix_not_hasFVar hdl hcl (fun i hi => ih i hi (hfv _ _ _ (hdecl i hi)))
  | done _ ih => rename_i hh; exact ih hh
  | @lam nf n n' m alt _ ih => rename_i hh; exact ih hh

/-- **`Lower` commutes with abstraction.** No level side condition: `toBvar` never reads or
rewrites an existing de Bruijn index, so unlike `Lower.shift_comm` this needs neither a
cutoff bound nor `ClosedBodies`. The two fix arms do not recurse — the block's `.fix` node is
inert under `toBvar` (`toBvar_fixNode`), read off `Lower.noFVar` at the block's own bodies. -/
theorem Lower.abstract {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {s t : LBTerm}
    (h : Lower Γ s t) (x : FVarId) : ∀ lvl, Lower Γ (toBvar x lvl s) (toBvar x lvl t) := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ lvl,
      LowerAlt Γ nf (toBvar x lvl m) (alt.1, toBvar x (lvl + alt.1.length) alt.2)) with
  | box => exact fun _ => .box
  | bvar i => exact fun _ => .bvar i
  | fvar y =>
      intro lvl
      cases hyx : (y == x)
      · rw [show toBvar x lvl (LBTerm.fvar y) = .fvar y from by simp [toBvar, hyx]]
        exact .fvar y
      · rw [show toBvar x lvl (LBTerm.fvar y) = .bvar lvl from by simp [toBvar, hyx]]
        exact .bvar lvl
  | prim p => exact fun _ => .prim p
  | const hk => exact fun _ => .const hk
  | lambda _ ih => exact fun lvl => .lambda (ih (lvl + 1))
  | letIn _ _ ihv ihb => exact fun lvl => .letIn (ihv lvl) (ihb (lvl + 1))
  | app _ _ ihf iha => exact fun lvl => .app (ihf lvl) (iha lvl)
  | proj _ ih => exact fun lvl => .proj (ih lvl)
  | @construct iid ci args args' hlen _ ih =>
      intro lvl
      simp only [toBvar, toBvarArgs_eq_map]
      refine .construct (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi lvl
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro lvl
      simp only [toBvar, toBvarAlts_eq_map]
      refine .case (ihd lvl) (by simp [hlen]) ?_ ?_
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, toBvar x (lvl + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, toBvar x (lvl + a.1.length) a.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, toBvar x (lvl + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, toBvar x (lvl + a.1.length) a.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi (lvl + (alts[i]!).1.length)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro lvl
      rw [toBvar_mkApps, toBvar_mkApps]
      simp only [List.map_append, List.map_cons, toBvar, toBvarAlts_eq_map]
      refine .elimApp hh (by simp [hlen]) (by simp [hmlen]) (by simp [halen]) ?_ (ihd lvl)
        (by simp [hxlen]) ?_
      · intro i hi
        rw [Lower.getElem!_map _ _ i (by omega), Lower.getElem!_map _ _ i (by omega)]
        exact ihmin i hi lvl
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
        exact ihx i hi lvl
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hnk hj _ih =>
      intro lvl
      have hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]! :=
        fun i hi => Lower.noFVar hfv (hlow i hi) (hfv _ _ _ (hdecl i hi))
      rw [show toBvar x lvl (LBTerm.const kn) = .const kn from rfl,
        toBvar_fixNode hdl hcl hnf]
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hnk hj
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl _ih =>
      intro lvl
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]! :=
        fun i hi => Lower.noFVar hfv (hlow i hi) (hfv _ _ _ (hdecl i hi))
      have hbfv : ¬ hasFVar x b := by
        have hb0 := hfv _ _ x (hdecl j hjk)
        rwa [hjeq] at hb0
      rw [toBvar_eq_of_not_hasFVar x lvl b hbfv, toBvar_fixNode hdl hcl hnf]
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl _ih =>
      intro lvl
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hnf : ∀ i, i < kns.length → ¬ hasFVar x bs'[i]! :=
        fun i hi => Lower.noFVar hfv (hlow i hi) (hfv _ _ _ (hdecl i hi))
      have hbfv : ¬ hasFVar x b := by
        have hb0 := hfv _ _ x (hdecl j hjk)
        rwa [hjeq] at hb0
      rw [toBvar_eq_of_not_hasFVar x lvl b hbfv,
        toBvar_eq_of_not_hasFVar x lvl _ (etaFix_not_hasFVar (nm := nm) hdl hcl hnf)]
      exact .fixEta hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow hcl hj hjl
  | done _ ih =>
      rename_i lvl
      simpa using LowerAlt.done (ih lvl)
  | @lam nf n n' m alt _ ih =>
      rename_i lvl
      have hih := ih (lvl + 1)
      simp only [toBvar, List.length_cons]
      have e : lvl + (alt.1.length + 1) = (lvl + 1) + alt.1.length := by omega
      rw [e]
      exact .lam hih

/-- The alternative half of the same law: an alternative's binders shift the abstraction
level by the field count. Obtained by induction on that count rather than by re-running the
fourteen `Lower` arms. -/
theorem LowerAlt.abstract {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {nf : Nat}
    {m : LBTerm} {alt : List BinderName × LBTerm} (h : LowerAlt Γ nf m alt) (x : FVarId) :
    ∀ lvl, LowerAlt Γ nf (toBvar x lvl m) (alt.1, toBvar x (lvl + alt.1.length) alt.2) := by
  induction nf generalizing m alt with
  | zero =>
      cases h with
      | done hl => intro lvl; simpa using LowerAlt.done (Lower.abstract hfv hl x lvl)
  | succ n ih =>
      cases h with
      | @lam _ n₀ n' m₀ alt₀ h₀ =>
          intro lvl
          have hih := ih h₀ (lvl + 1)
          simp only [toBvar, List.length_cons]
          have e : lvl + (alt₀.1.length + 1) = (lvl + 1) + alt₀.1.length := by omega
          rw [e]
          exact .lam hih

/-! ### `FVarFreeBodies` is not a formality

A one-member block whose declared body carries a stray free variable satisfies
`ClosedBodies` — `LBClosed`'s clause at an `.fvar` node is `True` — and refutes both laws.
So neither `ClosedBodies` nor the well-formedness predicates built on it imply the new
clause, and the two laws genuinely need it. -/

namespace FVarFixture

/-- The one member's kername. -/
def kn : Kername := { mp := .MPfile [], id := "cxA" }

/-- The stray variable the declared body carries. -/
def y : FVarId := ⟨.mkSimple "cxY"⟩

/-- The block identifier `visitMutual` would mint. -/
def z : FVarId := ⟨.mkSimple "cxV0"⟩

/-- The declared body: λ-headed, closed, and mentioning `y`. -/
def b : LBTerm := .lambda (.named "x") (.fvar y)

def kns : List Kername := [kn]
def ids : List FVarId := [z]
def defs : List (@FixDef LBTerm) := [{ name := .named "d0", body := b }]

/-- The one-entry specification environment. -/
def cxEnv : GlobalDeclarations := [(kn, .constantDecl ⟨some b⟩)]

/-- The member is declared. -/
theorem decl : DefnDecl cxEnv kn b := rfl

/-- Only the one body is declared. -/
theorem cxEnv_body_eq {k : Kername} {b' : LBTerm} (h : DefnDecl cxEnv k b') : b' = b := by
  rw [DefnDecl, cxEnv, LBTerm.envLookup] at h
  split at h
  · injection h with h; injection h with h; injection h with h
    exact (Option.some.inj h).symm
  · rw [LBTerm.envLookup] at h
    exact absurd h (by simp)

/-- The environment satisfies `ClosedBodies`: `LBClosed` says nothing about free variables. -/
theorem closed_cxEnv : ClosedBodies cxEnv := by
  intro k b' h
  rw [cxEnv_body_eq h]
  exact trivial

/-- …but not `FVarFreeBodies`. -/
theorem not_fvarFree : ¬ FVarFreeBodies cxEnv := fun H => H kn b y decl rfl

/-- The key is not a runtime key: the environment declares no block at all. -/
theorem not_rk : ¬ RuntimeKey cxEnv kn := by
  rintro ⟨iid, np, dp, nfs, -, mib, hmib, -⟩
  rw [cxEnv, LBTerm.envLookup] at hmib
  split at hmib
  · exact absurd hmib (by simp)
  · rw [LBTerm.envLookup] at hmib
    exact absurd hmib (by simp)

/-- The one-member block. -/
theorem blk : LowerBlock cxEnv kns [b] [b] ids defs where
  hb := rfl
  hb' := rfl
  hd := rfl
  hnd := List.Pairwise.cons (fun a ha => nomatch ha) .nil
  hids := List.Pairwise.cons (fun a ha => nomatch ha) .nil
  hilen := rfl
  hfresh := by
    intro x hx i hi
    match i, hi with
    | 0, _ =>
        have hxz : x = z := by
          rcases hx with _ | ⟨_, hx⟩
          · rfl
          · nomatch hx
        subst hxz
        exact fun hc => absurd (congrArg Lean.FVarId.name hc) (by decide)
  hrarg := by
    intro d hd
    cases hd with
    | head => rfl
    | tail _ hd => nomatch hd
  hdecl := by
    intro i hi
    match i, hi with
    | 0, _ => exact decl
  hfl := by
    intro j hj
    match j, hj with
    | 0, _ => rfl
  hlow := by
    intro i hi
    match i, hi with
    | 0, _ => exact .lambda (.fvar y)
  hcl := by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨b, .lambda (.fvar y), rfl⟩

/-- The `fixConst` arm fires, and its target carries the stray variable. -/
theorem lower_const : Lower cxEnv (.const kn) (.fix defs 0) :=
  Lower.fixConst' blk not_rk rfl

/-- **`Lower.noFVar` is false without `FVarFreeBodies`**, `ClosedBodies` granted: the
target of the `fixConst` arm carries a variable the source `.const` node does not. -/
theorem noFVar_needs_fvarFree :
    ¬ (∀ (Γ : GlobalDeclarations) (x : FVarId) (s t : LBTerm),
        ClosedBodies Γ → Lower Γ s t → ¬ hasFVar x s → ¬ hasFVar x t) := fun H =>
  H cxEnv y (.const kn) (.fix defs 0) closed_cxEnv lower_const id (Or.inl rfl)

/-- **`Lower.abstract` is false without `FVarFreeBodies`**, `ClosedBodies` granted:
abstracting the stray variable under the block's own binders manufactures an out-of-range
de Bruijn index, and `Lower` preserves closedness, so no arm relates the abstracted pair. -/
theorem abstract_needs_fvarFree :
    ¬ (∀ (Γ : GlobalDeclarations) (s t : LBTerm), ClosedBodies Γ → Lower Γ s t →
        ∀ (x : FVarId) (lvl : Nat), Lower Γ (toBvar x lvl s) (toBvar x lvl t)) := by
  intro H
  have h := H cxEnv (.const kn) (.fix defs 0) closed_cxEnv lower_const y 0
  rw [show toBvar y 0 (LBTerm.const kn) = .const kn from rfl] at h
  have hcl : LBClosed (toBvar y 0 (LBTerm.fix defs 0)) 0 :=
    Lower.closed closed_cxEnv h 0 trivial
  rw [show toBvar y 0 (LBTerm.fix defs 0)
        = LBTerm.fix [{ name := .named "d0", body := .lambda (.named "x") (.bvar 2) }] 0
      from rfl, LBClosed_fix, LBClosedDefs_iff] at hcl
  have hbv := hcl { name := .named "d0", body := .lambda (.named "x") (.bvar 2) } (by simp)
  simp only [LBClosed_lambda, LBClosed_bvar, List.length_singleton] at hbv
  omega

end FVarFixture


/-! ## Spine and telescope shapes -/

/-- A non-empty spine is an application. -/
theorem mkApps_cons_is_app (f x : LBTerm) (xs : List LBTerm) :
    ∃ g b, LBTerm.mkApps f (x :: xs) = .app g b := by
  induction xs generalizing f x with
  | nil => exact ⟨f, x, rfl⟩
  | cons y ys ih => exact ih (.app f x) y

/-- A spine is its own head or an application. -/
theorem mkApps_head_or_app (f : LBTerm) (args : List LBTerm) :
    LBTerm.mkApps f args = f ∨ ∃ g b, LBTerm.mkApps f args = .app g b := by
  rcases args with _ | ⟨x, xs⟩
  · exact .inl rfl
  · exact .inr (mkApps_cons_is_app f x xs)

/-- A non-empty telescope is a lambda. -/
theorem mkLambdas_is_lambda {ns : List BinderName} (h : ns ≠ []) (body : LBTerm) :
    ∃ n b, mkLambdas ns body = .lambda n b := by
  cases ns with
  | nil => exact absurd rfl h
  | cons n ns => exact ⟨n, mkLambdas ns body, rfl⟩

/-! ## Inversion -/

/-- `Lower` relates only `.box` to `.box`: no arm introduces or erases a box. -/
theorem Lower.target_box {Γ : GlobalDeclarations} {s t : LBTerm} (h : Lower Γ s t)
    (ht : t = .box) : s = .box := by
  cases h with
  | box => rfl
  | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a de Bruijn index to itself: passes do not renumber. -/
theorem Lower.target_bvar {Γ : GlobalDeclarations} {s t : LBTerm} {i : Nat} (h : Lower Γ s t)
    (ht : t = .bvar i) : s = .bvar i := by
  cases h with
  | bvar j => exact ht ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a free variable to itself. -/
theorem Lower.target_fvar {Γ : GlobalDeclarations} {s t : LBTerm} {x : Lean.FVarId}
    (h : Lower Γ s t) (ht : t = .fvar x) : s = .fvar x := by
  cases h with
  | fvar y => exact ht ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a primitive to itself. -/
theorem Lower.target_prim {Γ : GlobalDeclarations} {s t : LBTerm} {p : PrimVal}
    (h : Lower Γ s t) (ht : t = .prim p) : s = .prim p := by
  cases h with
  | prim q => exact ht ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- A constant in the target comes from the same constant, and is not a runtime key. -/
theorem Lower.target_const {Γ : GlobalDeclarations} {s t : LBTerm} {kn : Kername}
    (h : Lower Γ s t) (ht : t = .const kn) : s = .const kn ∧ ¬ RuntimeKey Γ kn := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection ht
      exact ⟨by rw [he], by rw [← he]; exact hk⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- A `.fix` in the target comes from one of the two fix arms, and carries a whole
`LowerBlock`: either the member's constant or its specification body. -/
theorem Lower.target_fix {Γ : GlobalDeclarations} {s t : LBTerm}
    {defs : List (@FixDef LBTerm)} {j : Nat} (h : Lower Γ s t) (ht : t = .fix defs j) :
    ∃ kns bs bs' ids, LowerBlock Γ kns bs bs' ids defs ∧
      ((∃ kn, s = .const kn ∧ kns[j]? = some kn) ∨ (bs[j]? = some s ∧ j < defs.length)) := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case»
  | fixEta => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @fixConst kn kns bs bs' ids defs₀ j₀ hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl
      hlow hcl hnk hj =>
      injection ht with hdefs hjj
      subst hdefs; subst hjj
      exact ⟨kns, bs, bs', ids,
        ⟨hb, hb', hdl, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩,
        .inl ⟨kn, rfl, hj⟩⟩
  | @fixBody b kns bs bs' ids defs₀ j₀ hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl
      hlow hcl hj hjl =>
      injection ht with hdefs hjj
      subst hdefs; subst hjj
      exact ⟨kns, bs, bs', ids,
        ⟨hb, hb', hdl, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩,
        .inr ⟨hj, hjl⟩⟩

/-- A `LowerAlt` pins the alternative's binder count to the field arity, nothing else. -/
theorem LowerAlt.arity {Γ : GlobalDeclarations} {nf : Nat} {m : LBTerm}
    {alt : List BinderName × LBTerm} (h : LowerAlt Γ nf m alt) : alt.1.length = nf := by
  induction h using LowerAlt.rec (motive_1 := fun _ _ _ => True) with
  | done => rfl
  | lam _ ih => simpa using ih
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case»
  | elimApp | fixConst | fixBody | fixEta => trivial


/-- A constructor node in the target comes from the same node, argument by argument: with
constructor introduction moved to `Erases.ctor`, no arm builds one out of a constant. -/
theorem Lower.target_construct {Γ : GlobalDeclarations} {s t : LBTerm} {iid : InductiveId}
    {k : Nat} {args' : List LBTerm} (h : Lower Γ s t) (ht : t = .construct iid k args') :
    ∃ args, s = .construct iid k args ∧ args'.length = args.length ∧
      ∀ i, i < args.length → Lower Γ args[i]! args'[i]! := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody | fixEta => exact LBTerm.noConfusion ht
  | @construct iid₀ k₀ args args₀ hlen hargs =>
      injection ht with hi hk hargs'
      subst hi; subst hk; subst hargs'
      exact ⟨args, rfl, hlen, hargs⟩
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- Spine congruence: `Lower` lifts from a head and its arguments to the whole
application spine. -/
theorem Lower.mkApps {Γ : GlobalDeclarations} {f f' : LBTerm} (hf : Lower Γ f f')
    {args args' : List LBTerm} (hlen : args'.length = args.length)
    (h : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
    Lower Γ (LBTerm.mkApps f args) (LBTerm.mkApps f' args') := by
  induction args generalizing f f' args' with
  | nil =>
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact hf
  | cons x xs ih =>
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, args' = y :: ys := by
        rcases args' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : Lower Γ x y := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine ih (.app hf hx) hlen' ?_
      intro i hi
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'

/-! ## Box-freedom

`NoBox` is what the capstone asks of the *lowered* value while the first-order theorem
proves it of the erasure. Its transport along `Lower` needs a premise excluding a `.fix`
in the target: `LowerFix.lean`'s `noBox_lower_needs_noFix` is the counterexample without
one. -/

mutual

/-- `t` contains no `□`. The box-freedom `[L Def. 6]`'s conclusion asserts of a
first-order answer. -/
def NoBox : LBTerm → Prop
  | .box => False
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .prim _ => True
  | .lambda _ b => NoBox b
  | .letIn _ v b => NoBox v ∧ NoBox b
  | .app f a => NoBox f ∧ NoBox a
  | .construct _ _ args => NoBoxArgs args
  | .case _ d alts => NoBox d ∧ NoBoxAlts alts
  | .proj _ e => NoBox e
  | .fix defs _ => NoBoxDefs defs

/-- `NoBox` over the arguments of a block-form constructor node. -/
def NoBoxArgs : List LBTerm → Prop
  | [] => True
  | t :: rest => NoBox t ∧ NoBoxArgs rest

/-- `NoBox` over `case` alternatives. -/
def NoBoxAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoBox b ∧ NoBoxAlts rest

/-- `NoBox` over `fix` definitions. -/
def NoBoxDefs : List (@FixDef LBTerm) → Prop
  | [] => True
  | fd :: rest => NoBox fd.body ∧ NoBoxDefs rest
end

/-- `NoBoxArgs` in the natural per-element form. -/
theorem NoBoxArgs_iff (l : List LBTerm) : NoBoxArgs l ↔ ∀ a ∈ l, NoBox a := by
  induction l with
  | nil => simp [NoBoxArgs]
  | cons a rest ih => simp [NoBoxArgs, ih]

/-- `NoBoxAlts` in the natural per-element form. -/
theorem NoBoxAlts_iff (l : List (List BinderName × LBTerm)) :
    NoBoxAlts l ↔ ∀ a ∈ l, NoBox a.2 := by
  induction l with
  | nil => simp [NoBoxAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoBoxAlts, ih]

@[simp] theorem NoBox_box : NoBox .box ↔ False := Iff.rfl
@[simp] theorem NoBox_bvar (i : Nat) : NoBox (.bvar i) := trivial
@[simp] theorem NoBox_fvar (x : FVarId) : NoBox (.fvar x) := trivial
@[simp] theorem NoBox_const (kn : Kername) : NoBox (.const kn) := trivial
@[simp] theorem NoBox_prim (p : PrimVal) : NoBox (.prim p) := trivial
@[simp] theorem NoBox_lambda (n : BinderName) (b : LBTerm) :
    NoBox (.lambda n b) ↔ NoBox b := Iff.rfl
@[simp] theorem NoBox_letIn (n : BinderName) (v b : LBTerm) :
    NoBox (.letIn n v b) ↔ NoBox v ∧ NoBox b := Iff.rfl
@[simp] theorem NoBox_app (f a : LBTerm) : NoBox (.app f a) ↔ NoBox f ∧ NoBox a := Iff.rfl
@[simp] theorem NoBox_proj (p : ProjectionInfo) (e : LBTerm) :
    NoBox (.proj p e) ↔ NoBox e := Iff.rfl
@[simp] theorem NoBox_construct (iid : InductiveId) (k : Nat) (args : List LBTerm) :
    NoBox (.construct iid k args) ↔ ∀ a ∈ args, NoBox a := by
  show NoBoxArgs args ↔ _; rw [NoBoxArgs_iff]
@[simp] theorem NoBox_case (ip : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoBox (.case ip d alts) ↔ NoBox d ∧ ∀ a ∈ alts, NoBox a.2 := by
  show NoBox d ∧ NoBoxAlts alts ↔ _; rw [NoBoxAlts_iff]

/-- Box-freedom of a spine is box-freedom of its head and of every argument. -/
theorem NoBox_mkApps (f : LBTerm) (args : List LBTerm) :
    NoBox (LBTerm.mkApps f args) ↔ NoBox f ∧ ∀ a ∈ args, NoBox a := by
  induction args generalizing f with
  | nil => simp [LBTerm.mkApps]
  | cons a as ih =>
      rw [LBTerm.mkApps, ih]
      constructor
      · rintro ⟨⟨hf, ha⟩, has⟩
        refine ⟨hf, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact has x hx
      · rintro ⟨hf, has⟩
        exact ⟨⟨hf, has a (by simp)⟩, fun x hx => has x (by simp [hx])⟩

/-- Box-freedom of a telescope is box-freedom of its body. -/
theorem NoBox_mkLambdas (ns : List BinderName) (b : LBTerm) :
    NoBox (mkLambdas ns b) ↔ NoBox b := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [mkLambdas, NoBox_lambda, ih]

/-- A telescope's own argument run is box-free. -/
theorem NoBox_bvarsDesc (n : Nat) : ∀ a ∈ bvarsDesc n, NoBox a := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := bvarsDesc_mem ha
  trivial

/-- `NoBoxDefs` in the natural per-element form. -/
theorem NoBoxDefs_iff (l : List (@FixDef LBTerm)) : NoBoxDefs l ↔ ∀ d ∈ l, NoBox d.body := by
  induction l with
  | nil => simp [NoBoxDefs]
  | cons a rest ih => simp [NoBoxDefs, ih]

@[simp] theorem NoBox_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoBox (.fix defs i) ↔ ∀ d ∈ defs, NoBox d.body := by
  show NoBoxDefs defs ↔ _; rw [NoBoxDefs_iff]

/-- `shift` moves indices and introduces no box. -/
theorem NoBox_shift : ∀ (t : LBTerm) (d c : Nat), NoBox t → NoBox (LBTerm.shift d c t) := by
  intro t
  induction t using LBTerm.recData with
  | hbox => intro _ _ h; exact h.elim
  | hbvar i => intro d c _; simp only [LBTerm.shift]; split <;> trivial
  | hfvar | hconst | hprim => intro _ _ _; trivial
  | hlam n b ih => intro d c h; exact ih d (c + 1) h
  | hletIn n v b ihv ihb => intro d c h; exact ⟨ihv d c h.1, ihb d (c + 1) h.2⟩
  | happ f a ihf iha => intro d c h; exact ⟨ihf d c h.1, iha d c h.2⟩
  | hproj p e ih => intro d c h; exact ih d c h
  | hconstruct iid k args ih =>
      intro d c h
      rw [NoBox_construct] at h
      simp only [LBTerm.shift, NoBox_construct, LBTerm.shiftArgs_eq_map, List.mem_map]
      rintro a ⟨x, hx, rfl⟩
      exact ih x hx d c (h x hx)
  | hcase info discr alts ihd iha =>
      intro d c h
      rw [NoBox_case] at h
      simp only [LBTerm.shift, NoBox_case, LBTerm.shiftAlts_eq_map, List.mem_map]
      refine ⟨ihd d c h.1, ?_⟩
      rintro a ⟨x, hx, rfl⟩
      exact iha x hx d _ (h.2 x hx)
  | hfix defs i ih =>
      intro d c h
      rw [NoBox_fix] at h
      simp only [LBTerm.shift, NoBox_fix, LBTerm.shiftDefs_eq_map, List.mem_map]
      rintro a ⟨x, hx, rfl⟩
      exact ih x hx d _ (h x hx)

/-! ## Small list and shape helpers

The list premises are indexed, so the proofs move between `l[i]!` and `∈ l` constantly, and
a spine inversion needs `getElem!` through `drop`, `reverse` and a one-element append. -/

/-- The last entry of a one-element append. -/
theorem getElem!_append_singleton {α : Type} [Inhabited α] (l : List α) (x : α) :
    (l ++ [x])[l.length]! = x := by
  rw [getElem!_pos (l ++ [x]) l.length (by simp)]
  simp

/-- `getElem!` through `List.drop`. -/
theorem getElem!_drop {α : Type} [Inhabited α] (l : List α) (m i : Nat)
    (h : i < (l.drop m).length) : (l.drop m)[i]! = l[m + i]! := by
  have h' : m + i < l.length := by simp only [List.length_drop] at h; omega
  rw [getElem!_pos (l.drop m) i h, getElem!_pos l (m + i) h', List.getElem_drop]

/-- `getElem!` through `List.reverse`. -/
theorem getElem!_reverse {α : Type} [Inhabited α] (l : List α) (i : Nat)
    (h : i < l.length) : l.reverse[i]! = l[l.length - 1 - i]! := by
  have h' : i < l.reverse.length := by simpa using h
  rw [getElem!_pos l.reverse i h', getElem!_pos l (l.length - 1 - i) (by omega),
    List.getElem_reverse h']

/-- A pointwise-related pair of lists stays pointwise related under `drop` and `reverse` —
the two list operations the ι rule applies to a constructor's fields. -/
theorem Lower.drop_reverse {Γ : GlobalDeclarations} {l l' : List LBTerm} (m : Nat)
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!) :
    ((l'.drop m).reverse).length = ((l.drop m).reverse).length ∧
      ∀ i, i < ((l.drop m).reverse).length →
        Lower Γ ((l.drop m).reverse)[i]! ((l'.drop m).reverse)[i]! := by
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_reverse, List.length_drop] at hi
  have hd : i < (l.drop m).length := by simp only [List.length_drop]; omega
  have hd' : i < (l'.drop m).length := by simp only [List.length_drop, hlen]; omega
  rw [getElem!_reverse _ i hd, getElem!_reverse _ i hd',
    getElem!_drop l m _ (by simp only [List.length_drop]; omega),
    getElem!_drop l' m _ (by simp only [List.length_drop, hlen]; omega)]
  have heq : (l'.drop m).length = (l.drop m).length := by simp [hlen]
  rw [heq]
  exact h _ (by simp only [List.length_drop] at *; omega)

/-- Extending a pointwise-related pair of lists by one related pair. -/
theorem Lower.concat {Γ : GlobalDeclarations} {l l' : List LBTerm} {x y : LBTerm}
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!)
    (hxy : Lower Γ x y) :
    (l' ++ [y]).length = (l ++ [x]).length ∧
      ∀ i, i < (l ++ [x]).length → Lower Γ (l ++ [x])[i]! (l' ++ [y])[i]! := by
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · rw [getElem!_pos (l ++ [x]) i (by simp; omega), getElem!_pos (l' ++ [y]) i (by simp; omega),
      List.getElem_append_left hlt, List.getElem_append_left (by omega),
      ← getElem!_pos l i hlt, ← getElem!_pos l' i (by omega)]
    exact h i hlt
  · obtain rfl : i = l.length := by omega
    rw [getElem!_append_singleton l x, ← hlen, getElem!_append_singleton l' y]
    exact hxy

/-- Two declarations of one constant carry the same body. -/
theorem DefnDecl.inj {Γ : GlobalDeclarations} {kn : Kername} {b b' : LBTerm}
    (h : DefnDecl Γ kn b) (h' : DefnDecl Γ kn b') : b = b' := by
  rw [DefnDecl] at h h'
  rw [h] at h'
  injection h' with h'; injection h' with h'; injection h' with h'
  exact Option.some.inj h'

/-- An in-range `getElem!` is the `getElem?`. -/
theorem getElem?_getElem! {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]? = some l[i]! := by
  rw [List.getElem?_eq_getElem h, getElem!_pos l i h]

/-- A `true` `isLambda` exhibits the λ. -/
theorem isLambda_eq_true {t : LBTerm} (h : isLambda t = true) : ∃ n b, t = .lambda n b := by
  cases t <;> simp [isLambda] at h ⊢

/-- Substituting does not change a λ head. -/
theorem isLambda_substList : ∀ (l : List LBTerm) {t : LBTerm}, isLambda t = true →
    isLambda (LBTerm.substList l t) = true
  | [], t, h => h
  | s :: l, t, h => by
      obtain ⟨n, b, rfl⟩ := isLambda_eq_true h
      exact isLambda_substList l (by rfl)

/-- A spine that is a constant is that constant, applied to nothing. -/
theorem mkApps_eq_const {f : LBTerm} {args : List LBTerm} {kn : Kername}
    (h : LBTerm.mkApps f args = .const kn) : args = [] ∧ f = .const kn := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, b, he⟩ := mkApps_cons_is_app f a as
      rw [he] at h; exact LBTerm.noConfusion h

/-- A spine that is a λ is that λ, applied to nothing. -/
theorem mkApps_eq_lambda {f : LBTerm} {args : List LBTerm} {n : BinderName} {b : LBTerm}
    (h : LBTerm.mkApps f args = .lambda n b) : args = [] ∧ f = .lambda n b := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, c, he⟩ := mkApps_cons_is_app f a as
      rw [he] at h; exact LBTerm.noConfusion h

/-- A spine that is a constructor node is that node, applied to nothing. -/
theorem mkApps_eq_construct {f : LBTerm} {args : List LBTerm} {iid : InductiveId} {k : Nat}
    {as : List LBTerm} (h : LBTerm.mkApps f args = .construct iid k as) :
    args = [] ∧ f = .construct iid k as := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as' =>
      obtain ⟨g, c, he⟩ := mkApps_cons_is_app f a as'
      rw [he] at h; exact LBTerm.noConfusion h

/-- A non-empty spine is an application. -/
theorem mkApps_ne_nil_is_app {f : LBTerm} {args : List LBTerm} (h : args ≠ []) :
    ∃ g b, LBTerm.mkApps f args = .app g b := by
  cases args with
  | nil => exact absurd rfl h
  | cons a as => exact mkApps_cons_is_app f a as

/-- A spine whose value is not an application is its head, applied to nothing. -/
theorem mkApps_eq_of_ne_app {f u : LBTerm} {args : List LBTerm}
    (hu : ∀ g b, u ≠ .app g b) (h : LBTerm.mkApps f args = u) : args = [] ∧ f = u := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, b, he⟩ := mkApps_cons_is_app f a as
      exact absurd (h.symm.trans he) (hu g b)

/-- `Lower` commutes with a whole substitution list. -/
theorem Lower.substList_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) :
    ∀ {l l' : List LBTerm}, l'.length = l.length →
      (∀ i, i < l.length → Lower Γ l[i]! l'[i]!) →
      ∀ {s t : LBTerm}, Lower Γ s t →
        Lower Γ (LBTerm.substList l s) (LBTerm.substList l' t)
  | [], l', hlen, _, s, t, h => by
      obtain rfl : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact h
  | x :: xs, l', hlen, hall, s, t, h => by
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, l' = y :: ys := by
        rcases l' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : Lower Γ x y := by
        have h0 := hall 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine Lower.substList_comm hΓ hlen' (fun i hi => ?_) (Lower.subst_comm hΓ hx h 0)
      have hi' := hall (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'

/-! ## λ-headedness of a block's members

`LowerBlock.hfl` is `LBWfPeregrine.fixLambda` read at one block: every emitted definition's
body is a λ. Transporting it to the specification bodies passes through `closeFix` and
`ConstToFVar`, both faithful on the head, and then through `Lower`, faithful on it too —
the only arm with a λ-headed target is `lambda`. So the source side is a projection of the
field and is never asserted a second time.

`lambda_of_fixLambda_needs_noEta` and its `EtaCounterexample` fixture are deleted with their
subject. They refuted the unconditional statement through `Lower.ctorEta`, which sent a
member body `.const lfC` to `λ_. lfC #0`; that arm is absent from the relation, and
`EtaSpine`, `not_etaSpine_lambda_named` and `Lower.source_isLambda`'s second disjunct are
deleted with it. -/

/-- Abstraction does not change the head constructor: `toBvar` maps a lambda to a lambda
and everything else to a non-lambda. -/
theorem isLambda_toBvar (x : FVarId) (lvl : Nat) (t : LBTerm) :
    isLambda (toBvar x lvl t) = isLambda t := by
  cases t with
  | fvar y => show isLambda (if y == x then _ else _) = _; split <;> rfl
  | _ => rfl

/-- `closeFix` does not change the head constructor. -/
theorem isLambda_closeFix (ids : List FVarId) (base : Nat) (t : LBTerm) :
    isLambda (closeFix ids base t) = isLambda t := by
  have go : ∀ (pairs : List (FVarId × Nat)) (u : LBTerm),
      isLambda (closeFixFold pairs u) = isLambda u := by
    intro pairs
    induction pairs with
    | nil => intro u; rfl
    | cons q rest ih =>
        obtain ⟨y, lvl⟩ := q
        intro u; rw [closeFixFold_cons, ih, isLambda_toBvar]
  exact go _ t

/-- Rewriting block constants to fixvars does not change the head constructor. -/
theorem ConstToFVar.isLambda_eq {kns : List Kername} {ids : List FVarId} {t u : LBTerm}
    (h : ConstToFVar kns ids t u) : isLambda u = isLambda t := by
  cases h <;> rfl

/-- The lowered bodies are λ-headed: `hfl` read back through `closeFix` and
`ConstToFVar`. -/
theorem LowerBlock.targetLambda_of_fixLambda {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hblock : LowerBlock Γ kns bs bs' ids defs) :
    ∀ j, j < kns.length → isLambda bs'[j]! = true := by
  intro j hj
  obtain ⟨u, hcu, heq⟩ := hblock.hcl j hj
  have := hblock.hfl j (hblock.hd ▸ hj)
  rw [heq, isLambda_closeFix, hcu.isLambda_eq] at this
  exact this

/-- A λ-headed target comes from a λ-headed source: `lambda` and `fixEta` are the only arms
whose target is a λ, since `elimApp`'s is a `.case` spine and the other two fix arms' is a
`.fix`.

Proved by induction, not by `cases`: `fixEta`'s source is a member body, whose λ-headedness
comes from `LowerBlock.lambda_of_fixLambda`, which is *defined* through this lemma. The
induction hypothesis at `hlow j` supplies it instead, against
`LowerBlock.targetLambda_of_fixLambda`, which reads `hcl`/`hfl` only. -/
theorem Lower.source_isLambda {Γ : GlobalDeclarations} {s t : LBTerm} (h : Lower Γ s t)
    (ht : isLambda t = true) : isLambda s = true := by
  revert ht
  induction h using Lower.rec (motive_2 := fun _ _ _ _ => True) with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case»
  | fixConst | fixBody => exact fun ht => absurd ht (by simp [isLambda])
  | lambda => exact fun _ => rfl
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      intro ht
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, a, he⟩ <;>
        rw [he] at ht <;> exact absurd ht (by simp [isLambda])
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro _
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hblock : LowerBlock Γ kns bs bs' ids defs :=
        ⟨hb, hb', hdl, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩
      have hlam := ih j hjk (hblock.targetLambda_of_fixLambda j hjk)
      rwa [hjeq] at hlam
  | done | lam => exact trivial

/-- **A block member's specification body is λ-headed**, unconditionally: the emitted
definition is, by `hfl`, and both halves of the transport are faithful on the head. -/
theorem LowerBlock.lambda_of_fixLambda {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hblock : LowerBlock Γ kns bs bs' ids defs) :
    ∀ j, j < kns.length → isLambda bs[j]! = true :=
  fun j hj => (hblock.hlow j hj).source_isLambda (hblock.targetLambda_of_fixLambda j hj)

/-! ## Source-side inversion at every node shape

`elimApp` is indexed by an application spine and the two fix arms by a declaration, so
inverting a derivation at a given *source* shape means ruling those out first. The `.fix`
target is ruled out by the derivation itself: a block carries `hfl`, so a member's
specification body is a λ and no source but a member's own constant reaches a `.fix`. -/

/-- Only a constant or a λ is lowered to a block's `.fix` node. -/
theorem Lower.notFix_of_block {Γ : GlobalDeclarations}
    {s : LBTerm} {defs : List (@FixDef LBTerm)} {j : Nat} (h : Lower Γ s (.fix defs j)) :
    (∃ kn, s = .const kn) ∨ isLambda s = true := by
  obtain ⟨kns, bs, bs', ids, hblock, hcase⟩ := Lower.target_fix h rfl
  rcases hcase with ⟨kn, rfl, _⟩ | ⟨hj, hjl⟩
  · exact .inl ⟨kn, rfl⟩
  · obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have := hblock.lambda_of_fixLambda j (by rw [hblock.hb] at hjb; exact hjb)
    rw [hjeq] at this
    exact .inr this

/-- A source that is neither a constant nor a λ has no `.fix` image: the only two arms with
a `.fix` target are the block member's constant and its own specification body, which the
block's `hfl` pins to a λ. -/
theorem Lower.ne_fix_of_block {Γ : GlobalDeclarations}
    {s t : LBTerm} (h : Lower Γ s t) (hc : ∀ kn, s ≠ .const kn) (hl : isLambda s = false)
    (defs : List (@FixDef LBTerm)) (j : Nat) : t ≠ .fix defs j := by
  intro ht
  subst ht
  rcases Lower.notFix_of_block h with ⟨kn, hk⟩ | hlam
  · exact hc kn hk
  · rw [hl] at hlam; exact Bool.noConfusion hlam

/-- **A source that is neither a constant nor a λ has no block image at all.** The three
arms whose target is built from a block — `fixConst`, `fixBody`, `fixEta` — have a constant
or a member body as source, and `LowerBlock.hfl` pins the latter to a λ. The second
component covers `fixEta`, whose target is a λ rather than a `.fix` node, and covers it
positively: every λ-headed target has a λ-headed source. -/
theorem Lower.ne_block_image {Γ : GlobalDeclarations}
    {s t : LBTerm} (h : Lower Γ s t) (hc : ∀ kn, s ≠ .const kn) (hl : isLambda s = false) :
    (∀ defs j, t ≠ .fix defs j) ∧ isLambda t = false := by
  refine ⟨Lower.ne_fix_of_block h hc hl, ?_⟩
  cases htl : isLambda t with
  | false => rfl
  | true => rw [h.source_isLambda htl] at hl; exact Bool.noConfusion hl

/-- `□` is lowered to `□`. -/
theorem Lower.source_box {Γ : GlobalDeclarations} {s t : LBTerm}
    (h : Lower Γ s t) (hs : s = .box) : t = .box := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box => rfl
  | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A de Bruijn index is lowered to itself. -/
theorem Lower.source_bvar {Γ : GlobalDeclarations} {s t : LBTerm} {i : Nat} (h : Lower Γ s t) (hs : s = .bvar i) : t = .bvar i := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | bvar j => exact hs ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A free variable is lowered to itself. -/
theorem Lower.source_fvar {Γ : GlobalDeclarations} {s t : LBTerm} {x : FVarId} (h : Lower Γ s t) (hs : s = .fvar x) : t = .fvar x := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | fvar y => exact hs ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A primitive is lowered to itself. -/
theorem Lower.source_prim {Γ : GlobalDeclarations} {s t : LBTerm} {p : PrimVal} (h : Lower Γ s t) (hs : s = .prim p) : t = .prim p := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | prim q => exact hs ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A `let` is lowered to a `let`, value and body pointwise. -/
theorem Lower.source_letIn {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName} {v b : LBTerm}
    (h : Lower Γ s t) (hs : s = .letIn n v b) :
    ∃ n' v' b', t = .letIn n' v' b' ∧ Lower Γ v v' ∧ Lower Γ b b' := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @letIn n₀ n' v₀ v' b₀ b' hv hb =>
      injection hs with _ hvv hbb
      subst hvv; subst hbb
      exact ⟨n', v', b', rfl, hv, hb⟩
  | box | bvar | fvar | prim | const | lambda | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A projection is lowered to a projection with the same triple. -/
theorem Lower.source_proj {Γ : GlobalDeclarations} {s t : LBTerm} {p : ProjectionInfo} {e : LBTerm} (h : Lower Γ s t) (hs : s = .proj p e) :
    ∃ e', t = .proj p e' ∧ Lower Γ e e' := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @proj p₀ e₀ e' he =>
      injection hs with hp hee
      subst hp; subst hee
      exact ⟨e', rfl, he⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A constructor node is lowered argument by argument. -/
theorem Lower.source_construct {Γ : GlobalDeclarations} {s t : LBTerm} {iid : InductiveId} {k : Nat} {args : List LBTerm}
    (h : Lower Γ s t) (hs : s = .construct iid k args) :
    ∃ args', t = .construct iid k args' ∧ args'.length = args.length ∧
      ∀ i, i < args.length → Lower Γ args[i]! args'[i]! := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @construct iid₀ k₀ args₀ args' hlen ha =>
      injection hs with hi hk hargs
      subst hi; subst hk; subst hargs
      exact ⟨args', rfl, hlen, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A `case` is lowered to a `case` with the same inductive, parameter count and branch
arities. -/
theorem Lower.source_case {Γ : GlobalDeclarations} {s t : LBTerm} {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} (h : Lower Γ s t) (hs : s = .case ip d alts) :
    ∃ d' alts', t = .case ip d' alts' ∧ Lower Γ d d' ∧ alts'.length = alts.length ∧
      (∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length) ∧
      ∀ i, i < alts.length → Lower Γ (alts[i]!).2 (alts'[i]!).2 := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @«case» ip₀ d₀ d' alts₀ alts' hd hlen hn hb =>
      injection hs with hi hdd hal
      subst hi; subst hdd; subst hal
      exact ⟨d', alts', rfl, hd, hlen, hn, hb⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A `.fix` in the source has no image at all: the relation has no `fix` congruence arm,
`fixConst`'s source is a constant, and `fixBody`'s is a member body the guard pins to a λ. -/
theorem Lower.source_fix {Γ : GlobalDeclarations} {s t : LBTerm} {defs₀ : List (@FixDef LBTerm)} {i : Nat}
    (h : Lower Γ s t) (hs : s = .fix defs₀ i) : False := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- What a λ can lower to: a λ, or a block's `.fix` node — a member's specification body is
a λ, which is exactly the `fixBody` source a block admits. `fixEta`'s target lands in the
first disjunct: the wrapper is a λ, so the statement does not change. -/
theorem Lower.source_lambda {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName}
    {b : LBTerm} (h : Lower Γ s t) (hs : s = .lambda n b) :
    (∃ n' b', t = .lambda n' b') ∨ ∃ defs j, t = .fix defs j := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₀ b' => exact .inl ⟨n', b', rfl⟩
  | @fixConst kn kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixBody b₀ kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixEta b₀ n₀ kns bs bs' ids defs j => exact .inl ⟨n₀, _, rfl⟩
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- **What a constant can lower to: two images, both under `¬ RuntimeKey`.** Itself, by
`const`, or a block's `.fix` node, by `fixConst`. The other two arms whose source is
unconstrained are `fixBody` and `fixEta`, and the block's own `hfl` excludes both: either
would force `isLambda (.const kn) = true`. This is why the two images are read off the
derivation and not off the source's syntax, and it is what lets an `ElimDecl` at `kn` refute
them. -/
theorem Lower.source_const {Γ : GlobalDeclarations} {s t : LBTerm} {kn : Kername}
    (h : Lower Γ s t) (hs : s = .const kn) :
    ¬ RuntimeKey Γ kn ∧ (t = .const kn ∨ ∃ defs j, t = .fix defs j) := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hk, .inl rfl⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @elimApp kn' iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn')
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @fixConst kn' kns bs bs' ids defs j _ _ _ _ _ _ _ _ _ _ _ _ hnk hj =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hnk, .inr ⟨defs, j, rfl⟩⟩
  | @fixBody b kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := (⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow,
        hcl⟩ : LowerBlock Γ kns bs bs' ids defs).lambda_of_fixLambda j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam
  | @fixEta b nm kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := (⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow,
        hcl⟩ : LowerBlock Γ kns bs bs' ids defs).lambda_of_fixLambda j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam

/-- What a nullary constructor node can lower to: itself, or a block's `.fix` node. A
consumer drops the second by `Lower.ne_fix_of_block`: a constructor node is no λ. The same
`hfl` that rules `fixBody` in rules `fixEta` out: a constructor node is no λ either. -/
theorem Lower.source_construct_nil {Γ : GlobalDeclarations} {s t : LBTerm}
    {iid : InductiveId} {k : Nat} (h : Lower Γ s t) (hs : s = .construct iid k []) :
    t = .construct iid k [] ∨ ∃ defs j, t = .fix defs j := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion hs
  | @fixConst kn kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixBody b kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixEta b nm kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := (⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow,
        hcl⟩ : LowerBlock Γ kns bs bs' ids defs).lambda_of_fixLambda j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam
  | @construct iid' k' args args' hlen ha =>
      injection hs with hi hk hargs
      subst hi; subst hk; subst hargs
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact .inl rfl
  | @elimApp kn iid' np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-! ## Growth of the specification environment

The proof of the registration invariant builds `Γspec` as it goes, so the pass must survive
the environment growing under it. `SpecGrow` is that growth — MetaRocq weakens `erases_deps`
under one fresh declaration (`../metarocq/erasure/theories/EDeps.v:492`, `erases_deps_cons`)
— with the third clause λ□'s own eliminator pruning forces: `Lower.const`'s premise is
*anti*-monotone in `Γ`, and a fresh prefix carrying a block can complete an `ElimDecl` at a
key the environment already declares.
-/

/-- A lookup survives a prefix whose keys all miss it. -/
theorem envLookup_append_of_fresh : ∀ {pre Γ : GlobalDeclarations} {kn : Kername}
    {d : GlobalDecl}, (∀ p ∈ pre, p.1 ≠ kn) → LBTerm.envLookup Γ kn = some d →
    LBTerm.envLookup (pre ++ Γ) kn = some d
  | [], _, _, _, _, h => h
  | (k, v) :: pre, Γ, kn, d, hf, h => by
      rw [List.cons_append, LBTerm.envLookup, if_neg]
      · exact envLookup_append_of_fresh (fun p hp => hf p (List.mem_cons_of_mem _ hp)) h
      · exact fun hb => hf (k, v) (List.mem_cons_self ..) (Kername.eq_of_beq hb)

/-- Every `.const` node of `t`, and every block its nodes read, is declared in `Γ`:
`ErasesEnv.deps` at the term's own references. -/
def ConstsDeclared (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn ∈ constRefs t, (LBTerm.envLookup Γ kn).isSome

/-- Every declared body's own references are declared: the `tConst` case of MetaRocq's
`wellformed` under `wf_glob` (`../metarocq/erasure/theories/EWellformed.v:166`, `:211`), the
δ column of λ□ well-formedness. `SpecGrowFixture.specGrow_needs_declaredEnv` is why the
pass's monotonicity asks for it and not for the term's references alone. -/
def ConstsDeclaredEnv (Γ : GlobalDeclarations) : Prop :=
  ∀ kn b, DefnDecl Γ kn b → ConstsDeclared Γ b

/-- The decidable twin of `ConstsDeclaredEnv`: the entry list read once. `envLookup` is the
quantifier `decide` cannot reach, so the check reads the list and `envLookup_mem` turns a
declaration back into an entry. -/
def constsDeclaredEnvB (Γ : GlobalDeclarations) : Bool :=
  Γ.all fun p => match p.2 with
    | .constantDecl ⟨some b⟩ => (constRefs b).all fun kn => (LBTerm.envLookup Γ kn).isSome
    | _ => true

/-- A `true` verdict is the property. -/
theorem constsDeclaredEnv_of_check {Γ : GlobalDeclarations} (h : constsDeclaredEnvB Γ = true) :
    ConstsDeclaredEnv Γ := by
  intro kn b hd kn' hkn'
  have hall := List.all_eq_true.1 h _ (envLookup_mem hd)
  simp only at hall
  exact List.all_eq_true.1 hall _ hkn'

/-- **The δ column carries the closure**: a seed of declared kernames stays declared under
any number of δ-steps, because a step only adds the references of a declared body. -/
theorem reachFrom_isSome_of_declaredEnv {Γ : GlobalDeclarations} (henv : ConstsDeclaredEnv Γ) :
    ∀ (n : Nat) {seen : List Kername}, (∀ kn ∈ seen, (LBTerm.envLookup Γ kn).isSome) →
      ∀ kn ∈ reachFrom Γ seen n, (LBTerm.envLookup Γ kn).isSome
  | 0, _, h => h
  | n + 1, _, h => by
      intro kn hkn
      rcases mem_expandRefs.1 hkn with hk | ⟨k, hk, b, hb, hcb⟩
      · exact reachFrom_isSome_of_declaredEnv henv n h kn hk
      · exact henv k b hb kn hcb

/-- **`ErasesEnv.deps` from the δ column.** Everything reachable from a term whose own
references are declared is declared, provided every declared body's references are. This is
the closure MetaRocq builds into `erases_deps` itself: its `tConst` arm demands
`erases_deps` of the declared body beside the declaration
(`../metarocq/erasure/theories/Extract.v:324-329`), so a structural derivation already
carries the transitive condition that `ReachableFrom` states separately. -/
theorem ReachableFrom.isSome_of_declaredEnv {Γ : GlobalDeclarations} {t : LBTerm}
    {kn : Kername} (ht : ConstsDeclared Γ t) (henv : ConstsDeclaredEnv Γ)
    (h : ReachableFrom Γ t kn) : (LBTerm.envLookup Γ kn).isSome :=
  reachFrom_isSome_of_declaredEnv henv _ ht kn (kernameElem_iff.1 h)

/-- A declared key stays declared under a new entry, whatever the entry's key. -/
theorem envLookup_cons_isSome {Γ : GlobalDeclarations} {k kn : Kername} {d : GlobalDecl}
    (h : (LBTerm.envLookup Γ kn).isSome) : (LBTerm.envLookup ((k, d) :: Γ) kn).isSome := by
  rw [LBTerm.envLookup]
  split
  · rfl
  · exact h

/-- A term's references stay declared under a new entry. -/
theorem ConstsDeclared.cons {Γ : GlobalDeclarations} {k : Kername} {d : GlobalDecl}
    {t : LBTerm} (h : ConstsDeclared Γ t) : ConstsDeclared ((k, d) :: Γ) t :=
  fun kn hkn => envLookup_cons_isSome (h kn hkn)

/-- The δ column survives a new entry, given it of whatever body the entry carries. -/
theorem constsDeclaredEnv_cons {Γ : GlobalDeclarations} {k : Kername} {d : GlobalDecl}
    (h : ConstsDeclaredEnv Γ)
    (hnew : ∀ b, d = .constantDecl ⟨some b⟩ → ConstsDeclared ((k, d) :: Γ) b) :
    ConstsDeclaredEnv ((k, d) :: Γ) := by
  intro kn b hd
  rw [DefnDecl, LBTerm.envLookup] at hd
  split at hd
  · exact hnew b (Option.some.inj hd)
  · exact (h kn b hd).cons

/-- `Γ'` extends `Γ` by a prefix of fresh keys and turns no key `Γ` already declares into a
runtime key. -/
def SpecGrow (Γ Γ' : GlobalDeclarations) : Prop :=
  ∃ pre : GlobalDeclarations, Γ' = pre ++ Γ ∧ (∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1) ∧
    ∀ kn, (LBTerm.envLookup Γ kn).isSome → RuntimeKey Γ' kn → RuntimeKey Γ kn

/-- Growth preserves a declaration. -/
theorem SpecGrow.lookup {Γ Γ' : GlobalDeclarations} (h : SpecGrow Γ Γ') {kn : Kername}
    {d : GlobalDecl} (hd : LBTerm.envLookup Γ kn = some d) :
    LBTerm.envLookup Γ' kn = some d := by
  obtain ⟨pre, rfl, hf, -⟩ := h
  exact envLookup_append_of_fresh (fun p hp => hf p hp (kn, d) (envLookup_mem hd)) hd

/-- Growth preserves declaredness. -/
theorem SpecGrow.isSome {Γ Γ' : GlobalDeclarations} (h : SpecGrow Γ Γ') {kn : Kername}
    (hd : (LBTerm.envLookup Γ kn).isSome) : (LBTerm.envLookup Γ' kn).isSome := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hd
  rw [h.lookup hd]; rfl

/-- Growth preserves a definition. -/
theorem SpecGrow.defnDecl {Γ Γ' : GlobalDeclarations} (h : SpecGrow Γ Γ') {kn : Kername}
    {b : LBTerm} (hd : DefnDecl Γ kn b) : DefnDecl Γ' kn b := h.lookup hd

/-- Growth preserves an eliminator declaration: both of `ElimDecl`'s lookups. -/
theorem SpecGrow.elimDecl {Γ Γ' : GlobalDeclarations} (h : SpecGrow Γ Γ') {kn : Kername}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    (hd : ElimDecl Γ kn iid np dp nfs) : ElimDecl Γ' kn iid np dp nfs :=
  ⟨⟨hd.1.choose, h.lookup hd.1.choose_spec.1, hd.1.choose_spec.2⟩,
    ⟨hd.2.choose, h.lookup hd.2.choose_spec.1, hd.2.choose_spec.2⟩⟩

/-- Growth turns no declared key into a runtime key: the third clause, named. -/
theorem SpecGrow.runtimeKey {Γ Γ' : GlobalDeclarations} (h : SpecGrow Γ Γ') {kn : Kername}
    (hd : (LBTerm.envLookup Γ kn).isSome) (hrk : RuntimeKey Γ' kn) : RuntimeKey Γ kn := by
  obtain ⟨-, -, -, h⟩ := h
  exact h kn hd hrk

/-- Growth preserves a runtime key: `ElimDecl`'s two lookups both survive. The converse at a
*declared* key is the third clause; this direction is free. -/
theorem RuntimeKey.specGrow {Γ Γ' : GlobalDeclarations} (hg : SpecGrow Γ Γ') {kn : Kername}
    (h : RuntimeKey Γ kn) : RuntimeKey Γ' kn :=
  let ⟨iid, np, dp, nfs, hd⟩ := h
  ⟨iid, np, dp, nfs, hg.elimDecl hd⟩

/-- Growth preserves declaredness of a term's references. -/
theorem ConstsDeclared.specGrow {Γ Γ' : GlobalDeclarations} {t : LBTerm}
    (h : SpecGrow Γ Γ') (hd : ConstsDeclared Γ t) : ConstsDeclared Γ' t :=
  fun kn hkn => h.isSome (hd kn hkn)

/-- Growth is reflexive. -/
theorem SpecGrow.refl (Γ : GlobalDeclarations) : SpecGrow Γ Γ :=
  ⟨[], rfl, by simp, fun _ _ h => h⟩

/-- Growth composes, which is what threads it through a run's successive steps. -/
theorem SpecGrow.trans {Γ₀ Γ₁ Γ₂ : GlobalDeclarations} (h₁ : SpecGrow Γ₀ Γ₁)
    (h₂ : SpecGrow Γ₁ Γ₂) : SpecGrow Γ₀ Γ₂ := by
  obtain ⟨pre₁, rfl, hf₁, hr₁⟩ := h₁
  obtain ⟨pre₂, rfl, hf₂, hr₂⟩ := h₂
  refine ⟨pre₂ ++ pre₁, by rw [List.append_assoc], ?_, ?_⟩
  · intro p hp q hq
    rcases List.mem_append.1 hp with hp | hp
    · exact hf₂ p hp q (List.mem_append_right _ hq)
    · exact hf₁ p hp q hq
  · intro kn hkn hrk
    refine hr₁ kn hkn (hr₂ kn ?_ hrk)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hkn
    rw [envLookup_append_of_fresh (fun p hp => hf₁ p hp (kn, d) (envLookup_mem hd)) hd]
    rfl

/-- Every eliminator body `Γ` declares has its block declared in `Γ` too. `ElimDecl` bundles
the two, so an environment whose eliminator entries are added with their blocks satisfies it,
and one whose declared bodies are erasure images satisfies it vacuously
(`erases_ne_elimBody`). -/
def ElimBlocksDeclared (Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (body : LBTerm) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
    LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) → ElimBody iid np dp nfs body →
    (LBTerm.envLookup Γ iid.mutualBlockName).isSome

/-- A lambda telescope names what its body names. -/
theorem constRefs_mkLambdas (ns : List BinderName) (b : LBTerm) :
    constRefs (mkLambdas ns b) = constRefs b := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [mkLambdas, constRefs, ih]

/-- An eliminator body names its own block: the `.case` node `mkElimBody` dispatches with
reads it, and `constRefs` reports a `.case` node's block. -/
theorem mem_constRefs_elimBody {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {b : LBTerm}
    (h : ElimBody iid np dp nfs b) : iid.mutualBlockName ∈ constRefs b := by
  have hcases : iid.mutualBlockName ∈ constRefs (mkElimBody iid np dp nfs) := by
    rw [mkElimBody, constRefs_mkLambdas, constRefs]
    exact List.mem_cons_self
  rcases h.shape with rfl | rfl
  · exact hcases
  · show iid.mutualBlockName ∈ constRefs (mkElimBodyRec iid np dp nfs)
    rw [mkElimBodyRec]
    show iid.mutualBlockName ∈ constRefsDefs _
    rw [constRefsDefs]
    exact List.mem_append_left _ hcases

/-- **The δ column pays `SpecGrow.of_fresh`'s side condition.** An eliminator body is one of
its own references, so an environment whose declared bodies name only declared keys has every
eliminator's block declared. -/
theorem elimBlocksDeclared_of_constsDeclaredEnv {Γ : GlobalDeclarations}
    (h : ConstsDeclaredEnv Γ) : ElimBlocksDeclared Γ :=
  fun _ _ _ _ _ _ hd he => h _ _ hd _ (mem_constRefs_elimBody he)

/-- **A fresh prefix is a growth** over an environment whose eliminator bodies already have
their blocks: `ElimDecl`'s two lookups are then answered by `Γ` itself, so no declared key
becomes a runtime key. Without the side condition the prefix can complete an eliminator
declaration `Γ` had only half of (`Round7M.freshPrefix_not_runtimeKey_stable`). -/
theorem SpecGrow.of_fresh {Γ pre : GlobalDeclarations}
    (hf : ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1) (hb : ElimBlocksDeclared Γ) :
    SpecGrow Γ (pre ++ Γ) := by
  refine ⟨pre, rfl, hf, ?_⟩
  intro kn hkn hrk
  obtain ⟨iid, np, dp, nfs, ⟨body, hbody, helim⟩, mib, hmib, hbo, hnp⟩ := hrk
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hkn
  have hd' : LBTerm.envLookup (pre ++ Γ) kn = some d :=
    envLookup_append_of_fresh (fun p hp => hf p hp (kn, d) (envLookup_mem hd)) hd
  have hdb : d = .constantDecl ⟨some body⟩ := by
    rw [hd'] at hbody; exact Option.some.inj hbody
  subst hdb
  have hblk := hb kn body iid np dp nfs hd helim
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 hblk
  have hd'' : LBTerm.envLookup (pre ++ Γ) iid.mutualBlockName = some d' :=
    envLookup_append_of_fresh
      (fun p hp => hf p hp (iid.mutualBlockName, d') (envLookup_mem hd')) hd'
  have hdm : d' = .inductiveDecl mib := by rw [hd''] at hmib; exact Option.some.inj hmib
  subst hdm
  exact ⟨iid, np, dp, nfs, ⟨body, hd, helim⟩, mib, hd', hbo, hnp⟩

/-! ### References of a part

The four shapes whose sub-terms the pass descends into, read at `constRefs`. -/

/-- A constructor node's arguments name only what the node names. -/
theorem ConstsDeclared.args {Γ : GlobalDeclarations} {iid : InductiveId} {k : Nat}
    {args : List LBTerm} (hd : ConstsDeclared Γ (.construct iid k args)) {i : Nat}
    (hi : i < args.length) : ConstsDeclared Γ args[i]! := by
  intro kn hkn
  refine hd kn ?_
  rw [constRefs, List.mem_cons]
  exact .inr (mem_constRefsArgs.2 ⟨args[i]!, Lower.getElem!_mem hi, hkn⟩)

/-- A branch body names only what the `case` node names. -/
theorem ConstsDeclared.alts {Γ : GlobalDeclarations} {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} (hd : ConstsDeclared Γ (.case ip d alts))
    {i : Nat} (hi : i < alts.length) : ConstsDeclared Γ (alts[i]!).2 := by
  intro kn hkn
  refine hd kn ?_
  rw [constRefs, List.mem_cons]
  exact .inr (List.mem_append_right _
    (mem_constRefsAlts.2 ⟨alts[i]!, Lower.getElem!_mem hi, hkn⟩))

/-- A discriminant names only what the `case` node names. -/
theorem ConstsDeclared.discr {Γ : GlobalDeclarations} {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} (hd : ConstsDeclared Γ (.case ip d alts)) :
    ConstsDeclared Γ d := by
  intro kn hkn
  refine hd kn ?_
  rw [constRefs, List.mem_cons]
  exact .inr (List.mem_append_left _ hkn)

/-- A spine's head and arguments name only what the spine names. -/
theorem ConstsDeclared.spine {Γ : GlobalDeclarations} {f : LBTerm} {l : List LBTerm}
    (hd : ConstsDeclared Γ (LBTerm.mkApps f l)) :
    ConstsDeclared Γ f ∧ ∀ x ∈ l, ConstsDeclared Γ x := by
  constructor
  · intro kn hkn
    exact hd kn (by rw [constRefs_mkApps]; exact List.mem_append_left _ hkn)
  · intro x hx kn hkn
    refine hd kn ?_
    rw [constRefs_mkApps]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hkn⟩)

/-! ### The pass survives growth -/

/-- **`Lower` is monotone along `SpecGrow`**, given that the term's own references and every
declared body's references are declared. The `const` arm spends the growth's third clause at
the term's own key; the three fix arms spend `ConstsDeclaredEnv` at the block's declared
bodies, which the term's references do not reach. -/
theorem Lower.specGrow {Γ Γ' : GlobalDeclarations} (hg : SpecGrow Γ Γ')
    (henv : ConstsDeclaredEnv Γ) {s t : LBTerm} (h : Lower Γ s t) :
    ConstsDeclared Γ s → Lower Γ' s t := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ConstsDeclared Γ m → LowerAlt Γ' nf m alt) with
  | box => exact fun _ => .box
  | bvar i => exact fun _ => .bvar i
  | fvar x => exact fun _ => .fvar x
  | prim p => exact fun _ => .prim p
  | @const kn hk =>
      intro hd
      refine .const fun hrk => hk (hg.runtimeKey (hd kn ?_) hrk)
      rw [constRefs]; exact List.mem_cons_self ..
  | lambda _ ih => exact fun hd => .lambda (ih hd)
  | letIn _ _ ihv ihb =>
      intro hd
      refine .letIn (ihv fun kn hkn => hd kn ?_) (ihb fun kn hkn => hd kn ?_)
      · rw [constRefs]; exact List.mem_append_left _ hkn
      · rw [constRefs]; exact List.mem_append_right _ hkn
  | app _ _ ihf iha =>
      intro hd
      refine .app (ihf fun kn hkn => hd kn ?_) (iha fun kn hkn => hd kn ?_)
      · rw [constRefs]; exact List.mem_append_left _ hkn
      · rw [constRefs]; exact List.mem_append_right _ hkn
  | proj _ ih =>
      intro hd
      refine .proj (ih fun kn hkn => hd kn ?_)
      rw [constRefs]; exact List.mem_cons_of_mem _ hkn
  | @construct iid k args args' hlen _ ih =>
      intro hd
      exact .construct hlen fun i hi => ih i hi (hd.args hi)
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro hd
      exact .case (ihd hd.discr) hlen hn fun i hi => ihb i hi (hd.alts hi)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro hd
      obtain ⟨-, hargs⟩ := hd.spine
      refine .elimApp (hg.elimDecl hh) hlen hmlen halen (fun i hi => ihmin i hi ?_)
        (ihd ?_) hxlen (fun i hi => ihx i hi ?_)
      · exact hargs _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ (Lower.getElem!_mem (by omega)))))
      · exact hargs _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_self ..)))
      · exact hargs _ (List.mem_append_right _ (Lower.getElem!_mem hi))
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hnk hj ih =>
      intro _
      obtain ⟨hjk, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk' : j < kns.length := by omega
      refine .fixConst hb hb' hdl hnd hids hilen hfresh hrarg
        (fun i hi => hg.defnDecl (hdecl i hi)) hfl
        (fun i hi => ih i hi (henv _ _ (hdecl i hi))) hcl (fun hrk => hnk ?_) hj
      refine hg.runtimeKey ?_ hrk
      rw [← hjeq]
      exact Option.isSome_of_eq_some (hdecl j hjk')
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro _
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg
        (fun i hi => hg.defnDecl (hdecl i hi)) hfl
        (fun i hi => ih i hi (henv _ _ (hdecl i hi))) hcl hj hjl
  | @fixEta b nm kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro _
      exact .fixEta hb hb' hdl hnd hids hilen hfresh hrarg
        (fun i hi => hg.defnDecl (hdecl i hi)) hfl
        (fun i hi => ih i hi (henv _ _ (hdecl i hi))) hcl hj hjl
  | done _ ih => rename_i hd; exact LowerAlt.done (ih hd)
  | @lam nf n n' m alt _ ih =>
      rename_i hd
      exact LowerAlt.lam (ih fun kn hkn => hd kn (by rw [constRefs]; exact hkn))

/-- The alternative half of the same law, by induction on the field count. -/
theorem LowerAlt.specGrow {Γ Γ' : GlobalDeclarations} (hg : SpecGrow Γ Γ')
    (henv : ConstsDeclaredEnv Γ) {nf : Nat} {m : LBTerm} {alt : List BinderName × LBTerm}
    (h : LowerAlt Γ nf m alt) (hd : ConstsDeclared Γ m) : LowerAlt Γ' nf m alt := by
  induction nf generalizing m alt with
  | zero => cases h with | done hl => exact .done (Lower.specGrow hg henv hl hd)
  | succ n ih =>
      cases h with
      | @lam _ n₀ n' m₀ alt₀ h₀ =>
          exact .lam (ih h₀ fun kn hkn => hd kn (by rw [constRefs]; exact hkn))

/-! ## Non-vacuity, and what `hfl` excludes

One fixture per arm whose premises read the environment: `elimApp` at its `.const`-headed
key with a non-empty `extra`, and — in `LowerFix.lean`, where the block fixture lives —
`fixConst` under its `¬ RuntimeKey` guard. The second fixture here is the one-member
counterexample `hfl` rules out. -/

namespace LowerElimFixture

/-- The fixture's inductive block. -/
def blockKn : Kername := { mp := .MPfile [], id := "LE" }
/-- Its `casesOn` eliminator constant. -/
def elimKn : Kername := { mp := .MPfile [], id := "LEcasesOn" }
/-- The block's one inductive: no parameters, two constructors of `0` and `1` fields. -/
def iid : InductiveId := { mutualBlockName := blockKn, idx := 0 }

/-- The emitted inductive body, non-propositional, with the two field counts. `propositional`
is written out: `F-PROP` removed its `false` default, because `Erasure.register_inductive`
computes it from the declared arity. -/
def mib : MutualInductiveBody :=
  { npars := 0,
    bodies := [{ name := "LE", propositional := false,
                 ctors := [{ name := "nil", nargs := 0 },
                           { name := "one", nargs := 1 }], projs := [] }] }

/-- The block and its eliminator, whose body is the canonical non-recursive shape at one
dropped argument (the motive) and two minors. -/
def env : GlobalDeclarations :=
  [(blockKn, .inductiveDecl mib),
   (elimKn, .constantDecl ⟨some (mkElimBody iid 0 1 [0, 1])⟩)]

/-- Both conjuncts of `ElimDecl`: the eliminator's body and the block it dispatches on,
with the block's own `propositional = false`. -/
theorem elimDecl : ElimDecl env elimKn iid 0 1 [0, 1] :=
  ⟨⟨_, rfl, .cases⟩, ⟨mib, rfl, ⟨rfl, _, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩⟩

/-- Hence the eliminator constant is a runtime key, so neither `const` nor `fixConst`
relates it — which is what `Lower.source_const` turns into an inversion. -/
theorem runtimeKey_elimKn : RuntimeKey env elimKn := ⟨_, _, _, _, elimDecl⟩

/-- **`elimApp` fires at the new key, with `extra ≠ []`.** The eliminator spine — motive,
discriminant, two minors — applied to one argument past its arity becomes the `.case` node
applied to that argument. -/
theorem elimApp_fires :
    Lower env
      (LBTerm.mkApps (.const elimKn)
        ([.box] ++ .bvar 0 :: [.box, .lambda .anon (.bvar 0)] ++ [.bvar 1]))
      (LBTerm.mkApps (.case (iid, 0) (.bvar 0) [([], .box), ([.anon], .bvar 0)]) [.bvar 1]) := by
  refine .elimApp elimDecl rfl rfl rfl ?_ (.bvar 0) rfl ?_
  · intro i hi
    match i, hi with
    | 0, _ => exact .done .box
    | 1, _ => exact .lam (alt := ([], .bvar 0)) (.done (.bvar 0))
  · intro i hi
    match i, hi with
    | 0, _ => exact .bvar 1

end LowerElimFixture

/-! ### The constructor-bodied one-member block -/

namespace LowerCtorBodyFixture

/-- The block of the one-entry counterexample environment. -/
def iid : InductiveId := ⟨rootKername "U", 0⟩

/-- One definition whose body is a nullary constructor node — `Unit.unit`'s shape in every
one of the five programs' specification environments. -/
def env : GlobalDeclarations :=
  [(rootKername "u", .constantDecl ⟨some (.construct iid 0 [])⟩)]

/-- The block's one fixvar. -/
def ids : List FVarId := [⟨.mkSimple "u"⟩]

/-- The definition `mkDef` would emit for it: `closeFix` of the same node, which is the
node again. -/
def defs : List (@FixDef LBTerm) :=
  [{ name := .anon, body := closeFix ids 0 (.construct iid 0 []), principalArgIdx := 0 }]

/-- **A constructor-bodied definition is no block of the pass**: `hfl` fails, because the
emitted body is the constructor node and not a λ. `Unit.unit ↦ .construct …` is that shape
and every one of the five programs declares it, so a λ-headedness condition quantified over
every `LowerBlock` over `Γ`, rather than over the blocks a run builds, is refuted there. -/
theorem lowerBlock_needs_lambda_bodies :
    ¬ LowerBlock env [rootKername "u"] [.construct iid 0 []] [.construct iid 0 []]
        ids defs :=
  fun h => Bool.noConfusion (h.hfl 0 Nat.zero_lt_one)

end LowerCtorBodyFixture

/-! ### What growth alone does not preserve

`Lower.const`'s premise is anti-monotone in the environment, so the pass survives growth only
because `SpecGrow`'s third clause and `ConstsDeclaredEnv` between them keep every guarded key
declared. Drop the second and the law is false: the fixture's member body names a key the
smaller environment does not declare, and the prefix declares it as an eliminator. -/

namespace SpecGrowFixture

open Lean (FVarId)

/-- The declared member's kername. -/
def aKn : Kername := ⟨.MPfile [], "sgA"⟩
/-- The key the prefix declares an eliminator at, and `Γ` does not declare at all. -/
def cKn : Kername := ⟨.MPfile [], "sgC"⟩
/-- The block key the prefix declares beside it. -/
def blkKn : Kername := ⟨.MPfile [], "sgBlk"⟩
/-- The block identifier the eliminator dispatches on. -/
def cIid : InductiveId := ⟨blkKn, 0⟩
/-- A one-constructor, non-propositional block. -/
def cMib : MutualInductiveBody := ⟨.finite, 0, [⟨"I", false, .IntoAny, [⟨"mk", 0⟩], []⟩]⟩

/-- The member's declared body: a λ over the key the prefix makes an eliminator. -/
def aBody : LBTerm := .lambda .anon (.const cKn)

/-- The smaller environment: one definition, no block, and `cKn` undeclared. -/
def gsmall : GlobalDeclarations := [(aKn, .constantDecl ⟨some aBody⟩)]

/-- The prefix: the eliminator at `cKn` together with its block. -/
def gpre : GlobalDeclarations :=
  [(cKn, .constantDecl ⟨some (mkElimBody cIid 0 0 [0])⟩), (blkKn, .inductiveDecl cMib)]

/-- The grown environment. -/
def ggrown : GlobalDeclarations := gpre ++ gsmall

/-- The block's fix variable. -/
def x : FVarId := ⟨.mkSimple "sgV0"⟩
/-- The block's fix-variable list. -/
def ids : List FVarId := [x]
/-- The block's one member. -/
def kns : List Kername := [aKn]
/-- Its declared body, as the block's source list. -/
def bs : List LBTerm := [aBody]
/-- The definition `mkDef` would emit for it. -/
def defs : List (@FixDef LBTerm) :=
  [{ name := .named "sgA", body := closeFix ids 0 aBody, principalArgIdx := 0 }]

/-- At the grown environment the prefix's key is a runtime key. -/
theorem runtimeKey_cKn : RuntimeKey ggrown cKn :=
  ⟨cIid, 0, 0, [0], ⟨_, rfl, .cases⟩, cMib, rfl, ⟨rfl, _, rfl, rfl⟩, _, rfl, rfl⟩

/-- The smaller environment declares no block, so it has no runtime key at all. -/
theorem not_runtimeKey_small {kn : Kername} : ¬ RuntimeKey gsmall kn := by
  rintro ⟨iid, np, dp, nfs, -, mib, hmib, -⟩
  rw [gsmall, LBTerm.envLookup] at hmib
  split at hmib
  · exact absurd hmib (by simp)
  · simp [LBTerm.envLookup] at hmib

/-- The one-member block, every field discharged at the smaller environment. -/
theorem lowerBlock : LowerBlock gsmall kns bs bs ids defs where
  hb := rfl
  hb' := rfl
  hd := rfl
  hnd := by decide
  hids := by simp [ids]
  hilen := rfl
  hfresh := by
    intro y _ i hi
    have h0 : i = 0 := by have : i < 1 := hi; omega
    subst h0
    simp [bs, aBody, hasFVar]
  hrarg := by decide
  hdecl := by
    intro i hi
    have h0 : i = 0 := by have : i < 1 := hi; omega
    subst h0
    rfl
  hfl := by decide
  hlow := by
    intro i hi
    have h0 : i = 0 := by have : i < 1 := hi; omega
    subst h0
    exact .lambda (.const not_runtimeKey_small)
  hcl := by
    intro i hi
    have h0 : i = 0 := by have : i < 1 := hi; omega
    subst h0
    exact ⟨aBody, .lambda (.miss (by decide)), rfl⟩

/-- The member's constant lowers to the block's `.fix` node at the smaller environment. -/
theorem lower_small : Lower gsmall (.const aKn) (.fix defs 0) :=
  Lower.fixConst' lowerBlock not_runtimeKey_small rfl


/-- The member's body is no eliminator body: an eliminator's telescope ends in a `case`. -/
theorem not_elimBody_aBody {iid : InductiveId} {np dp : Nat} {nfs : List Nat} :
    ¬ ElimBody iid np dp nfs aBody := by
  intro h
  rcases ElimBody.shape h with he | he
  · rw [mkElimBody, show dp + 1 + nfs.length = (dp + nfs.length) + 1 by omega,
      List.replicate_succ, mkLambdas, aBody] at he
    injection he with _ he
    cases hk : dp + nfs.length with
    | zero => rw [hk, List.replicate_zero, mkLambdas] at he; exact LBTerm.noConfusion he
    | succ k => rw [hk, List.replicate_succ, mkLambdas] at he; exact LBTerm.noConfusion he
  · rw [mkElimBodyRec, aBody] at he; exact LBTerm.noConfusion he

/-- The declared body at `aKn` is `aBody`. -/
theorem defn_aKn {b : LBTerm} (h : DefnDecl ggrown aKn b) : b = aBody := by
  rw [DefnDecl, show LBTerm.envLookup ggrown aKn = some (.constantDecl ⟨some aBody⟩) from rfl] at h
  injection h with h; injection h with h; injection h with h
  exact (Option.some.inj h).symm

/-- The two bodies the grown environment declares. -/
theorem body_of_grown {kn : Kername} {b : LBTerm} (h : DefnDecl ggrown kn b) :
    b = aBody ∨ b = mkElimBody cIid 0 0 [0] := by
  rw [DefnDecl, ggrown, gpre, gsmall, List.cons_append, List.cons_append, List.nil_append,
    LBTerm.envLookup] at h
  split at h
  · injection h with h; injection h with h; injection h with h
    exact .inr (Option.some.inj h).symm
  · rw [LBTerm.envLookup] at h
    split at h
    · exact absurd h (by simp)
    · rw [LBTerm.envLookup] at h
      split at h
      · injection h with h; injection h with h; injection h with h
        exact .inl (Option.some.inj h).symm
      · simp [LBTerm.envLookup] at h

/-- The smaller environment's eliminator bodies — there are none — have their blocks. -/
theorem elimBlocksDeclared_small : ElimBlocksDeclared gsmall := by
  intro kn body iid np dp nfs hlk helim
  rw [gsmall, LBTerm.envLookup] at hlk
  split at hlk
  · injection hlk with hlk; injection hlk with hlk; injection hlk with hlk
    exact absurd ((Option.some.inj hlk) ▸ helim) not_elimBody_aBody
  · simp [LBTerm.envLookup] at hlk

/-- The prefix is a growth: its keys are fresh and the smaller environment declares no
eliminator body whose block it could complete. -/
theorem specGrow_small_grown : SpecGrow gsmall ggrown :=
  SpecGrow.of_fresh (by decide) elimBlocksDeclared_small

/-- **The grown environment relates the member's body to nothing**: the body is a λ over
`cKn`, and at the grown environment `cKn` is a runtime key, which both arms whose source is
a constant forbid. The fix arms regress to the same body, which the induction closes. -/
theorem no_lower_aBody {s t : LBTerm} (h : Lower ggrown s t) : s ≠ aBody := by
  induction h using Lower.rec (motive_2 := fun _ _ _ _ => True) with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact fun hs => by simp [aBody] at hs
  | @lambda n n' b b' hb _ =>
      intro hs
      rw [aBody] at hs
      injection hs with _ hs
      exact (Lower.source_const hb hs).1 runtimeKey_cKn
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      intro hs
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he, aBody] at hs; exact LBTerm.noConfusion hs
  | @fixConst kn kns bs bs' ids defs j => exact fun hs => by simp [aBody] at hs
  | @fixBody b kns₂ bs₂ bs₂' ids₂ defs₂ j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl
      hlow hcl hj hjl ih =>
      intro hs
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      exact ih j (by omega) (hjeq.trans hs)
  | @fixEta b nm kns₂ bs₂ bs₂' ids₂ defs₂ j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl
      hlow hcl hj hjl ih =>
      intro hs
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      exact ih j (by omega) (hjeq.trans hs)
  | done | lam => trivial

/-- Hence the member's constant lowers to nothing at the grown environment. -/
theorem not_lower_grown : ¬ Lower ggrown (.const aKn) (.fix defs 0) := by
  intro h
  obtain ⟨kns₂, bs₂, bs₂', ids₂, hblk, hcase⟩ := Lower.target_fix h rfl
  rcases hcase with ⟨kn, hkn, hj⟩ | ⟨hj, hjl⟩
  · have hk : kn = aKn := by injection hkn with hk; exact hk.symm
    obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have hjk : (0 : Nat) < kns₂.length := hjb
    have hdec := hblk.hdecl 0 hjk
    rw [hjeq, hk] at hdec
    exact no_lower_aBody (hblk.hlow 0 hjk) (defn_aKn hdec)
  · obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have hjk : (0 : Nat) < kns₂.length := hblk.hb ▸ hjb
    have hdec := hblk.hdecl 0 hjk
    rw [hjeq] at hdec
    rcases body_of_grown hdec with he | he <;> simp [aBody, mkElimBody, mkLambdas] at he

/-- The smaller environment is not reference-closed: that is what the counterexample turns on. -/
theorem not_constsDeclaredEnv_small : ¬ ConstsDeclaredEnv gsmall := by
  intro h
  have hx := h aKn aBody rfl cKn (by rw [aBody, constRefs, constRefs]; exact List.mem_cons_self ..)
  rw [show LBTerm.envLookup gsmall cKn = none from rfl] at hx
  exact Bool.noConfusion hx

/-- The source's own references are declared. -/
theorem constsDeclared_small : ConstsDeclared gsmall (.const aKn) := by
  intro kn hkn
  rw [constRefs] at hkn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
  subst hkn
  rfl

/-- **`Lower` is not monotone along `SpecGrow` on the term's own references alone.** The
source's references are declared and the growth is one, yet the pass is lost: the missing
condition is on the *environment*, not on the term — `ConstsDeclaredEnv`. -/
theorem specGrow_needs_declaredEnv :
    ∃ (Γ Γ' : GlobalDeclarations) (s t : LBTerm),
      SpecGrow Γ Γ' ∧ ConstsDeclared Γ s ∧ Lower Γ s t ∧ ¬ Lower Γ' s t :=
  ⟨gsmall, ggrown, .const aKn, .fix defs 0, specGrow_small_grown,
    constsDeclared_small, lower_small, not_lower_grown⟩


end SpecGrowFixture

end LeanToLambdaBox
