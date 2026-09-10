# Reuse inventory — exact signatures of the CARRIED and RE-ANCHORED assets

Probe output for the design phase. Everything below is measured at `dev/verify` HEAD
(`d5a10f3` + the uncommitted lean4lean re-pin to `20ec229`), Lean `4.33.0-rc2`. Signatures
are transcribed verbatim from the source; `file:line` is the declaration's first line.
Axiom measurements were taken with `lake env lean` in this session and are marked
**[measured]**.

Column *Consumer* names the theorem of `doc/rework/00-REFERENCE-SPEC.md` §2 that will need
the declaration.

---

## 0. Summary index

| § | Asset | Spec class | Verdict |
|---|---|---|---|
| 1 | `Semantics/*` — flags, values, `WcbvEval`, env queries, substitution, metatheory | CARRIED | carries; **flag set is wrong at two points** (§1.1) |
| 2 | `Closed.lean` | CARRIED | carries unchanged |
| 3 | `Abstract.lean` + `Basic.lean` de-partialization | CARRIED | carries unchanged |
| 4 | `FixMetatheory.lean` / `FixUnfold.lean` | CARRIED, re-aimed at T6 `fixIntro` | carries; statements already λ□-only |
| 5 | `IotaBridge.lean` | CARRIED, re-aimed at T6 `elimInline` | carries unchanged |
| 6 | `Erasability.lean` | CARRIED | carries unchanged |
| 7 | `Relevance`/`RelevanceCheck`/`CheckerAdequacy`/`OracleDischarge` | CARRIED, must enter capstone closure | carries; **costs 33 axioms** (§7.5) |
| 8 | `Optimize.lean` | CARRIED as T6 template | **statement is at block form; the pass arms must be re-proved** (§8.3) |
| 9 | `FirstOrder.lean:103-155` | CARRIED, re-indexed | carries; class B (`sorryAx`) [measured] |
| 10 | `ErasureRun.lean` (74 `run_*` + `RunConcl`) | RE-ANCHORED | survives intact; relation-independent |
| 11 | `VisitExprRefines.lean` (18 motives, `BridgeInv`, `⊑`) | RE-ANCHORED | scaffolding survives; 18 conclusions restated |
| 12 | `ColdStart{Run,Shape,Induction}` | RE-ANCHORED | `erase_run_ok`, `visitExpr_shape_all` durable |
| 13 | `SubjectReduction{,Full,Iota}` | RE-ANCHORED | three `*_defeq`, one survives as T4 `SEval.defeq` |
| 14 | `Erases` transport metatheory | RE-ANCHORED | per-rule inductions; 6 of 15 rules die |
| 15 | `EnvErasure{,Nonrec,Rec}` | RE-ANCHORED | restated as T3 `ErasesEnv` |
| 16 | Shipping diff `dev/verify` vs `dev/bump-4.33` | CARRIED (proof-only part only) | 6 behaviour-affecting edits isolated (§16) |

---

## 1. `Semantics/*` — T1

`LeanToLambdaBox/Semantics/{Flags,Values,Eval,Env,Substitution,Metatheory}.lean`, 1,225 lines.

### 1.1 Flags — `Semantics/Flags.lean:36`

```lean
structure WcbvFlags where
  with_prop_case            : Bool
  with_guarded_fix          : Bool
  with_constructor_as_block : Bool
  deriving Repr, DecidableEq

def defaultFlags : WcbvFlags := ⟨true,  true,  true⟩   -- :46
def optFlags     : WcbvFlags := ⟨false, true,  true⟩   -- :50
def targetFlags  : WcbvFlags := ⟨false, false, true⟩   -- :54
def appliedFlags : WcbvFlags := ⟨false, true,  false⟩  -- :59
```

**Two mismatches against the spec, both load-bearing.**

1. The spec's `eraseFlags := ⟨with_prop_case := true, with_guarded_fix := true,
   with_constructor_as_block := false⟩` **does not exist** in the tree. The nearest is
   `appliedFlags`, which differs in `with_prop_case`. Every T5/T6 statement therefore
   needs a new flag constant, and nothing currently instantiates `WcbvEval` at
   `⟨true, true, false⟩`.
2. The tree's `targetFlags` is `⟨false, false, **true**⟩` — block form. The spec's
   `targetFlags` (T6, T9) must be `⟨false, _, false⟩`. The name collides; rename or
   redefine, and note that no current theorem is stated at the spec's target point.
3. `Flags.lean:19-24`'s header asserts "we are always block form … we pin this to `true`
   and do not model the accumulation rules". This is false — `construct_atom` /
   `construct_app` / `iota` / `proj` are all present in `Eval.lean` — and the spec §4.1
   already requires the rewrite.

### 1.2 `WcbvEval` — `Semantics/Eval.lean:79`, 22 rules

```lean
inductive WcbvEval (Γ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → LBTerm → Prop
```

| line | rule | gate |
|---|---|---|
| 81 | `box` | — |
| 83 | `lam` | — |
| 85 | `fvar` | — (Lean-only extension) |
| 87 | `prim` | — |
| 89 | `fix_atom` | — |
| 92 | `beta` | — |
| 97 | `app_box` | — (**amendment (1)**) |
| 100 | `zeta` | — (ζ is present; T4's "no capstone can evaluate a `let`" is a capstone-side gap, not a semantics gap) |
| 103 | `delta` | — |
| 109 | `construct` | `hb : with_constructor_as_block = true` |
| 118 | `construct_atom` | `hb : … = false` |
| 130 | `construct_app` | `hb : … = false` |
| 143 | `iota` | `hb : … = false` |
| 157 | `iota_block` | `hb : … = true` |
| 171 | `iota_sing` | `hpc : with_prop_case = true` (**amendment (2)**) |
| 181 | `proj` | `hb : … = false` |
| 191 | `proj_block` | `hb : … = true` |
| 200 | `proj_prop` | `hpc : with_prop_case = true` |
| 210 | `fix_guarded` | `hg : with_guarded_fix = true` (**amendment (3)**) |
| 224 | `fix_stuck` | `hg : … = true` |
| 235 | `fix_unguarded` | `hg : … = false` |
| 245 | `app_cong` | — |

`abbrev Eval Γ := WcbvEval Γ optFlags` (:251); `abbrev EvalProp Γ := WcbvEval Γ defaultFlags` (:255).

### 1.3 Metatheory — `Semantics/Metatheory.lean`

```lean
theorem value_final {Γ : GlobalDeclarations} {fl : WcbvFlags} {v : LBTerm} :          -- :55
    Value Γ fl v → WcbvEval Γ fl v v

theorem eval_to_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm} :      -- :90
    WcbvEval Γ fl t v → Value Γ fl v

theorem eval_deterministic {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}   -- :138
    (h1 : WcbvEval Γ fl t v) : ∀ {v'}, WcbvEval Γ fl t v' → v = v'

theorem eval_value {Γ : GlobalDeclarations} {fl : WcbvFlags} {v v' : LBTerm}          -- :379
    (hv : Value Γ fl v) (h : WcbvEval Γ fl v v') : v = v'

theorem eval_unique {Γ fl t v} (h1 h2 : WcbvEval Γ fl t v) : h1 = h2 := rfl           -- :385
```

All four are **flag-polymorphic** — no `fl` is pinned — so the flag-set change of §1.1
costs nothing here. Non-vacuity guards already exist and are the model criterion 5 asks
for: `value_final_hyps_satisfiable` (:402), `eval_hyps_satisfiable` (:409),
`eval_deterministic_fires` (:417), `construct_app_fires` (:457) and `construct_app_value`
(:469) — the last two at `appliedFlags`, i.e. exactly the applied-constructor form the
spec makes primary — plus `mf_fix_stuck`/`mf_fix_value` (:490, :496) for the fixpoint rule.

**Axioms [measured]:** `eval_deterministic` → `[propext, Classical.choice, Quot.sound]`;
`eval_to_value` → `[propext]`; `value_final` → `[propext, Quot.sound]`. **Trust class A
confirmed.**

### 1.4 Values and env queries

```lean
def atomValue    : LBTerm → Prop                                       -- Values.lean:35
def isStuckApp   (fl : WcbvFlags) (f : LBTerm) : Bool                  -- Values.lean:71
inductive Value  (Γ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → Prop  -- Values.lean:85

def isPropositionalInductive (Γ : GlobalDeclarations) (iid : InductiveId) : Bool  -- Env.lean:21
def wouldCollapse (Γ : GlobalDeclarations) (iid : InductiveId)
    (alts : List (List BinderName × LBTerm)) : Bool                    -- Env.lean:31
def constructorArity (Γ : GlobalDeclarations) (iid : InductiveId) (c : Nat) : Option Nat -- Env.lean:44
```

`isPropositionalInductive` is the *target-side* subsingleton test that `iota_sing` and
`LBOptimize` consult. It is a query on the **erased** environment, so T3's
`Subsingleton`/large-elimination obligation (Q2) is about producing an environment on
which this predicate is correct, not about redefining it.

### 1.5 Substitution — `Semantics/Substitution.lean`, 30 declarations

Definitions: `shift`/`shiftArgs`/`shiftAlts`/`shiftDefs` (:48-71), `subst`/`substArgs`/
`substAlts`/`substDefs`/`subst1` (:78-110), `substList` (:118), `mkApps` (:124),
`spineHead`/`spineArgs` (:130,:137), `fixSubst` (:220), `envLookup` (:35),
`Kername.beq`/`ModPath.beq` (:18,:26).

Load-bearing lemmas for the pass layer:

```lean
theorem mkApps_concat  (f) (args) (a) : mkApps f (args ++ [a]) = app (mkApps f args) a  -- :143
theorem spineHead_mkApps (f) (args) : spineHead (mkApps f args) = spineHead f           -- :149
theorem spineArgs_mkApps (f) (args) : spineArgs (mkApps f args) = spineArgs f ++ args   -- :155
theorem mkApps_construct_inj  … : iid = iid' ∧ c = c' ∧ args = args'                    -- :177
theorem mkApps_fix_inj        … : defs = defs' ∧ i = i' ∧ argsv = argsv'                -- :192
theorem mkApps_construct_ne_fix … : mkApps (construct iid c []) args ≠ mkApps (fix defs i) argsv -- :207
```

The three injectivity/disjointness lemmas are stated at *applied* form
(`construct iid c []` with args by `mkApps`) and are what `ctorInline` and `elimInline`
will need for head analysis.

---

## 2. `Closed.lean` — CARRIED unchanged, 871 lines, 50 declarations

Definitions: `LBClosed`, `LBClosedArgs`, `LBClosedAlts`, `LBClosedDefs` + their `_iff`
characterisations.

Lemma inventory (all `LBTerm`-only, no lean4lean, no `Erases`):

`LBClosed.shift_eq`, `.subst_eq`, `lbClosed_of_shift_eq`, `LBClosed.mono`, `.shift`,
`.subst_gen`, `.subst`, `.subst1_gen`, `.subst1`, `.substList`, `.mkApps`, `.mkApps_head`,
`.mkApps_inv`, `.mkLambdas`, `.mkLambdas_inv`, `LBTerm.shift_bvar`, `.subst_bvar`,
`.shift_shift`, `.subst_shift_cancel`, `.subst_shift_comm`, `.subst_subst_gen`,
`.subst_subst`, `.substList_append`, `.substList_concat`, `.substList_reverse_subst`,
`lbClosed_toBvar`, `lbClosed_foldl_toBvar`, `lbClosed_foldl_zipIdx`,
`lbClosed_foldl_zipIdx_map`, `lbClosed_fix_of_bodies`.

*Consumer:* T1 (`WcbvEval` side conditions), T6 (`LBPass.correct`'s `LBClosed t`
hypothesis), T8 (`mkAlt`/`mkLambda` output shape), T9 (`LBWfPeregrine`).

**Known duplicate to delete, not carry:** `LBTerm.subst_shift_cancel` and
`subst_shift_cancel` print identical types (review R1).

---

## 3. `Abstract.lean` + `Basic.lean` de-partialization — CARRIED unchanged

`Abstract.lean`, 423 lines, 27 declarations. Definitions `hasFVar`/`hasFVarArgs`/
`hasFVarAlts`/`hasFVarDefs` and the `toBvar` metatheory:

`toBvarArgs_eq_map`, `toBvarAlts_eq_map`, `toBvarDefs_eq_map`, `abstract_eq`,
`hasFVarArgs_iff`, `hasFVarAlts_iff`, `hasFVarDefs_iff`, `fvarId_beq_iff_eq`,
`toBvar_eq_of_not_hasFVar` (+ the three list variants), `abstract_eq_of_not_hasFVar`,
`toBvarDefs_length`, `shiftDefs_length`, `toBvar_shift` (+ three variants),
`toBvar_toBvar` (+ three variants).

Rests on `Basic.lean`'s `toBvar`/`toBvarArgs`/`toBvarAlts`/`toBvarDefs` mutual block
(the de-partialization; see §16). *Consumer:* T2's `Erases.abstract`/`.uninstantiate`
(the fvar↔de Bruijn transport §3.3 of the spec calls Lean-only), T8 (`mkLambda`,
`mkLetIn`, `mkAlt` all produce `toBvar` applications).

---

## 4. `FixMetatheory.lean` + `FixUnfold.lean` — CARRIED, re-aimed at T6 `fixIntro`

1,184 lines, 62 declarations. Everything is `LBTerm`-only.

```lean
def closeFixFold : List (FVarId × Nat) → LBTerm → LBTerm      -- FixMetatheory.lean:51
def closeFix (ids : List FVarId) (base : Nat) (t : LBTerm) : LBTerm  -- :60
```

**The pivot lemma:**

```lean
theorem closeFix_substList_fixSubst                                    -- FixUnfold.lean:748
    {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hilen : ids.length = defs.length)
    (hdefs : ∀ j, LBClosed (LBTerm.fix defs j) 0)
    (hfv : ∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j))
    (hcl : LBClosed t 0) :
    LBTerm.substList (LBTerm.fixSubst defs) (closeFix ids 0 t) = substFix ids defs t
```

plus the general form `closeFix_substList_fixSubst_gen` (:690) and the non-vacuity
guards `closeFix_substList_fixSubst_fires` / `_fires_value` (:762, :770).

**The unfolding chain:**

```lean
inductive FixUnfoldChain : List (@FixDef LBTerm) → Nat → LBTerm → Prop   -- FixUnfold.lean:800
  | step  {defs idx} (hidx : idx < defs.length)
          (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0) :
      FixUnfoldChain defs idx (LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body)
  | trans {defs idx defs' idx' u}
          (hidx : idx < defs.length) (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
          (heq : LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body = .fix defs' idx')
          (h : FixUnfoldChain defs' idx' u) : FixUnfoldChain defs idx u

theorem FixUnfoldChain.eval {E : GlobalDeclarations} {fl : WcbvFlags}     -- FixUnfold.lean:830
    (hg : fl.with_guarded_fix = true)
    {defs idx u} (hch : FixUnfoldChain defs idx u) :
    ∀ {f a av r : LBTerm}, WcbvEval E fl f (.fix defs idx) → WcbvEval E fl a av →
      WcbvEval E fl (.app u av) r → WcbvEval E fl (.app f a) r

theorem FixUnfoldChain.lbClosed {defs idx u} (hch : FixUnfoldChain defs idx u) :  -- :853
    LBClosed (.fix defs idx) 0 → LBClosed u 0

theorem LBTerm.fix_or_not (t : LBTerm) :                                          -- :817
    (∃ defs i, t = .fix defs i) ∨ …
theorem hasFVar_toBvar (x y : FVarId) : ∀ t lvl, hasFVar x (toBvar y lvl t) → x ≠ y ∧ hasFVar x t  -- :901
theorem fixUnfoldChain_selfLoop_step : FixUnfoldChain nvDefs 0 (.fix nvDefs 0)    -- :874 (guard)
```

**Axioms [measured]:** `closeFix_substList_fixSubst` → `[propext, Quot.sound]`. **Class A.**

*Consumer:* T6 `fixIntro.correct`. `FixUnfoldChain.eval` is stated at
`with_guarded_fix = true`, which both `eraseFlags` and `appliedFlags` satisfy; the
`with_constructor_as_block` flag is never read. Note `FixUnfoldChain.step`'s
`hrarg : ∀ d ∈ defs, d.principalArgIdx = 0` — the shipping `mkDef` emits `principalArgIdx`
from the declaration, so `fixIntro` will need this as a side condition or a generalisation.

---

## 5. `IotaBridge.lean` — CARRIED unchanged, re-aimed at T6 `elimInline`

207 lines, 4 declarations, `Erases`-free and lean4lean-free.

```lean
theorem wcbvEval_mkApps_head_congr {E : GlobalDeclarations} {fl : WcbvFlags} :   -- :40
    ∀ (args : List LBTerm) {g h : LBTerm},
      (∀ {v : LBTerm}, WcbvEval E fl g v → WcbvEval E fl h v) →
      ∀ {r : LBTerm}, WcbvEval E fl (LBTerm.mkApps g args) r →
        WcbvEval E fl (LBTerm.mkApps h args) r

theorem value_mkApps_construct_args {E : GlobalDeclarations} {fl : WcbvFlags}    -- :69
    {iid : InductiveId} {c : Nat} :
    ∀ (n : Nat) {args : List LBTerm}, args.length = n →
      Value E fl (LBTerm.mkApps (.construct iid c []) args) → ∀ x ∈ args, Value E fl x

theorem wcbvEval_mkApps_mkLambdas_substList {E : GlobalDeclarations} {fl : WcbvFlags} :  -- :111
    ∀ (fields : List LBTerm) (names : List BinderName) (body : LBTerm),
      names.length = fields.length →
      (∀ x ∈ fields, WcbvEval E fl x x) → (∀ x ∈ fields, LBClosed x 0) →
      ∀ {r : LBTerm}, WcbvEval E fl (LBTerm.mkApps (mkLambdas names body) fields) r →
        WcbvEval E fl (LBTerm.substList fields.reverse body) r

theorem wcbvEval_mkApps_mkLambdas_substList_fires :                              -- :192 (guard)
    WcbvEval [] appliedFlags
      (LBTerm.substList ([(.box : LBTerm), .lambda (.named "y") .box].reverse) (.bvar 1)) .box
```

**Axioms [measured]:** `wcbvEval_mkApps_mkLambdas_substList` →
`[propext, Classical.choice, Quot.sound]`. **Class A.**

*Consumer:* T6 `elimInline.correct` — this is the "β-chain of field applications *is*
`iota_red`" lemma the spec's pass table names. Fully flag-polymorphic; the non-vacuity
guard is already at `appliedFlags`. `value_mkApps_construct_args` supplies the
`∀ x ∈ fields, WcbvEval E fl x x` premise by way of `value_final`.

---

## 6. `Erasability.lean` — CARRIED unchanged, 230 lines, 14 declarations

```lean
inductive IsArity : VExpr → Prop                                        -- :34
def IsArityUpTo (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop  -- :43
def Erasable (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop     -- :56
```

`Erasable` is `∃ A, HasType U Γ e A ∧ (HasType U Γ A (.sort .zero) ∨ IsArityUpTo env U Γ A)` —
the two disjuncts kept separate, exactly as spec §3.2 requires.

Stability kit (= Letouzey Lemma 2):

```lean
theorem IsArity.inst   {A} (h : IsArity A) (e₀ : VExpr) (k : Nat) : IsArity (A.inst e₀ k)   -- :67
theorem IsArity.liftN  {A} (h : IsArity A) (n k : Nat) : IsArity (A.liftN n k)              -- :73
theorem IsArityUpTo.inst  (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) (h : IsArityUpTo env U Γ₁ A) :
    IsArityUpTo env U Γ (A.inst e₀ k)                                                        -- :79
theorem IsArityUpTo.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ')
    (h : IsArityUpTo env U Γ A) : IsArityUpTo env U Γ' (A.liftN n k)                         -- :87
theorem IsArityUpTo.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hAA : env.IsDefEqU U Γ A'' A) (h : IsArityUpTo env U Γ A) : IsArityUpTo env U Γ A''      -- :99
theorem Erasable.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hee : env.IsDefEqU U Γ e e') (h : Erasable env U Γ e) : Erasable env U Γ e'              -- :112
theorem IsArityUpTo.defeqDFC (henv : env.Ordered) (hΓ : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (h : IsArityUpTo env U Γ₁ A) : IsArityUpTo env U Γ₂ A                                     -- :121
theorem Erasable.defeqDFC (henv : env.Ordered) (hΓ : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (h : Erasable env U Γ₁ e) : Erasable env U Γ₂ e                                           -- :130
theorem Erasable.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ')
    (h : Erasable env U Γ e) : Erasable env U Γ' (e.liftN n k)                                -- :142
theorem Erasable.inst (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) (h : Erasable env U Γ₁ e) : Erasable env U Γ (e.inst e₀ k)  -- :156
theorem Erasable.app (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : Erasable env U Γ f) (hTf : env.HasType U Γ f (.forallE A B))
    (hTa : env.HasType U Γ a A) : Erasable env U Γ (.app f a)                                 -- :179
```

**Axioms [measured]:** `Erasable.inst` → `[propext, Quot.sound]`. Note: the *stability
kit itself* is class A — it does not go through `TrExprS.uniq`. `Erasable.app` and
`.defeq` take `env.WF` and will inherit `sorryAx` only where a caller supplies a WF from
the sorry-carrying cluster.

*Consumer:* T2 `Erases.box`'s premise; `erases_subst`'s pivot; T7's non-erasability
argument; T8 field 4.

---

## 7. The verified relevance oracle — CARRIED, must enter the capstone closure

495 lines across four files. This is the development's only trust *reduction*.

### 7.1 `Relevance.lean` — the executable check (namespace `LeanToLambdaBox`)

```lean
def isErasableProp (e : Expr) : Lean4Lean.TypeChecker.RecM Bool                   -- :25
def isArityCheck.loop (fuel : Nat) (ty : Expr) : Lean4Lean.TypeChecker.RecM Bool  -- :31
def isArityCheck (ty : Expr) : Lean4Lean.TypeChecker.RecM Bool                    -- :44
def isErasable (e : Expr) : Lean4Lean.TypeChecker.RecM Bool                       -- :50
  -- := do let ty ← inferType e; if (← isProp ty) then return true else isArityCheck ty
```

### 7.2 `RelevanceCheck.lean` — soundness in lean4lean's `M.WF` calculus

```lean
theorem isErasableProp.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}     -- :67
    (he : c.TrExprS e e') :
    (isErasableProp e).WF c s fun b _ => b → Erasable c.venv c.lparams.length c.vlctx.toCtx e'

theorem IsArityUpTo.forallE {env : VEnv} (henv : env.WF) {U Γ A B}                -- :84
    (hΓ : OnCtx Γ (env.IsType U)) (hA : env.IsType U Γ A) (hB : env.IsType U (A :: Γ) B)
    (h : IsArityUpTo env U (A :: Γ) B) : IsArityUpTo env U Γ (.forallE A B)

theorem isArityCheck.loop.WF {c s ty ty' fuel} (hty : c.TrExprS ty ty') :         -- :104
    (isArityCheck.loop fuel ty).WF c s fun b _ =>
      b → IsArityUpTo c.venv c.lparams.length c.vlctx.toCtx ty'

theorem isArityCheck.WF {c s ty ty'} (hty : c.TrExprS ty ty') :                   -- :133
    (isArityCheck ty).WF c s fun b _ => b → IsArityUpTo c.venv c.lparams.length c.vlctx.toCtx ty'

theorem isErasable.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}         -- :145
    (he : c.TrExprS e e') :
    (isErasable e).WF c s fun b _ => b → Erasable c.venv c.lparams.length c.vlctx.toCtx e'
```

### 7.3 `CheckerAdequacy.lean` — from `M.WF` to a real run (namespace `Lean4Lean.TypeChecker`)

```lean
def kernelNGen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }      -- :54
def VContext.ofMLCtx {env : Environment} {ves : VEnvs} (wf : ves.WF env)          -- :59
    (safety : DefinitionSafety := .safe) (lparams : List Name := [])
    (fuel : FuelConfig := {}) (m : MLCtx) (mwf : m.WF (ves.venv safety) lparams) : VContext
-- + three @[simp] projections (:73, :78, :83)

theorem VState.WF.initial … (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) : -- :94
    VState.WF (.ofMLCtx wf safety lparams fuel m mwf) {}

theorem M.WF.run' {env ves} (wf : ves.WF env) {safety lparams fuel m}             -- :112
    (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {x : M α} {Q} (H : x.WF (.ofMLCtx wf safety lparams fuel m mwf) {} fun a _ => Q a) :
    (M.run env safety m.lctx lparams fuel x).WF Q

theorem kernel_isErasable_sound {env : Environment} {ves : VEnvs} (wf : ves.WF env)  -- :130
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {e : Expr} {ve : VExpr}
    (he : TrExprS (ves.venv safety) lparams m.vlctx e ve)
    (hrun : M.run env safety m.lctx lparams fuel
      (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true) :
    Erasable (ves.venv safety) lparams.length m.vlctx.toCtx ve
```

**Fully-qualified name is `Lean4Lean.TypeChecker.kernel_isErasable_sound`** — this file
declares eight `Lean4Lean.TypeChecker`-namespace declarations in *this* repository, which
acceptance criterion 21 ("no `Lean4Lean`-namespace declaration in this repository")
forbids. Either the criterion admits an exception for the adequacy layer, or these eight go
upstream. Flag for the design decision.

### 7.4 `OracleDischarge.lean` — the residual bundle

```lean
structure ResidualHyps (env₀ : Lean.Kernel.Environment) (ves : VEnvs) (Us : List Name)  -- :65
    (Γ : ErasureCtx) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  orc_refl  : …  -- for every `liftMetaM (isErasable ctx.lparams e)` run returning `b`:
                 --   gw w ≤ gw w₁, and if `b = true` and `ctx.lparams <+: Us` then either
                 --   (kernel branch) ctx.lparams = Us ∧ M.run env₀ .safe … = .ok true
                 --   (Meta fallback) ∀ m ve, m.WF … → TrExprS … → Erasable …
  fresh_run : …  -- mkFreshFVarId: ¬(gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁
                 --   ∧ kernelNGen.Reserves x
  cases_run : …  -- getCasesInfo? n = r → gw w ≤ gw w₁ ∧ (Γ.casesOns n = none → r = none)
  ctor_run  : …  -- LCNF.getCtorArity? n = r → gw w ≤ gw w₁ ∧ (Γ.ctors n = none → r = none)

theorem ResidualHyps.toBridgeHyps {env₀ ves Us Γ gw}                              -- :106
    (R : ResidualHyps env₀ ves Us Γ gw) (wf : ves.WF env₀) : BridgeHyps (ves.venv .safe) Us Γ gw
```

`ResidualHyps` is a **four-field**, already-`PrimSpec`-shaped bundle: `orc_refl` is
spec field 4 (partly discharged, partly the `Meta` fallback), `fresh_run` is field 3,
`cases_run`/`ctor_run` are field 2. Spec field 1 (`env_connect` / `abs_env_irr`) appears
here as the parameter pair `(env₀, ves)` plus the `wf : ves.WF env₀` argument to
`toBridgeHyps`, and is *not* a field. **`PrimSpec` can be built by renaming
`ResidualHyps` and adding one `env_connect` field.**

### 7.5 [measured] The axiom cost of routing the oracle into the capstone

| theorem | # axioms | includes |
|---|---|---|
| `LeanToLambdaBox.isErasable.WF` | 8 | `propext, sorryAx, Classical.choice, Quot.sound` + 4 Lean-core model axioms |
| `Lean4Lean.TypeChecker.kernel_isErasable_sound` | **33** | the above + `Lean4Lean.ptrEqExpr_eq`, `ptrEqConstantInfo_eq`, … and **two `_native.bv_decide` axioms** (`Lean.Expr.mkData_flags._native.bv_decide.ax_1_12`, `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7`) |
| `LeanToLambdaBox.ResidualHyps.toBridgeHyps` | **33** | same set |

**Design consequence.** Acceptance criterion 9 (route `OracleDischarge` into the capstone)
and criterion 15 (`#print axioms` matches a committed fixture) interact: satisfying 9
enlarges the capstone's axiom set from ~8 to ~33, and two of the new entries are
`bv_decide`-generated native axioms from Lean core, which the T11 ledger must classify.
The alternative — leaving `oracle_sound` as a class-**D** field — keeps the fixture small
but forfeits the development's only trust reduction. The spec chooses 9; the ledger must
therefore have an "inherited from lean4lean's executable checker" row with all 29
non-standard names, not just the `sorryAx` cluster.

---

## 8. `Optimize.lean` — CARRIED as T6's template, **but the statement is at the wrong flags**

1,090 lines, 79 declarations, currently consumer-free.

### 8.1 The pass

```lean
def caseCollapse (info : InductiveId × Nat) (isProp : Bool)                       -- :27
def projCollapse (Γ : GlobalDeclarations) (p : ProjectionInfo) (e' : LBTerm) : LBTerm  -- :39
mutual
def LBOptimize     (Γ : GlobalDeclarations) : LBTerm → LBTerm                     -- :49
def LBOptimizeArgs (Γ : GlobalDeclarations) : List LBTerm → List LBTerm
def LBOptimizeAlts (Γ : GlobalDeclarations) : List (List BinderName × LBTerm) → …
def LBOptimizeDefs (Γ : GlobalDeclarations) : List (@FixDef LBTerm) → …
end
def LBOptimize_env (Γ : GlobalDeclarations) : GlobalDeclarations :=              -- :81
  Γ.map fun (kn, d) => match d with
    | .constantDecl ⟨some body⟩ => (kn, .constantDecl ⟨some (LBOptimize Γ body)⟩)
    | _ => (kn, d)
```

### 8.2 The correctness theorem and its guards

```lean
theorem LBOptimize_correct {Γ : GlobalDeclarations} {t v : LBTerm} :              -- :927
    EvalProp Γ t v → Eval (LBOptimize_env Γ) (LBOptimize Γ t) (LBOptimize Γ v)

theorem LBOptimize_correct_hyps_satisfiable : EvalProp vacΓ vacTerm .box          -- :1066
theorem LBOptimize_correct_not_refutable : ∃ Γ t v, EvalProp Γ t v                -- :1076
theorem LBOptimize_correct_fires : Eval (LBOptimize_env vacΓ) .box .box           -- :1083
```

**Axioms [measured]:** `LBOptimize_correct` → `[propext, Quot.sound]`. **Class A confirmed.**

Distribution lemmas the pass layer reuses verbatim: `LBOptimize_shift_comm` (:160),
`LBOptimize_subst_comm` (:164), `LBOptimize_substList_box` (:169), `LBOptimize_substList`
(:173), `LBOptimize_fixSubst`, `LBOptimize_fixUnfold_body` (:901), `LBOptimize_iota_red`
(:909), `envLookup_LBOptimize_env` (:740), `LBOptimize_env_eq_map` (:845),
`isPropositionalInductive_LBOptimize_env` (:871), `projCollapse_subst`/`_shift` (:392,:397),
`caseCollapse_subst`/`_shift` (:517,:533), `caseCollapse_prop_single`/`_nil`/`_cons2`/
`_nonprop` (:412-425).

### 8.3 The flag problem — the single largest re-proof cost in the CARRIED list

`EvalProp = WcbvEval Γ defaultFlags = ⟨true, true, **true**⟩` and
`Eval = WcbvEval Γ optFlags = ⟨false, true, **true**⟩`. **Both are block form.**
The spec needs `optimize : ⟨true, true, false⟩ → ⟨false, true, false⟩`.

Measured on the proof body (`Optimize.lean:927-1030`), the twenty-two rule arms split:

| arms | today | at applied form |
|---|---|---|
| `box`, `lam`, `fvar`, `prim`, `fix_atom`, `beta`, `app_box`, `zeta`, `delta`, `iota_sing`, `proj_prop`, `fix_guarded`, `fix_stuck`, `app_cong` (14) | proved | **transfer verbatim** — none reads `with_constructor_as_block` |
| `construct`, `iota_block`, `proj_block` (3) | proved, block-specific | become unreachable (`simp [eraseFlags] at hb`) |
| `construct_atom`, `construct_app`, `iota`, `proj` (4) | discharged as unreachable by `simp [defaultFlags] at hb` | **must be proved** |
| `fix_unguarded` (1) | unreachable (`hg`) | still unreachable |

So the re-proof is exactly **four new arms** (and the `iota`/`proj` arms have their block
twins to copy from, with `LBOptimize_iota_red` and `projCollapse_subst` already stated
form-independently). Best route: generalise the statement to
`WcbvEval Γ ⟨true, g, b⟩ t v → WcbvEval (LBOptimize_env Γ) ⟨false, g, b⟩ …` and prove all
seven constructor/ι/proj arms, which then discharges T6 `optimize` at any flag point.

---

## 9. `FirstOrder.lean:103-155` — CARRIED, re-indexed onto `FirstOrderInd`

```lean
def InformativeType (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop := -- :49
  ∃ ve A, TrExprS env Us Δ e ve ∧ env.HasType Us.length Δ.toCtx ve A ∧
    ¬ env.HasType Us.length Δ.toCtx A (.sort .zero) ∧
    ¬ IsArityUpTo env Us.length Δ.toCtx A

inductive FirstOrderValue (env : VEnv) (Us : List Name) (Γ : ErasureCtx) :          -- :71
    VLCtx → Expr → Prop
  | ctor {Δ} (cn) (us) (iid) (cidx) {args}
      (hc : Γ.ctors cn = some (iid, cidx)) (hcas : Γ.casesOns cn = none)
      (info : InformativeType env Us Δ (args.foldl Expr.app (.const cn us)))
      (hargs : ∀ i (h : i < args.length), FirstOrderValue env Us Γ Δ args[i]) :
      FirstOrderValue env Us Γ Δ (args.foldl Expr.app (.const cn us))

theorem informativeType_not_erasable {env : VEnv} (henv : env.WF) {Us : List Name}  -- :103
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (info : InformativeType env Us Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ¬ Erasable env Us.length Δ.toCtx ve

theorem firstOrderValue_not_erasable {env : VEnv} (henv : env.WF) {Us : List Name}  -- :133
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {v : Expr} (hfo : FirstOrderValue env Us Γ Δ v)
    {ve : VExpr} (htr : TrExprS env Us Δ v ve) :
    ¬ Erasable env Us.length Δ.toCtx ve
```

**Axioms [measured]:** `informativeType_not_erasable` →
`[propext, sorryAx, Classical.choice, Quot.sound]`. **Class B**, exactly as T7 predicts:
the `sorryAx` enters through `TrExprS.uniq` and `VEnv.IsDefEq.uniqU`, the two named seams.

**What carries and what does not.** `informativeType_not_erasable` (:103-131) is
*independent of `FirstOrderValue`* — it is stated over `InformativeType`, which mentions
neither `Γ` nor a constructor spine. It therefore **carries unchanged** and is the whole
proof content T7 needs; only the four-line wrapper `firstOrderValue_not_erasable`
(:133-141) is re-indexed. The spec's T7 must supply a bridge
`FirstOrderInd env I → HasType ve (mkApps (.const I us) args) → InformativeType env Us [] v`
— i.e. "a value at a first-order inductive type has an informative type" — which is new
and is the only genuinely new obligation in this asset.

`FirstOrder.lean`'s other 700 lines (`eraseArgs_mono`, `eraseCore` fuel monotonicity, A3)
are keyed on `eraseCore` and the deleted `Erases.ctor`; §4.3 of the spec deletes them
except the fuel/monotonicity lemmas.

---

## 10. `ErasureRun.lean` — RE-ANCHORED, survives intact

3,234 lines, 141 top-level declarations, of which **74 are named `run_*`** (the spec says
75; the 75th is `Erasure.run_eq`, which lives in `ColdStartRun.lean:644`).

### 10.1 `RunConcl` and its neighbours — the run-algebra vocabulary

```lean
def CanonicalConstants (s : ErasureState) : Prop :=                              -- :1482
  ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = toKername n

def addAxiomState (n : Name) (s : ErasureState) : ErasureState                   -- :1485

structure ConstExt (s s' : ErasureState) : Prop where                            -- :1498
  canon  : CanonicalConstants s → CanonicalConstants s'
  dom    : ∀ {n : Name}, (s.constants.get? n).isSome → (s'.constants.get? n).isSome
  gdecls : ∃ pre : GlobalDeclarations, s'.gdecls = pre ++ s.gdecls ∧
    ∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩ ∧
      ∃ m : Name, p.1 = toKername m ∧ (s'.constants.get? m).isSome

structure AxiomExt (s s' : ErasureState) : Prop extends ConstExt s s' where       -- :1505
  inds : s'.inductives = s.inductives

structure StateLe (s s' : ErasureState) : Prop where                             -- :1585
  consts : ∀ {n : Name}, (s.constants.get? n).isSome → (s'.constants.get? n).isSome
  inds   : ∀ {n : Name}, (s.inductives.get? n).isSome → (s'.inductives.get? n).isSome
  gdecls : ∃ pre : GlobalDeclarations, s'.gdecls = pre ++ s.gdecls

structure RunConcl (s s' : ErasureState) : Prop where                            -- :1609
  le    : StateLe s s'
  canon : CanonicalConstants s → CanonicalConstants s'
```

with `RunConcl.rfl'` (:1613), `.of_eq` (:1616), `.trans` (:1619); `StateLe.rfl'`/`.trans`
(:1590,:1595); `ConstExt.rfl'`/`.of_same`/`.trans` (:1508,:1513,:1519);
`AxiomExt.rfl'`/`.trans`/`.addAxiom` (:1534,:1538,:1543).

**`RunConcl` is the shape every one of the 18 motives concludes**, and it mentions neither
`Erases` nor `ErasureCtx`. It carries into T8 unchanged. `RunConclδ` (the δ-record
variant that the motives actually use) lives in `DeltaHyps.lean` and is spec-deleted;
motives must be restated with `RunConcl` plus T3's `ErasesEnv`.

### 10.2 The 74 `run_*` lemmas, by family

**Monad algebra (22):** `run_pure` :78, `run_bind` :85, `run_bind_ok` :105,
`run_bind_ne_ok` :126, `run_get` :135, `run_set` :139, `run_modify` :143,
`run_modifyGet` :147, `run_read` :154, `run_read_bind` :161, `run_withReader` :166,
`run_throw` :170, `run_throw_ne_ok` :174, `run_throwError_ne_ok` :182,
`run_liftCoreM` :197, `run_liftCoreM_ok` :214, `run_liftCoreM_state` :229,
`run_liftMetaM` :235, `run_liftMetaM_ok` :245, `run_liftMetaM_state` :260,
`run_panic` :267, `run_panicWithPosWithDecl` :272.

**Approximation (2):** `run_ok_of_le` :492, `run_ok_of_le₁` :508.

**Loop/traversal algebra (11):** `run_list_forIn'_ok` :704, `run_list_forIn_ok` :739,
`run_array_forIn_ok` :773, `run_list_forIn_ok'_go` :787, `run_list_forIn_ok'` :824,
`run_array_forIn_ok'` :843, `run_list_foldlM_ok_go` :860, `run_list_foldlM_ok` :887,
`run_array_foldlM_ok` :902, `run_list_mapM_ok_go` :917, `run_list_mapM_ok` :948.

**Primitive state effects (5):** `run_monadRefWithRef` :1429, `run_logInfo_state` :1433,
`run_getEnv_state` :1438, `run_mkFreshFVarId_state` :1442, `run_getConstInfo_state` :1447.

**Registration (7):** `run_addAxiom_ok` :1669, `run_register_inductive_hit_ok` :1692,
`run_register_inductive_hit_mk` :1722, `run_register_inductive_cold_ok` :1738,
`run_register_inductive_runConcl` :1965, `run_register_inductive_gdeclsConst` :1992,
`run_get_constant_kername_ok` :2117.

**Declaration exits (12):** `run_mkDef_ok` :2023, `run_mkDef_rarg` :2069,
`run_modify_forIn_ok` :2084, `run_inline_tail_ok` :2201, `run_inline_prefix_ok` :2248,
`run_nonrec_exit_ok` :2283, `run_rec_exit_ok` :2343, `run_visitMutual_ok` :2422,
`run_inline_tail_ok'` :2526, `run_inline_prefix_ok'` :2574, `run_nonrec_exit_ok'` :2604,
`run_rec_exit_ok'` :2660, `run_inline_prefix_decomp'` :2756.

**Block/freshness (3):** `run_mkFreshFVarId_list` :2890, `run_rec_exit_siblings_le` :672,
`run_rec_exit_siblings_chained` :2949.

**Binder and output constructors (12):** `run_withLocalDecl_ok` :3031,
`run_withLocalDef_ok` :3045, `run_lambdaMonocular_ok` :3062, `run_letMonocular_ok` :3077,
`run_forallMonocular_ok` :3092, `run_lambdaMonocularOrIntro_ok` :3107,
`run_lambdaOrIntroToArity_ok` :3124, `run_fvar_to_name_ok` :3144, `run_mkLambda_ok` :3154,
`run_mkLetIn_ok` :3169, `run_mkAlt_ok` :3184.

The last three are the ones that pin the **output shape** and therefore feed Q1
("does `LBCompile` reproduce `visitExpr` exactly?"):

```lean
theorem run_mkLambda_ok … : s' = s ∧ w' = w ∧ ∃ nm, t = .lambda nm (toBvar x 0 body)    -- :3154
theorem run_mkLetIn_ok … : s' = s ∧ w' = w ∧ ∃ nm, t = .letIn nm val (toBvar x 0 body)  -- :3169
theorem run_mkAlt_ok … : s' = s ∧ w' = w ∧ r.1.length = xs.length ∧
    r.2 = xs.reverse.zipIdx.foldl (fun b p => toBvar p.1 p.2 b) body                    -- :3184
```

`run_mkAlt_ok` is the exact binder order Q1 asks about, already proved. **Q1 is decidable
from this lemma plus `run_mkDef_ok`/`run_mkDef_rarg` without new proof work.**

### 10.3 Admissibility and `⊑` machinery — RE-ANCHORED, survives verbatim

```lean
theorem est_admissible_ok {ε σ α} [Nonempty ε] (Q : Void σ → α → Void σ → Prop) :       -- :289
    admissible (α := EST ε σ α) (fun x => ∀ w a w', x w = .ok a w' → Q w a w')
theorem est_admissible_ok_pair …                                                       -- :311
theorem eraseM_admissible_ok  (Q : … ) : admissible (α := EraseM τ) …                  -- :334
theorem eraseM_admissible_ok₁ (Q : γ₁ → … ) : admissible (α := γ₁ → EraseM τ) …        -- :362
theorem eraseM_admissible_ok₂ …  -- :377
theorem eraseM_admissible_ok₃ …  -- :393
theorem eraseM_admissible_ok₄ …  -- :410
theorem eraseM_admissible_ok₅ …  -- :427

theorem approx_rfl {α : Sort u} [PartialOrder α] {x : α} : x ⊑ x                        -- :485
theorem run_ok_of_le {τ} {x y : EraseM τ} (h : x ⊑ y) (hx : x s ctx cctx ref w = .ok (r,s') w') :
    y s ctx cctx ref w = .ok (r, s') w'                                                 -- :492
theorem run_ok_of_le₁ {γ τ} {f g : γ → EraseM τ} (h : f ⊑ g) …                          -- :508
theorem admissible_and_le {α} [CCPO α] (P : α → Prop) (c : α) (hP : admissible P) :     -- :519
    admissible (fun x => P x ∧ x ⊑ c)
theorem fix_step_le {α} [CCPO α] {F : α → α} (hF : monotone F) {x : α}                  -- :525
    (h : x ⊑ fix F hF) : F x ⊑ fix F hF
```

**The induction principle used** is `partial_fixpoint`'s own, reached through:

* eighteen `*_eq_mutual : visitXxx = visitExpr.mutual.2.…` `rfl` lemmas (:536-587), each
  under an `unseal`;
* `theorem mutual_le_of {f₁ … f₁₈} (h₁ : f₁ ⊑ visitExpr) … (h₁₈ : f₁₈ ⊑ visitAlt) :`
  `(⟨f₁,…,f₁₈⟩ : (Expr → EraseM LBTerm) ×' _) ⊑ Erasure.visitExpr.mutual` (:597), which
  packs the eighteen `⊑` conjuncts into the `PProd` that
  `Erasure.visitExpr.mutual._proof_1 : Lean.Order.monotone …` (generated by
  `partial_fixpoint`) is stated over;
* `rec_exit_siblings_mono` (:648) and `run_rec_exit_siblings_le` (:672) — the sibling
  `mapM`'s monotonicity, needed because `visitMutual` recurses through a `mapM`.

**All of this is relation-independent** — none of it mentions `Erases`, `ErasureCtx` or
lean4lean. It transfers to T8 with zero edits. The eighteen slots' *types* change only if
the shipping mutual block changes, which the rework forbids.

---

## 11. `VisitExprRefines.lean` — RE-ANCHORED, 4,641 lines

### 11.1 `BridgeInv` — `VisitExprRefines.lean:889`, ten fields

```lean
structure BridgeInv (env : VEnv) (Us : List Name) (known : Name → Prop)
    (Γ : ErasureCtx) (cfg₀ : ErasureConfig) (gen : NameGenerator)
    (ctx : Erasure.ErasureContext) (s : Erasure.ErasureState) (Δ : VLCtx) : Prop where
  mlc      : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  lparams  : ctx.lparams <+: Us
  cfg      : ctx.config = cfg₀
  natcfg   : Γ.natPeano = true → ctx.config.nat = .peano
  kfresh   : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  fixvars  : ∀ (nm : Name) (x : FVarId),
               ctx.fixvars.bind (fun m => m[nm]?) = some x ↔ Γ.fixvars nm = some x
  fixfresh : ∀ (nm : Name) (x : FVarId), Γ.fixvars nm = some x → gen.Reserves x ∧ x ∉ Δ.fvars
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  knames   : ∀ n : Name, Γ.constants n = toKername n
  consts   : ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = Γ.constants n
```

plus `BridgeInv.trlctx` (:972, re-derives `TrLCtx env Us ctx.lctx Δ` from `mlc`) and the
transport lemmas `mono`, `mono_state` (:1001, :1031), `withFixvars` (:1067),
`of_coh` / `mkLocalDecl` / `mkLetDecl`.

**Field survival under the rework:**

| field | survives? | why |
|---|---|---|
| `mlc` | **yes** | this is `PrimSpec.env_connect`'s local half; nothing replaces it |
| `lparams` | **yes** | N9 keeps polymorphic *dependencies*; the prefix discipline is exactly what that needs |
| `cfg` | **yes** | T8's `hcfg` is stated on `cfg₀`; this field cashes it against the run |
| `natcfg` | **delete** | N3 pins `cfg.nat = .peano`; the `Γ.natPeano` flag is a second copy of the same fact |
| `kfresh` | **yes** | `PrimSpec.fresh_names` |
| `fixvars`, `fixfresh` | **delete** | keyed on `Erases.fixvar`, which §4.3 deletes; `fixIntro` (T6) sees no fvars |
| `reserved` | **yes** | freshness discipline |
| `knames`, `consts` | **yes** but move | these are the `Γ`↔state agreement; with `ErasureCtx` deleted they become facts about `toKername` and `ErasesEnv`, i.e. `∀ n k, s.constants.get? n = some k → k = toKername n` = `CanonicalConstants` (which already exists at `ErasureRun.lean:1482`) |

Net: **7 of 10 fields survive**, two collapse into the existing `CanonicalConstants`, and
`natcfg`/`fixvars`/`fixfresh` die with the rules they served.

### 11.2 The eighteen motives — `visitExpr_refines_erases_core`, `VisitExprRefines.lean:1901`

Hypotheses (all seven bundles die under §4.3, replaced by one `PrimSpec`):

```lean
theorem visitExpr_refines_erases_core {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ₀ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H  : BridgeHyps env Us Γ₀ gw) (HD : DataBridgeHyps Γ₀ gw)
    (C  : CasesBridgeHyps Γ₀ gw)   (P  : ProjBridgeHyps Γ₀ gw)
    (Hδ : ∀ cctx ref, DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    (Hβ : ∀ cctx ref, BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (Hreg : RecBlockAgreement env Us known Γ₀ cfg₀)
    (henv : env.Ordered) : <18-fold conjunction>
```

Every conjunct has the uniform shape

```
(∀ <args> s ctx cctx ref w <res> s' w', visitXxx <args> s ctx cctx ref w = .ok (<res>, s') w' →
   ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars),
   ∀ Δ <extra>, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ → <side conditions> →
     <conclusion> ∧ RunConclδ env Us Γ₀ Esrc s s' ∧ gw w ≤ gw w')
∧ Erasure.visitXxx ⊑ Erasure.visitXxx
```

| # | function | extra binders | side conditions beyond `BridgeInv` | conclusion |
|---|---|---|---|---|
| 1 | `visitExpr e` | — | `Supported known Γ e`, `∃ ve, TrExprS env Us Δ e ve` | `Erases env Us Γ Δ e t` |
| 2 | `visitLiteral l` | `n iid` | `l = .natVal n`, `Γ.natPeano = true`, `Γ.ctors ``Nat.zero = some (iid,0)`, `… Nat.succ = some (iid,1)`, `∃ ve, TrExprS … (.lit l) ve` | `Erases env Us Γ Δ (.lit l) r` |
| 3 | `visitConstructor cn args` | `us iid cidx` | `Γ.ctors cn = some (iid,cidx)`, `ctx.config.nat = .peano ∨ (cn ≠ Nat.zero ∧ cn ≠ Nat.succ)`, per-arg `Supported`+`TrExprS` | `Erases … (args.foldl Expr.app (.const cn us)) t` |
| 4 | `visitConst e` | `n us` | `e = .const n us`, `known n ∨ Γ.fixvars n ≠ none`, `Γ.ctors n = none`, `Γ.casesOns n = none` | `Erases env Us Γ Δ e t` |
| 5 | `get_constant_kername n` | — | `known n` | `kn = Γ.constants n` |
| 6 | `visitMutual n` | — | `known n` | *(registration only)* `(s'.constants.get? n).isSome` |
| 7 | `visitAppArgs f' args` | `hd` | `Erases env Us Γ Δ hd f'`, per-arg `Supported`+`TrExprS` | `Erases … (args.foldl Expr.app hd) t` |
| 8 | `visitLet e` | `n ty v b nd` | `e = .letE n ty v b nd`, `Supported`, `TrExprS` | `Erases env Us Γ Δ e t` |
| 9 | `visitLambda e` | `n ty b bi` | `e = .lam n ty b bi`, `Supported`, `TrExprS` | `Erases env Us Γ Δ e t` |
| 10 | `visitProj tn i e` | `iid np nf` | `Γ.projs tn = some (iid,np)`, `Γ.ctorFields iid = some [nf]`, `i < nf`, `Supported`, `TrExprS` | `Erases … (.proj tn i e) r` |
| 11 | `visitApp e` | — | `Supported`, `TrExprS` | `Erases env Us Γ Δ e t` |
| 12 | `visitConstApp e` | `cn us` | `Supported`, `TrExprS`, `e.getAppFn = .const cn us` | `Erases env Us Γ Δ e t` |
| 13 | `visitCtorEta cn ar e` | `us iid cidx` | `e.getAppFn = .const cn us`, `Γ.ctors cn = some (iid,cidx)`, `Γ.ctorArities cn = some ar`, `ar ≤ e.getAppArgs.size`, `cn ≠ Nat.zero`, `cn ≠ Nat.succ`, per-arg facts | `Erases env Us Γ Δ e t` |
| 14 | `visitCtorEtaGo cn ar ty fe args` | `us iid cidx` | as 13 with `ar ≤ args.size` | `Erases … (args.foldl Expr.app (.const cn us)) t` |
| 15 | `visitCasesEta ci e` | `con us iid np dp nfs` | `e.getAppFn = .const con us`, `Γ.casesOns con = some (iid,np)`, `Γ.casesDiscrPos con = some dp`, `Γ.ctorFields iid = some nfs`, `CasesInfoAgrees ci con dp nfs`, `con.getPrefix ≠ ``Nat`, `≠ ``Int`, `dp+1+nfs.length ≤ e.getAppArgs.size`, `CasesSpineFacts …` | `Erases env Us Γ Δ e t` |
| 16 | `visitCasesEtaGo ci ty fe args` | as 15 | as 15 on `args` | `Erases … (args.foldl Expr.app (.const con us)) t` |
| 17 | `visitCases ci args` | as 15 | as 15 on `args` | `Erases … (args.foldl Expr.app (.const con us)) t` |
| 18 | `visitAlt nf mask e` | — | `mask = Array.replicate nf .keep`, `IsLamTelescope nf e`, `Supported`, `TrExprS` | *(alt shape)* |

**Exported form**, `VisitExprRefines.lean:3645`:

```lean
theorem visitExpr_refines_erases {env Us known Γ cfg₀ Esrc gw}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (P : ProjBridgeHyps Γ gw)
    (Hδ : ∀ cctx ref, DeltaHyps env Us known Γ cfg₀ Esrc gw cctx ref)
    (Hβ : ∀ cctx ref, BlockHyps env Us known Γ cfg₀ Esrc cctx ref)
    (Hreg : RecBlockAgreement env Us known Γ cfg₀) (henv : env.Ordered) :
    ∀ e s ctx cctx ref w t s' w',
      Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ∀ Δ, BridgeInv env Us known Γ cfg₀ (gw w) ctx s Δ →
        Supported known Γ e → (∃ ve, TrExprS env Us Δ e ve) →
        Erases env Us Γ Δ e t ∧ RunConclδ env Us Γ Esrc s s' ∧ gw w ≤ gw w'
```

The proof is `(…core….1.1) e s ctx cctx ref w t s' w' hrun Γ (ErasureCtx.withFixvars_self Γ).symm Δ`.

### 11.3 What restating the eighteen motives costs

* Motives **1, 7, 8, 9, 11, 12, 18** conclude `Erases … e t` on nodes that survive T2
  (app/lam/letE/bvar/fvar/const). Their conclusions change only by replacing
  `Erases env Us Γ Δ` with `Erases env Us Δ` and dropping `RunConclδ` for `RunConcl` +
  T3's `ErasesEnv` obligation. **Restatement is mechanical.**
* Motives **2 (lit), 10 (proj)** survive with their side conditions moving from `Γ` to the
  environment relation.
* Motives **3, 13, 14 (constructor path)** conclude `Erases … (.const cn us) applied` and
  must be restated as `∃ t₀, Erases … t₀ ∧ t = ctorInline.term Σ t₀`.
* Motives **15, 16, 17 (casesOn path)** likewise against `elimInline`.
* Motives **4, 5, 6 (const / kername / visitMutual)** are where `ErasesEnv` replaces
  `RunConclδ` outright; motive 6 has no `Erases` conjunct at all today and is pure
  registration, so it **survives verbatim** modulo the record's name.

Realistic split confirmed against the file: 7 motives mechanical, 3 environment-facing,
8 pass-facing.

### 11.4 The `Supported` fragment predicate — `Bridge.lean:100`

```lean
inductive Supported (known : Name → Prop) (Γ : ErasureCtx) : Expr → Prop
  | bvar | fvar | const (hk : known n ∨ Γ.fixvars n ≠ none) | app | lam | letE
  | natLit | proj | ctorApp | casesApp
```

Ten constructors at `:101,102,109,112,114,116,137,162,174,204`. `Supported.casesApp`
(:204) is where the sparse-`casesOn` hole must become visible (acceptance criterion 11);
today its docstring's sparse sentence is the review's DOC finding. `IsLamTelescope`
(:60) is the alt-shape predicate motive 18 uses.

---

## 12. `ColdStart{Run,Shape,Induction}` — RE-ANCHORED

### 12.1 `ColdStartRun.lean` — the run decomposition

```lean
theorem run_eq (x : EraseM α) (cfg : ErasureConfig) :                            -- :644
    Erasure.run x cfg cctx ref w = x {} { «config» := cfg } cctx ref w := rfl

theorem erase_run_ok {e : Expr} {cfg : ErasureConfig} {p : Program}              -- :651
    {inls : List Kername} {w' : Void IO.RealWorld}
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (pe : Expr) (t : LBTerm) (sp sf : ErasureState) (wp wt : Void IO.RealWorld),
      prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp ∧
      visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt ∧
      p = .untyped sf.gdecls (some t) ∧ inls = sf.inlinings

theorem run_prepare_erasure_ok {e s ctx w pe s₁ w₁}                              -- :169
    (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) :
    s₁ = s ∧ ∃ (e₁ e₂ e₃ : Expr) (v₁ v₂ v₃ : Void IO.RealWorld),
      (liftM (replaceUnsafeRecNames e) : EraseM Expr) s ctx cctx ref w = .ok (e₁, s) v₁ ∧
      (liftM (Compiler.LCNF.macroInline e₁) : EraseM Expr) s ctx cctx ref v₁ = .ok (e₂, s) v₂ ∧
      (liftM (Compiler.LCNF.inlineMatchers e₂) : EraseM Expr) s ctx cctx ref v₂ = .ok (e₃, s) v₃ ∧
      (liftM (Compiler.LCNF.macroInline e₃) : EraseM Expr) s ctx cctx ref v₃ = .ok (pe, s) w₁

theorem run_prepare_erasure_state {e s ctx w pe s₁ w₁}                           -- :578
    (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) : s₁ = s

theorem prepare_sound_of_prepareHyps {Γ Esrc} (HP : PrepareHyps Γ Esrc)          -- :589
    (hcs : ctx.config.csimp = false) (hrun : …) :
    ∀ {v : Expr}, SEvalData Γ Esrc pe v ↔ SEvalData Γ Esrc e v
```

`erase_run_ok` is **exactly T9's decomposition** and carries unchanged: the subject is
`Erasure.erase`, `Σ = sf.gdecls` and `t` are produced by the run, and `inls = sf.inlinings`
is the N11 output. `run_prepare_erasure_ok` enumerates the four `prepare_erasure` stages
that spec §3.4 names, under exactly the N1 hypothesis `cfg.csimp = false`.

`prepare_sound_of_prepareHyps` is the `e ↔ pe` link the review's GA-06 says is unclosed —
it is stated at `SEvalData`, one of the seven relations §4.3 deletes. **Its statement must
be re-aimed at T4's single `SEval`; the proof (an `Iff` transported through four δ steps)
is relation-generic.**

### 12.2 `ColdStartInduction.lean` — the unconditional shape induction

```lean
structure RunClosed (Q : ErasureState → Prop) : Prop where                       -- :156
  inl, ax, reg, prep, nrc, rc                                                     -- six closure clauses
def ShapeC (Q : ErasureState → Prop) (s s' : ErasureState) (t : LBTerm) : Prop    -- :199
theorem visitExpr_shape {Q} (H : RunClosed Q) : <18-fold conjunction>             -- :280
theorem runClosed_true : RunClosed (fun _ => True)                                -- :1091

theorem visitExpr_shape_all {e s ctx cctx ref w t s' w'}                          -- :1104
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    NoFix t ∧ LBClosed t 0 ∧ NoBlock t

theorem visitExpr_noFix_closed … : NoFix t ∧ LBClosed t 0                         -- :1115
theorem visitExpr_noBlock     … : NoBlock t                                       -- :1125
theorem visitExpr_output_shape {Q} (H : RunClosed Q) …                            -- :1133
```

`visitExpr_shape_all` has **no hypotheses at all** — not on the state, not on the source
expression, not on the configuration, and it is panic-tolerant. It is the single most
reusable result in the ColdStart family and it directly supplies two conjuncts of T9's
`LBWfPeregrine`: `NoBlock t` **is** applied-constructor form (spec §3.1's primary target),
and `LBClosed t 0` is closedness. `NoFix t` says the *term* has no `.fix` node — which is
consistent with T2.4 (no `Erases` rule produces `.fix`) and is evidence that the
`fixIntro` pass acts on **declaration bodies**, not on the subject term.

Also here: `RegBridgeHyps` (:1195), `RunClosed.regInvShape` (:1295),
`visitExpr_regInvShape` (:1317), `visitMutual_regInvShape` (:1327),
`get_constant_kername_regInvShape` (:1337), `runClosed_keysDistinct_refuted` (:1363),
`gRegBridgeHyps` (:1394), `gVisitExpr_regInvShape` (:1416), `RegShapeHyps` (:1454),
and the block helpers `rec_block_closed` (:207), `rec_block_noBlock` (:222),
`rec_bodies_closed` (:237), `rec_bodies_noBlock` (:245),
`visitCases_match_tri` (:94), `visitConstructor_match_quad` (:127).

### 12.3 `ColdStartShape.lean` — `RegInvShape`, `ColdStartShape.lean:314`

```lean
structure RegInvShape (Γ : ErasureCtx) (s : ErasureState) : Prop where
  kn         : ∀ {n : Name} {k : Kername}, s.constants.get? n = some k → k = Γ.constants n
  cover      : ConstKeysCovered s
  ctors      : RegisteredCtorsOn Γ s.gdecls (BlockRegistered s.gdecls)
  cases      : RegisteredCasesOn Γ s.gdecls (BlockRegistered s.gdecls)
  fields     : RegisteredCtorFieldsOn Γ s.gdecls (BlockRegistered s.gdecls)
  projs      : RegisteredProjsOn Γ s.gdecls (BlockRegistered s.gdecls)
  projfields : RegisteredProjCtorFieldsOn Γ s.gdecls (BlockRegistered s.gdecls)
  nofix      : NoFixEnvD s.gdecls
  closed     : ClosedEnv s.gdecls
```

Accompanying API: `.empty` (:340 — every field vacuous at `Erasure.run`'s initial state),
`.registeredCtors` (:354), `.registeredCases` (:360), `.registeredCtorFieldsAll` (:366),
`.registeredProjs`, `.registeredProjCtorFields`, `.closedEnv`, `.noFixEnv`,
`.addAxiom` (:474), `.constExt`, `.registerInd`, `.addAxiom_run`,
`.register_inductive_run` — 63 declarations in the file.

**Under the rework `RegInvShape` becomes T3's `ErasesEnv` derived-from-the-run half.** The
five `Registered*On` fields are the five `Γ`-keyed registration records §4.3 collapses into
one `ErasesEnv`; `closed`/`nofix` become `LBWfPeregrine` conjuncts; `kn` becomes
`CanonicalConstants`; `cover` (`ConstKeysCovered`) survives as the key discipline any
environment relation needs. The `.empty` lemma is the cold-start base case and carries
verbatim — it is the technique the spec calls "the current tree's durable contribution".

---

## 13. `SubjectReduction{,Full,Iota}` — RE-ANCHORED; three `*_defeq`, one survives

```lean
theorem SEvalβ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}    -- SubjectReduction.lean:52
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv} {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve) (hev : SEvalβ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve

theorem SEvalβζδ_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}  -- SubjectReductionFull.lean:389
    (hΔ : VLCtx.WF env Us.length Δ) {Esrc : SEnv}
    (hcon : SEnvConsistent env Us Esrc) {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve) (hev : SEvalβζδ Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve

theorem SEvalDataι_defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx} -- SubjectReductionIota.lean:146
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {ia : IotaArities} {Esrc : SEnv}
    (hcon : SEnvConsistentL env Us Γ.lparams Esrc) (hiota : IotaConsistent env Us Γ ia)
    (hproj : ProjConsistent env Us Γ) {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve) (hev : SEvalDataι Γ ia Esrc e v) :
    ∃ vve, TrExprS env Us Δ v vve ∧ env.IsDefEqU Us.length Δ.toCtx ve vve
```

Auxiliary: `SEvalβζδ_defeq_spine` (SubjectReductionFull.lean:309) — the spine-congruence
schema, parameterised by an abstract `P : Expr → Expr → Prop` with the defeq-transport
property. **This is the piece that makes one relation's proof reusable for another and is
precisely how T4's single flag-parameterised `SEval.defeq` should be organised.**

`SEvalDataι_defeq_of_shape` (SubjectReductionIota.lean:256) takes nine hypotheses
(`PatsIotaSpec`, `SEnvConsistent`, `Γ.lparams = fun _ => []`, `IotaShape`, `ProjDefeqSpec`,
`ProjCtorAgree`, `ProjStructFacts`, `ProjFieldsCoherent`) — the chain §4.3 deletes;
`IotaShape` is one of the two uninhabited predicates (review TA-06).

**Reuse verdict.** The conclusion shape
`∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv` **is verbatim the
spec's `SEval.defeq`**. Of the three proofs, the β/ζ/δ arms are the same three arms written
three times (review R4: two copies byte-identical at `SubjectReductionFull.lean:398-430` =
`SubjectReductionIota.lean:157-189`); the ι and proj arms are the extra content in the
third. Writing T4's single proof means: take `SEvalβζδ_defeq`'s arms, add
`SEvalDataι_defeq`'s ι/proj arms, drop the `IotaShape`/`Proj*` premise chain in favour of
T3's `ErasesDecl.recr`/`ElimBody`. Estimated survival ~1,050 of 1,414 lines.

---

## 14. `Erases` transport metatheory — RE-ANCHORED

`Erases` today (`Erases.lean:415`) has **fifteen** rules:

| line | rule | fate |
|---|---|---|
| 419 | `box` | survives (T2) |
| 443 | `lit` | survives |
| 482 | `proj` | survives |
| 489 | `bvar` | survives |
| 491 | `fvar` | survives |
| 493 | `const` | survives, loses its registry premises |
| 497 | `app` | survives |
| 500 | `lam` | survives |
| 504 | `letE` | survives |
| 516 | `ctor` | **delete** → T3 `ErasesDecl.ctor` + T6 `ctorInline` |
| 530 | `ctor_head` | **delete** |
| 562 | `cases` | **delete** → T3 `ErasesDecl.recr` + T6 `elimInline` |
| 612 | `fixvar` | **delete** |
| 630 | `const_fix` | **delete** |
| 689 | `fix` | **delete** → T6 `fixIntro` |

Spec's tenth rule, `mdata`, is **new**.

Transport theorems (the assets that carry):

```lean
theorem erases_shift {env} (henv : env.Ordered) {Us Γ Δ Δ' dn dk n k}             -- Erases.lean:718
    (W : VLCtx.BVLift Δ Δ' dn dk n k) {e t} (h : Erases env Us Γ Δ e t) :
    Erases env Us Γ Δ' (e.liftLooseBVars' dk dn) (LBTerm.shift dn dk t)

theorem instN_toBVLift {Δ₀ Δ₁ Δ e₀' A₀ dk k}                                      -- Erases.lean:783
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0

theorem erases_subst {env} (henv : env.Ordered) {Us Γ Δ₀ e₀ e₀' A₀ s'}             -- Erases.lean:795
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀') (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (h₀ : Erases env Us Γ Δ₀ e₀ s') {Δ₁ Δ dk k} (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e t} (h : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t)

theorem Erases.abstract {env Us Γ Δ₀ v₀ d₀ dk k Δ₁ Δ}                             -- ErasesAbstract.lean:122
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) {e t} (hc : Closed e dk)
    (H : Erases env Us Γ Δ₁ e t) : Erases env Us Γ Δ (e.abstract1 v₀ dk) (toBvar v₀ dk t)

theorem Erases.uninstantiateN {env Us Γ Δ₀ v₀ d₀ dk k Δ₁ Δ}                       -- ErasesAbstract.lean:214
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) {e t}
    (H : Erases env Us Γ Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) t)
    (sc : FVarsIn (· ≠ v₀) e) (hc : Closed e (dk + 1)) : Erases env Us Γ Δ e (toBvar v₀ dk t)
-- + Erases.uninstantiate (the k = 0 corollary)
```

`ErasesStrengthen.lean` (747 lines): `ThinVLet`, `TrExprS.thin_vlet`, `Erases.thin_vlet`,
`Erases.strengthen_vlet`, `VLCtx.FVWF.fvars_nodup`, `TrExprS.weakFV'_fvwf`,
`TrExprS.weakFV_fvwf`, `erases_weakFV`, `TrExprS.weakFV'_nofvars`,
`TrExprS.weakFV_nofvars`, `erases_weakFV_nofvars`, `erases_weak_any`.

`ErasesUniform.lean` (820 lines): `ErasableStrengthen` (a commissioned premise),
`erasableStrengthen_liftN_zero`, `NoProj` + `NoProj.toIsUnique`/`.natLitToConstructor`/
`.strLitToConstructor`/`.toConstructor`, `NoProjBinders` + transports,
`Erases.strengthen_fvlift`, `Erases.strengthen_fvlift_binders`, `erases_strengthen_closed`,
`erases_uniform_closed`, `erases_uniform_of_nil`.

Each of these is a per-rule induction over `Erases`. **Nine of fifteen arms survive; the
six deleted rules take their arms with them.** No transport theorem's *statement* changes
except by dropping the `Γ : ErasureCtx` index (T2.1). Several `TrExprS.*` lemmas here
(`thin_vlet`, `weakFV'_fvwf`, `weakFV_nofvars`) are **kernel-generic** and criterion 21
sends them upstream.

Note: `Erases.lean` also carries ~30 fixture/witness declarations (`envNatLit`, `ΓnatLit`,
`natLitTower`, `erases_natLit`, `projInd`, `Γproj`, `erases_proj_fvar`, `erases_proj_ctor`,
`envNatT*`, `vNatTower`, `trExprS_natLit`, `fixRecDefs`, `ΓfixRec`, `erases_fixRec`,
`fixMutDefs`, `ΓfixMut`, `erases_fixMut_f/g`, `ΓfixOpen`, `erases_fixvar_fixOpen`). The
`fixRec`/`fixMut`/`fixOpen` families witness the deleted rules and go with them; the
`natLit` and `proj` families are the non-vacuity guards T2 still wants.

---

## 15. `EnvErasure{,Nonrec,Rec}` — RE-ANCHORED as T3 `ErasesEnv`

1,640 lines.

`EnvErasureNonrec.lean`: `RegisteredCtor`, `RegisteredCtors`, `ErasesEnvCtor`,
`ErasesEnvCases`, `RegisteredCases`, `RegisteredCtorFields`, `RegisteredCtorFieldsAll`,
`ErasesEnvProjs`, `RegisteredProjs`, `RegisteredProjCtorFields`;
`erasesEnvCtor_of_registeredCtors`, `erasesEnvCases_of_registeredCases`,
`ErasesEnvCases.nonProp`, `ctorFieldsCoherent_of_registered`,
`erasesEnvProjs_of_registeredProjs`, `ErasesEnvProjs.nonProp`,
`projFieldsCoherent_of_registered`, `erases_nonrec_const_body`;
`structure RegisteredClosure` + `erasesEnvDelta_of_registeredClosure`;
`structure RegisteredClosureData` + `erasesEnvDeltaData_of_registeredClosureData`;
plus fifteen `g*` non-vacuity fixtures (`gΓctor_*`, `gΓcases_*`, `Γproj_*`, `gΓι_*`,
`gRegisteredClosure`, `gErasesEnvDelta`, `gBridgeInv_nil`).

`EnvErasureRec.lean`: `structure RegisteredClosureRec`,
`erasesEnvDelta_of_registeredClosureRec`, `gErases_fix`, `gErasesOpenR`, `gInstFixvarsR`,
`gErases_fix_of_open`, `gRegisteredClosureRec`, `gErasesEnvDeltaRec`,
`no_wcbvEval_app_gCxFix`, `gCxSEval`, `gCxTrExprS`, `ContentlessFix`, `gCxErasesHead`,
`gCxErases`, `gCxNoBlock`, `gCxNoFixEnv`,
`erases_correct_data_without_noFix_false_of_contentless_fix`, `not_contentlessFix`,
`registeredClosure_of_registeredClosureRec`, `erasesEnvDelta_of_registeredClosureRec'`,
`recEnvConsistent_of_registeredClosureRec`, `erases_correct_data_recursive_fires`,
`erases_correct_data_recursive_value`.

`EnvErasure.lean` (183 lines) is a thin re-export plus
`shipping_erase_correct_firstorder_registered`.

**Reuse verdict.** The *derivation direction* — "what the run registered ⟹ the environment
relation holds" — is what T3 keeps and the spec explicitly calls better than the paper's
presentation. Five `Registered*` predicates and three `RegisteredClosure*` structures
collapse into one `ErasesEnv`; the `_of_registered*` implications become the constructors
of that relation's derivation from `RegInvShape`. The `EnvErasureRec` half is entirely
keyed on `Erases.fix`/`const_fix`/`fixvar` and does not survive as proof, **except**
`ContentlessFix` / `not_contentlessFix` / `no_wcbvEval_app_gCxFix`, which are the
counterexample apparatus showing why a fix-carrying environment needs a side condition —
that content re-aims onto T6 `fixIntro`'s non-vacuity guard.

---

## 16. The shipping edits: `dev/verify` vs `dev/bump-4.33`

`git diff --stat dev/bump-4.33 dev/verify -- LeanToLambdaBox/{Erasure,Basic,Printing}.lean`:

```
 LeanToLambdaBox/Basic.lean   |  32 +++-
 LeanToLambdaBox/Erasure.lean | 418 +++++++++++++++++++++++++++++++++++++------
 2 files changed, 387 insertions(+), 63 deletions(-)
```

`Printing.lean` is **unchanged**. `dev/bump-4.33` HEAD is `7e3747a` ("bump: Lean v4.29.0 →
v4.33.0-rc2") and is the merge-base, so the diff is exactly the verification branch's own
delta.

### 16.1 PROOF-ONLY (the §4.1 "shipping-side edits enabling induction" asset)

| # | edit | location | evidence it is proof-only |
|---|---|---|---|
| P1 | `partial def erase … where visitExpr …` → `mutual` block of 18 `partial_fixpoint` defs; `erase` extracted as a plain `def` after `end` | `Erasure.lean:576-931` | same bodies, textually; `partial_fixpoint` changes the *definitional* mechanism, giving `.eq_def` and `.mutual_fixpoint_induct`; the compiled function is the same fixpoint |
| P2 | nine `@[partial_fixpoint_monotone]` lemmas: `withReader_mono`, `withLocalDecl_mono`, `withLocalDef_mono`, `lambdaMonocular_mono`, `letMonocular_mono`, `forallMonocular_mono`, `lambdaMonocularOrIntro_mono`, `lambdaOrIntroToArity_mono`, `expr_withApp_mono` | `Erasure.lean:364-500` | theorems only; they exist to let `partial_fixpoint` discharge its monotonicity side conditions |
| P3 | `theorem expr_withApp_eq` (`e.withApp k = k e.getAppFn e.getAppArgs`), re-proved locally so the shipping build need not import lean4lean's `Verify` layer | `Erasure.lean:477` | a theorem |
| P4 | `visitCasesEta`/`visitCasesEtaGo`/`visitCtorEta`/`visitCtorEtaGo` — specializations of `withAppEtaToMinArity` with a `visitCases`/`visitConstructor` continuation | `Erasure.lean:690-730` | forced by `partial_fixpoint`'s no-nested-recursion rule; the code is `withAppEtaToMinArity`'s body inlined with the continuation fixed. Review shipping-integrity lens confirms the shape reproduces `inferType`-then-`withApp`-then-`go` exactly. `withAppEtaToMinArity` itself is now **dead shipping code** (review SI-11) |
| P5 | `for arg in (args[casesInfo.arity:]).toArray` (was: over the `Subarray`) | `Erasure.lean:832` | same elements in the same order; the change exists because v4.29's `Subarray` `ForIn` has no derivable monotonicity lemma without `LawfulMonad EST` |
| P6 | `Basic.lean`: `partial def toBvar` → `mutual def toBvar / toBvarArgs / toBvarAlts / toBvarDefs` | `Basic.lean:105-140` | line-for-line transcription of the three `.map`s, including the `lvl + names.length` and hoisted `lvl + defs.length` offsets. `Abstract.lean`'s `toBvarArgs_eq_map`/`toBvarAlts_eq_map`/`toBvarDefs_eq_map` **prove** the equivalence with the old `.map` bodies |
| P7 | `import LeanToLambdaBox.Relevance` added to `Erasure.lean` | `Erasure.lean:5` | build-graph only — **but** it makes the shipping module depend on lean4lean, which is a packaging change worth stating in the ledger |

### 16.2 BEHAVIOUR-AFFECTING

| # | edit | location | effect |
|---|---|---|---|
| B1 | **`isErasable` kernel reroute.** `def isErasable (e : Expr) : MetaM Bool` (Meta-only) split into `isErasableMeta` (the old body) + a new `def isErasable (lparams : List Name) (e : Expr) : MetaM Bool` that runs `Lean4Lean.TypeChecker.M.run … (RecM.run (LeanToLambdaBox.isErasable e))` and falls back to `isErasableMeta` on `.error` | `Erasure.lean:151-187` | **changes relevance verdicts.** Its own comment says so ("relevance decisions can differ … edge cases; extracted output should be re-validated"). Review SI-1 measured an under-erasure on the *success* path (`kernel=false, meta=true`) for a definition whose declared type aliases a ∀-telescope, because the `approxDepth`-derived fuel bounds the *unreduced* type. Review SI-4: >13× per-call cost (fresh `TypeChecker.State` + `toKernelEnv` per node). Review SI-5: the fallback is silent and uninstrumented. **Spec §4.1 explicitly excludes this edit from the carried asset.** |
| B2 | **`ErasureContext.lparams : List Name := []`** added, and installed by `visitMutual`'s two `withReader`s (`lparams := ci.levelParams`) on both the recursive and non-recursive exits | `Erasure.lean:121-130`, `:887`, `:910` | only observable through B1 (it is the universe context the kernel checker runs in), but it is a genuine reader-state change, and `BridgeInv.lparams : ctx.lparams <+: Us` exists because of it |
| B3 | **`auto_inline_typeclass_dispatch : Bool := false`** config field + `LBTerm.stripLambdas`, `LBTerm.containsFix`, `LBTerm.isTrivialAlias` + the post-erasure marking block in `visitMutual` (`Lean.Meta.isInstance` ∨ trivial-alias ⇒ cons onto `s.inlinings`) | `Erasure.lean:69-133`, `:895-905` | changes the emitted `.ast.inlinings` list when enabled. Default `false`, so the default path is unchanged. **This is N5's `hinline : cfg.auto_inline_typeclass_dispatch = false`** — the flag the spec restricts already exists, which is convenient. Review SI-10: an unverified product feature that rode into the verification branch |
| B4 | **`@[inline]` marking restructured**: the attribute lookup is hoisted to `let leanInline := single_decl && match Compiler.getInlineAttribute? … `, so a name in a *multi*-declaration mutual block is no longer marked inline | `Erasure.lean:857-875` | changes the `inlinings` output for mutual blocks. Not covered by any current hypothesis |
| B5 | **`withLocalDef` drops `nd`** from the `mkLetDecl` call (`ctx.lctx.mkLetDecl fvarid n type val nd` → `… n type val`), parameter renamed `_nd` | `Erasure.lean:283-295` | the docstring claims byte-identical behaviour on the corpus and gives the reason (`MLCtx.vlet` uses the default `nonDep`); it is nevertheless a changed argument to a Lean core API, and there is no reproducible corpus diff in-repo (review SI-9: `*.ast` is gitignored, no diff script, CI builds `main` only). **Treat as behaviour-affecting-unless-measured.** |
| B6 | **`MLType` extended** (`string`, `option a`, `array a`, `prod a b`), `MLType.toString` made `partial` and re-parenthesised (`protArrow`/`protCtor` replacing `toStringProtected`), `to_ml_type` extended with `Int`, `String`, `Option`, `Array`, `Prod` | `Erasure.lean:934-980` | affects the `.mli` sidecar only, not the λ□ output. Falls under N11 (one ledger row) |

### 16.3 Consequences for the rework

* The §4.1 asset "~380 diff lines, condition: none" is accurate **for P1-P7 only**;
  P1-P7 measure ~330 of the 387 added lines. B1-B6 are the remaining ~55 plus the deletions.
* T8's subject is the `partial_fixpoint` family, i.e. P1-P5 are load-bearing preconditions
  and cannot be reverted.
* B1 is the edit T8's `PrimSpec.oracle_sound` is *about*. If B1 were reverted, field 4 would
  have to be assumed (class D) rather than discharged (class B), and acceptance criterion 9
  would be unsatisfiable. **The spec's choice to route `OracleDischarge` into the capstone
  is therefore a choice to keep B1** — with its measured under-erasure bug (SI-1) inside
  the fragment `Supported`/`PrimSpec` must exclude, and its 33-axiom cost (§7.5).
* B3/B5 are already the shape N5/N1-style hypotheses want; B4 and B6 have no hypothesis
  today and need either a ledger row (N11) or a `Supported`/`hcfg` conjunct.

---

## 17. Cross-cutting observations for the design

1. **Nothing in the CARRIED list is stated at the spec's `eraseFlags`.** `WcbvEval` and its
   metatheory are flag-polymorphic (free), `IotaBridge` and `FixUnfold` are
   flag-polymorphic or gated only on `with_guarded_fix` (free), but `Optimize` is pinned to
   block form and costs four new rule arms (§8.3). Defining `eraseFlags` and re-pointing
   `targetFlags` is the first concrete task.
2. **`PrimSpec` already exists under another name.** `ResidualHyps` (§7.4) has four fields
   in exactly the spec's shape; the missing piece is field 1's `abs_env_irr`, which today
   is the `(env₀, ves)` parameter pair plus `toBridgeHyps`'s `wf` argument.
3. **Q1 is answerable without new proof work** from `run_mkAlt_ok`, `run_mkLambda_ok`,
   `run_mkLetIn_ok`, `run_mkDef_ok`, `run_mkDef_rarg` (§10.2).
4. **`visitExpr_shape_all` already delivers two thirds of `LBWfPeregrine`** unconditionally
   and panic-tolerantly (§12.2).
5. **The trust ledger's row count is understated.** Routing the oracle in (criterion 9)
   brings 33 axioms, including two `_native.bv_decide` axioms from Lean core. Criterion 15's
   committed fixture must accommodate that, and criterion 16's "`sorryAx` roots at
   `file:line` in the pinned lean4lean" is only part of the story.
6. **Criterion 21 conflicts with `CheckerAdequacy.lean`**, which declares eight
   `Lean4Lean.TypeChecker`-namespace declarations in this repository (§7.3) and is on the
   critical path for criterion 9.
