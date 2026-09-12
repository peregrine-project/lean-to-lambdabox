import LeanToLambdaBox.ErasesCorrect.Iota

/-!
# First-order inductive types, and the erasure of their values

A first-order inductive type is monomorphic, index-free, informative, and has only
`.const`-headed constructor fields — the domain on which erasure stops being a relation and
becomes a function. Three declarations carry that:

* `FirstOrderInd env I`, whose closure parameter is **closed inside the definition** as an
  existentially quantified post-fixed point (`FOClosed`). A free closure parameter makes the
  predicate satisfiable by `fun _ => True`, which admits a `True`-fielded type former;
* `firstOrderIndB`, the fuelled Boolean checker on a reified `Witness.SourceTable`, decided
  by `rfl` on `Nat`, `Bool` and a two-constructor tree;
* `firstorder_erases_deterministic` and `firstorder_no_box`: at a value of a first-order
  type the erasure relation has exactly one image, and that image holds no box.

Both theorems run one induction, `firstorder_erases_core`, over the shape of a source value
(`SValue`, what an `SEval` derivation returns). Their box-freedom and their uniqueness come
from the same place: at each node of the value the box rule is excluded by
`not_erasable_of_informative` (`ErasesCorrect/Iota.lean`, stated once and used twice), and
what remains is the constructor congruence.

`mono` (monomorphic) and `noIndices` (index-free) are **declared scope restrictions**: they
reject types that are first-order and box-free, and they are booked to this development, not
to Letouzey's Def. 14 or to MetaRocq's `firstorder_ind`. `informative` is the result-sort
half of Def. 6, in the shape the tree's own `InformativeInd` uses.

Two facts this file cannot prove are named premises: `FOFields`, the source-theory typing of
a first-order constructor value, and `IndSpineNotProp`, which `not_erasable_of_informative`
already takes. `firstOrderIndB`'s soundness against `FirstOrderInd` is **not** landed —
`firstOrderIndB_step` is its table-side half, and the model-side half needs an inversion of
`Lean4Lean.TrEnv'` at an inductive name that the pinned fork does not have.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Witness

/-! ## The first-order domain -/

/-- The block `decl` is declared by `env`'s own declaration list. -/
def HasInduct (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds

/-- A first-order field type: a bare type former, either one of the block's own (`own`) or
one the closure `fo` already accepts. Constructor types are closed — `VConstant.WF` types
them in the empty context — so a block's self-reference arrives as a `.const`, and there is
no `.bvar` clause: binder `i` sits under `i` binders, so a `.bvar` there is a parameter or an
earlier field, never a type former. -/
def FOType (own : List Name) (fo : Name → Prop) : VExpr → Prop
  | .const I _ => I ∈ own ∨ fo I
  | _ => False

/-- The four clauses of a first-order block, at the closure `fo` and the block's own type
former names `own`. `informative` is the result-sort half of `[L Def. 6]`, stated with the
successor shape the tree's `InformativeInd` reads; `fields` is `[L Def. 14]` restricted to
unapplied field types. `mono` and `noIndices` are declared scope restrictions. -/
structure FirstOrderDecl (own : List Name) (fo : Name → Prop) (decl : VInductDecl) : Prop where
  /-- Monomorphic. A declared scope restriction. -/
  mono : decl.uvars = 0
  /-- Every type former of the block lands in a successor sort. -/
  informative : ∀ t ∈ decl.types, ∃ l, vResultSort t.type = some (.succ l)
  /-- Index-free. A declared scope restriction. -/
  noIndices : ∀ t ∈ decl.types, t.type.piArity = decl.nparams
  /-- Every constructor binder — parameters included — is a first-order field type. -/
  fields : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ i < c.type.piArity,
    ∃ A, c.type.piBinders[i]? = some A ∧ FOType own fo A

/-- A post-fixed point of the first-order condition: every name `fo` accepts is declared by a
block all of whose members are first-order w.r.t. `fo` itself. The checker's visited set is
the witness. -/
def FOClosed (env : VEnv) (fo : Name → Prop) : Prop :=
  ∀ J, fo J → ∃ decl, HasInduct env decl ∧
    FirstOrderDecl (decl.types.map (·.name)) fo decl ∧ ∃ t ∈ decl.types, t.name = J

/-- `I` is a first-order inductive type of `env`. The closure is existentially quantified
here rather than a parameter: a free `fo` is satisfied by `fun _ => True`, under which the
predicate accepts a type former with an arbitrary field. -/
def FirstOrderInd (env : VEnv) (I : Name) : Prop := ∃ fo, FOClosed env fo ∧ fo I

/-- The block a first-order type former belongs to, in the form upstream ask 6 reads. -/
theorem FirstOrderInd.indDeclOf {env : VEnv} {I : Name} (h : FirstOrderInd env I) :
    IndDeclOf env I := by
  obtain ⟨fo, hcl, hI⟩ := h
  obtain ⟨decl, ⟨ds, hds, hd⟩, -, t, hmem, hname⟩ := hcl I hI
  exact ⟨ds, decl, t, hds, hd, hmem, hname⟩

/-- A first-order type former is informative: its declared type — the block's own, read off
the environment the block produced — lands in a successor sort. -/
theorem FirstOrderInd.informativeInd {env : VEnv} {I : Name} (h : FirstOrderInd env I) :
    InformativeInd env I := by
  obtain ⟨fo, hcl, hI⟩ := h
  obtain ⟨decl, ⟨ds, hds, hd⟩, hdecl, t, hmem, hname⟩ := hcl I hI
  obtain ⟨e₀, e₁, -, hadd, hle⟩ := wf'_induct_origin hds hd
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hfind := VEnv.addTypes_find hT t hmem
  have hle' : envT ≤ env :=
    ((VEnv.addCtors_le hC).trans ((VEnv.addRecs_le hR).trans (VEnv.addRules_le hP))).trans hle
  exact ⟨_, hname ▸ hle'.constants hfind, hdecl.informative t hmem⟩

/-- Upstream ask 6 at a first-order type former: a spine headed by it is definitionally
equal to no sort and to no Π-type. -/
theorem FirstOrderInd.notSortNotPi {env : VEnv} {I : Name} (A : UpstreamAsks env) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hfo : FirstOrderInd env I)
    {ius : List VLevel} {iargs : List VExpr}
    (hisT : ∃ V, env.HasType U Γ (VExpr.mkApps (.const I ius) iargs) V) :
    (∀ u, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const I ius) iargs) (.sort u)) ∧
    (∀ X Y, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const I ius) iargs) (.forallE X Y)) := by
  obtain ⟨ds, decl, t, hds, hdecl, hmem, rfl⟩ := hfo.indDeclOf
  exact A.constArityInv hds hΓ hdecl hmem hisT

/-! ## The Boolean checker -/

/-- The leading Π-binder types of a source type, outermost first — the `Lean.Expr` twin of
`Lean4Lean.VExpr.piBinders`. -/
def piDomains : Expr → List Expr
  | .forallE _ t b _ => t :: piDomains b
  | _ => []

/-- `FOType`'s decision: a constructor binder is a bare type former of the block itself or
one the callback `rec` accepts. -/
def foFieldB (own : List Name) (rec : Name → Bool) : Expr → Bool
  | .const K _ => own.contains K || rec K
  | _ => false

/-- One member of a candidate block, checked against the table: monomorphic, index-free,
informative, declaring the same block, and with every constructor binder a first-order field
type. -/
def foMemberB (tbl : SourceTable) (own : List Name) (rec : Name → Bool) (J : Name) : Bool :=
  match tbl.ind? J with
  | none => false
  | some Jval =>
    Jval.levelParams.isEmpty && Jval.numIndices == 0 && Jval.all == own &&
      informativeB Jval &&
      Jval.ctors.all fun c => (piDomains c.type).all (foFieldB own rec)

/-- The fuelled first-order check: `I` is tabled, belongs to the block it names, and every
member of that block is `foMemberB` at one less unit of fuel. -/
def firstOrderIndB (tbl : SourceTable) : Nat → Name → Bool
  | 0, _ => false
  | fuel + 1, I =>
    match tbl.ind? I with
    | none => false
    | some Ival =>
      Ival.all.contains I && Ival.all.all (foMemberB tbl Ival.all (firstOrderIndB tbl fuel))

/-! ## What the checker's verdict says about the table -/

/-- The field check is monotone in its callback. -/
theorem foFieldB_mono {own : List Name} {r r' : Name → Bool} (hr : ∀ K, r K = true → r' K = true) :
    ∀ {A : Expr}, foFieldB own r A = true → foFieldB own r' A = true
  | .const .., h => by
    simp only [foFieldB, Bool.or_eq_true] at h ⊢
    exact h.imp id (hr _)
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .app .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit .., h | .mdata .., h | .proj .., h => h

/-- The member check is monotone in its callback. -/
theorem foMemberB_mono {tbl : SourceTable} {own : List Name} {r r' : Name → Bool} {J : Name}
    (hr : ∀ K, r K = true → r' K = true) (h : foMemberB tbl own r J = true) :
    foMemberB tbl own r' J = true := by
  unfold foMemberB at h ⊢
  split at h
  · exact absurd h (by simp)
  · rename_i Jval _
    simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨h.1, fun c hc A hA => foFieldB_mono hr (h.2 c hc A hA)⟩

/-- More fuel decides no fewer names. -/
theorem firstOrderIndB_mono {tbl : SourceTable} :
    ∀ {fuel fuel' : Nat} {I : Name}, fuel ≤ fuel' →
      firstOrderIndB tbl fuel I = true → firstOrderIndB tbl fuel' I = true
  | 0, _, _, _, h => by simp [firstOrderIndB] at h
  | _ + 1, 0, _, hle, _ => by omega
  | fuel + 1, fuel' + 1, I, hle, h => by
    unfold firstOrderIndB at h ⊢
    split at h
    · exact absurd h (by simp)
    · rename_i Ival _
      simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
      exact ⟨h.1, fun J hJ =>
        foMemberB_mono (fun _ => firstOrderIndB_mono (by omega)) (h.2 J hJ)⟩

/-- **The table-side half of soundness.** One step of the checker's fixed point, read off
the table: an accepted name is tabled, belongs to the block it names, and every member of
that block satisfies the four clauses with its field types accepted at one less unit of
fuel. What this does *not* give is that the tabled block is a block of the model
environment — see the module header. -/
theorem firstOrderIndB_step {tbl : SourceTable} {fuel : Nat} {I : Name}
    (h : firstOrderIndB tbl (fuel + 1) I = true) :
    ∃ Ival, tbl.ind? I = some Ival ∧ I ∈ Ival.all ∧
      ∀ J ∈ Ival.all, ∃ Jval, tbl.ind? J = some Jval ∧
        Jval.all = Ival.all ∧ Jval.levelParams = [] ∧ Jval.numIndices = 0 ∧
        informativeB Jval = true ∧
        ∀ c ∈ Jval.ctors, ∀ A ∈ piDomains c.type, ∃ K us, A = .const K us ∧
          (K ∈ Ival.all ∨ firstOrderIndB tbl fuel K = true) := by
  unfold firstOrderIndB at h
  split at h
  · exact absurd h (by simp)
  · rename_i Ival hI
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    refine ⟨Ival, hI, h.1, fun J hJ => ?_⟩
    have hmem := h.2 J hJ
    unfold foMemberB at hmem
    split at hmem
    · exact absurd hmem (by simp)
    · rename_i Jval hJt
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hmem
      obtain ⟨⟨⟨⟨hlp, hni⟩, hall⟩, hinf⟩, hctors⟩ := hmem
      refine ⟨Jval, hJt, hall, hlp, by simpa using hni, hinf, fun c hc A hA => ?_⟩
      have := hctors c hc A hA
      match A with
      | .const K us =>
        exact ⟨K, us, rfl, by simpa [foFieldB, List.contains_iff_mem] using this⟩
      | .bvar .. | .fvar .. | .mvar .. | .sort .. | .app .. | .lam .. | .forallE ..
      | .letE .. | .lit .. | .mdata .. | .proj .. => exact absurd this (by simp [foFieldB])

/-! ## What the checker decides -/

namespace FOFixture

/-- The binary-trees benchmark's tree, redeclared here: `VerifyBench` is a separate library
that imports this one, so its own declarations are out of reach. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

/-- A wrapper whose field is a function type: outside the domain, since `FOType` admits only
bare type formers. -/
inductive Fn where
  | mk : (Nat → Nat) → Fn

end FOFixture

/-- The reified slice the examples are decided on. -/
def foTable : SourceTable :=
  reify% Nat, Bool, FOFixture.Tree, FOFixture.Fn, True, List, Prod

example : firstOrderIndB foTable 64 ``Nat = true := by rfl

example : firstOrderIndB foTable 64 ``Bool = true := by rfl

example : firstOrderIndB foTable 64 ``FOFixture.Tree = true := by rfl

/-- A function-typed field is rejected: `FOType` is `.const`-headed. -/
example : firstOrderIndB foTable 64 ``FOFixture.Fn = false := by rfl

/-- A proposition is rejected: its result sort is not a successor. -/
example : firstOrderIndB foTable 64 ``True = false := by rfl

/-- `List Nat` and `Nat × Nat` are first-order data, but the predicate is chosen at the
*declaration* level, so a universe-polymorphic former is out of the domain. -/
example : firstOrderIndB foTable 64 ``List = false := by rfl

example : firstOrderIndB foTable 64 ``Prod = false := by rfl

/-! ## The shapes a source evaluation returns -/

/-- What an `SEval` derivation returns: a λ, a type, or a constant-headed spine of values
whose head is a constructor or a type former. The argument clause is what the first-order
induction recurses on. -/
inductive SValue (env : VEnv) : Expr → Prop
  /-- λ-abstractions are values. -/
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) : SValue env (.lam n ty b bi)
  /-- Sorts are values. -/
  | sort {u : Level} : SValue env (.sort u)
  /-- Π-types are values. -/
  | forallE {n : Name} {ty b : Expr} {bi : BinderInfo} : SValue env (.forallE n ty b bi)
  /-- A constructor spine of values. -/
  | ctor {c I : Name} {k : Nat} {us : List Level} {args : List Expr} (hc : CtorOf env c I k)
      (hargs : ∀ i, i < args.length → SValue env args[i]!) :
      SValue env (mkApps (.const c us) args)
  /-- A type-former spine of values. -/
  | ind {c : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat} {us : List Level}
      {args : List Expr} (hi : IndInfo env c iid np nfs)
      (hargs : ∀ i, i < args.length → SValue env args[i]!) :
      SValue env (mkApps (.const c us) args)

/-- **A source evaluation returns a value.** One arm per rule: the three value arms conclude
directly, and every reduction arm reads its result off the continuation. -/
theorem SEval.svalue {env : VEnv} {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Δ : VLCtx} {e v : Expr} (h : SEval env bo Us fl Δ e v) : SValue env v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | sort => exact .sort
  | forallE => exact .forallE
  | beta _ _ _ _ _ _ ihb => exact ihb
  | zeta _ _ _ _ ihb => exact ihb
  | deltaC _ _ _ _ _ _ _ _ _ ihcont => exact ihcont
  | ctorVal hc _ _ hlen _ ihargs => exact .ctor hc (fun i hi => ihargs i (hlen ▸ hi))
  | indVal hi hlen _ ihargs => exact .ind hi (fun i hi => ihargs i (hlen ▸ hi))
  | iota _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihcont => exact ihcont
  | proj _ _ _ _ _ _ ihcont => exact ihcont
  | lit _ _ ih => exact ih

/-- **`SEval.svalue` fires** at its constructor arm: the nullary constructor of `Erases`'s
one-block fixture evaluates to itself, and the shape read off that evaluation is
`SValue.ctor`. -/
theorem svalue_ctor_fires {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Δ : VLCtx} {us : List Level} : SValue blkEnv (.const blkMk us) :=
  (SEval.ctorVal (bo := bo) (Us := Us) (fl := fl) (Δ := Δ) (us := us) (args := [])
    (argsv := []) blk_ctorOf blk_indInfo (by simp) rfl (by simp)).svalue

/-! ## The fields of a first-order value -/

/-- The source theory's typing of a first-order constructor value: every argument of a
well-typed constructor value of a first-order inductive is itself typed at a first-order
type former. A named premise, class **C**, and the only one the two theorems below add.
It is `FirstOrderDecl.fields` transported to a value; its discharge needs the spine typing
inversion filed upstream, the identification of the constructor's own type former with the
one the value is typed at, and uniqueness of the block declaring a former. -/
def FOFields (env : VEnv) (Us : List Name) : Prop :=
  ∀ {I I' c : Name} {k i : Nat} {us : List Level} {cargs : List Expr} {vv a : VExpr}
    {ius : List VLevel} {iargs : List VExpr},
    FirstOrderInd env I → CtorOf env c I' k →
    TrExprS env Us [] (mkApps (.const c us) cargs) vv →
    env.HasType Us.length [] vv (VExpr.mkApps (.const I ius) iargs) →
    i < cargs.length → TrExprS env Us [] cargs[i]! a →
    ∃ (J : Name) (jus : List VLevel) (jargs : List VExpr),
      FirstOrderInd env J ∧ env.HasType Us.length [] a (VExpr.mkApps (.const J jus) jargs)

/-- Two pointwise erasures of the same list agree when each element's erasure is unique. -/
theorem forall₂_unique {α β : Type _} {R : α → β → Prop} {as : List α} {ts ts' : List β}
    (h : ∀ a ∈ as, ∀ x y, R a x → R a y → x = y) :
    List.Forall₂ R as ts → List.Forall₂ R as ts' → ts = ts' := by
  intro h₁
  induction h₁ generalizing ts' with
  | nil => intro h₂; cases h₂; rfl
  | @cons a b as bs hab _ ih =>
    intro h₂
    cases h₂ with
    | cons hab' hrest' =>
      rw [h a (List.mem_cons_self ..) _ _ hab hab',
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hrest']

/-! ## Uniqueness and box-freedom at a first-order value -/

/-- **The erasure of a first-order value is unique and box-free.** One induction over the
value's shape: a λ is excluded because its type is a Π and a first-order spine is not
(`UpstreamAsks.constArityInv`); a sort, a Π-type and a type-former spine are excluded because
they are erasable and a first-order value is not (`not_erasable_of_informative`); and a
constructor spine erases by the congruence alone — its boxed readings by the same fact, its
head by `constOrigin_not_ctorOf`, its arguments by the induction hypothesis at the field
typings `FOFields` supplies. -/
theorem firstorder_erases_core {env : VEnv} {Us : List Name} (henv : env.WF)
    (A : UpstreamAsks env) (P : IndSpineNotProp env) (F : FOFields env Us) :
    ∀ {v : Expr}, SValue env v →
      ∀ {I : Name} {ius : List VLevel} {iargs : List VExpr} {vv : VExpr} {t : LBTerm},
        FirstOrderInd env I → TrExprS env Us [] v vv →
        env.HasType Us.length [] vv (VExpr.mkApps (.const I ius) iargs) →
        Erases env Us [] v t → NoBox t ∧ ∀ t', Erases env Us [] v t' → t' = t := by
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓ : OnCtx (VLCtx.toCtx ([] : VLCtx)) (env.IsType Us.length) := hΔ.toCtx
  intro v hval
  induction hval with
  | lam n ty b bi =>
    intro I ius iargs vv t hfo hwt hty _
    exfalso
    cases hwt with
    | lam htyty _ _ =>
      obtain ⟨u, hu⟩ := htyty
      obtain ⟨-, B, hB⟩ := hty.lam_inv henv hΓ
      obtain ⟨w, hw⟩ := hty.isType henv hΓ
      exact (hfo.notSortNotPi A hΓ ⟨_, hw⟩).2 _ _
        (VEnv.IsDefEq.uniqU henv hΓ hty (hu.lam hB))
  | sort =>
    intro I ius iargs vv t hfo hwt hty _
    exact absurd (Erases.sort_erasable henv hwt)
      (not_erasable_of_informative henv A P hΓ hfo.indDeclOf hfo.informativeInd hty)
  | forallE =>
    intro I ius iargs vv t hfo hwt hty _
    exact absurd (Erases.forallE_erasable henv hΔ hwt)
      (not_erasable_of_informative henv A P hΓ hfo.indDeclOf hfo.informativeInd hty)
  | @ind c iid np nfs us args hi _ _ =>
    intro I ius iargs vv t hfo hwt hty _
    obtain ⟨hve, htrh⟩ := trExprS_spine_head args hwt
    exact absurd (erasable_mkApps henv hΔ args hwt htrh (Erases.indInfo_erasable henv hΔ hi htrh))
      (not_erasable_of_informative henv A P hΓ hfo.indDeclOf hfo.informativeInd hty)
  | @ctor c I' k us cargs hc _ ihargs =>
    intro I ius iargs vv t hfo hwt hty her
    obtain ⟨iid, np, nfs, hi⟩ := hc.indInfo
    have hnotEr : ¬ Erasable env Us.length (VLCtx.toCtx []) vv :=
      not_erasable_of_informative henv A P hΓ hfo.indDeclOf hfo.informativeInd hty
    -- every erasure of the spine is the congruence, at the constructor node
    have hshape : ∀ {s : LBTerm}, Erases env Us [] (mkApps (.const c us) cargs) s →
        ∃ ts, List.Forall₂ (Erases env Us []) cargs ts ∧
          s = LBTerm.mkApps (.construct iid k []) ts := by
      intro s hs
      rcases erases_mkApps_inv cargs hs with
        ⟨th, ts, hth, hts, rfl⟩ | ⟨pre, suf, ts, heq, ⟨we, htrwe, herwe⟩, -, rfl⟩
      · rcases Erases.const_inv hth with ⟨⟨we, htrwe, herwe⟩, rfl⟩ |
          ⟨I'', iid'', k'', np'', nfs'', hc'', hi'', rfl⟩ | ⟨-, ho, -⟩
        · exact absurd (erasable_mkApps henv hΔ cargs hwt htrwe herwe) hnotEr
        · obtain ⟨rfl, rfl⟩ := CtorOf.inj A hc'' hc
          obtain ⟨rfl, -, -⟩ := IndInfo.inj A hi'' hi
          exact ⟨ts, hts, rfl⟩
        · exact absurd hc (constOrigin_not_ctorOf A ho I' k)
      · refine absurd (erasable_mkApps henv hΔ suf ?_ htrwe herwe) hnotEr
        rw [heq, mkApps_append] at hwt
        exact hwt
    -- each argument's erasure is unique and box-free
    have harg : ∀ a ∈ cargs, ∀ (x : LBTerm), Erases env Us [] a x →
        NoBox x ∧ ∀ y, Erases env Us [] a y → y = x := by
      intro a ha x hx
      obtain ⟨i, hilt, rfl⟩ := Lower.mem_getElem! ha
      obtain ⟨w, htrw⟩ := trExprS_spine_mem cargs hwt _ ha
      obtain ⟨J, jus, jargs, hfoJ, hJty⟩ := F hfo hc hwt hty hilt htrw
      exact ihargs i hilt hfoJ htrw hJty hx
    obtain ⟨ts, hts, rfl⟩ := hshape her
    refine ⟨?_, fun t' ht' => ?_⟩
    · rw [NoBox_mkApps]
      refine ⟨by simp, fun x hx => ?_⟩
      obtain ⟨a, ha, hax⟩ := forall₂_mem_right hts x hx
      exact (harg a ha x hax).1
    · obtain ⟨ts', hts', rfl⟩ := hshape ht'
      rw [forall₂_unique (fun a ha x y hx hy => ((harg a ha x hx).2 y hy).symm) hts' hts]

/-- **First-order erasure is deterministic** `[S §7.3]`: at a value of a first-order
inductive type the relation `Erases` has one image. -/
theorem firstorder_erases_deterministic {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {I : Name} {us : List VLevel} {args : List VExpr} {v : Expr} {vv : VExpr}
    {t₁ t₂ : LBTerm} (henv : env.WF) (A : UpstreamAsks env) (P : IndSpineNotProp env)
    (F : FOFields env Us) (hfo : FirstOrderInd env I) (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env bo Us fl [] v v) (h₁ : Erases env Us [] v t₁)
    (h₂ : Erases env Us [] v t₂) : t₁ = t₂ :=
  (firstorder_erases_core henv A P F hval.svalue hfo hwt hty h₂).2 t₁ h₁

/-- **The erasure of a first-order value holds no box** `[L Def. 6]`. Of the erasure, not of
its lowered image: box-freedom does not transport along `Lower`, whose `fixConst` arm relates
a box-free constant to a block whose definitions carry their own boxes. -/
theorem firstorder_no_box {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {I : Name} {us : List VLevel} {args : List VExpr} {v : Expr} {vv : VExpr}
    {t : LBTerm} (henv : env.WF) (A : UpstreamAsks env) (P : IndSpineNotProp env)
    (F : FOFields env Us) (hfo : FirstOrderInd env I) (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env bo Us fl [] v v) (h : Erases env Us [] v t) : NoBox t :=
  (firstorder_erases_core henv A P F hval.svalue hfo hwt hty h).1

/-! ## The predicate is inhabited -/

namespace FOModel

/-- The fixture's type former: an empty `Type`-valued inductive with no parameters, no
indices and no constructors. -/
def E : Name := `E

/-- The fixture's eliminator. -/
def ERec : Name := `E.rec

/-- The eliminator's motive binder, `E → Prop`. -/
def motiveTy : VExpr := .forallE (.const E []) (.sort .zero)

/-- The eliminator's type, `∀ (C : E → Prop) (z : E), C z`. -/
def recTy : VExpr := .forallE motiveTy (.forallE (.const E []) (.app (.bvar 1) (.bvar 0)))

/-- The type former's declaration. -/
def typeVal : VInductiveType :=
  { uvars := 0, type := .sort (.succ .zero), name := E, ctors := [] }

/-- The eliminator's declaration: one motive, no minors, no ι rules. -/
def recVal : VRecursor :=
  { uvars := 0, type := recTy, name := ERec, all := [E], numParams := 0, numMotives := 1,
    numMinors := 0, numIndices := 0, k := false, rules := [] }

/-- The block. -/
def decl : VInductDecl := { uvars := 0, nparams := 0, types := [typeVal], recs := [recVal] }

/-- The environment after the type former. -/
def envT : VEnv := (VEnv.empty.addConst E ⟨0, .sort (.succ .zero)⟩).getD .empty

theorem decl_addTypes : decl.addTypes VEnv.empty = some envT := rfl

theorem decl_addTypesCtors : decl.addTypesCtors VEnv.empty = some envT := rfl

theorem envT_E : envT.constants E = some ⟨0, .sort (.succ .zero)⟩ := rfl

/-- The fixture's environment: the block alone. -/
def env : VEnv := (VEnv.empty.addInduct decl).getD .empty

theorem env_eq : VEnv.empty.addInduct decl = some env := rfl

/-- The type former is a `Type`-valued constant once it is declared. -/
theorem E_ty {Γ : List VExpr} : VEnv.HasType envT 0 Γ (.const E []) (.sort (.succ .zero)) :=
  VEnv.HasType.const envT_E nofun rfl

/-- The eliminator's type is a type once the type former is declared. -/
theorem recTy_ty : VEnv.HasType envT 0 [] recTy
    (.sort (.imax (.imax (.succ .zero) (.succ .zero)) (.imax (.succ .zero) .zero))) :=
  VEnv.HasType.forallE (VEnv.HasType.forallE E_ty (VEnv.HasType.sort (l := .zero) trivial)) <|
    VEnv.HasType.forallE E_ty <|
      VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ .zero))
        (VEnv.HasType.bvar .zero)

/-- The block is a well-formed declaration. Every constructor clause is vacuous — the type
former has none — and the eliminator eliminates into `Prop`, so no large-elimination
obligation arises. -/
theorem decl_wf : decl.WF VEnv.empty where
  types_wf := by
    intro t ht; cases List.mem_singleton.1 ht
    exact ⟨.succ (.succ .zero), VEnv.HasType.sort (l := .succ .zero) trivial⟩
  ctors_wf := by intro _ _ t ht c hc; cases List.mem_singleton.1 ht; cases hc
  recs_wf := by
    intro envC h r hr
    rw [decl_addTypesCtors] at h; cases h
    cases List.mem_singleton.1 hr
    exact ⟨_, recTy_ty⟩
  types_uvars := by intro t ht; cases List.mem_singleton.1 ht; rfl
  ctors_uvars := by intro t ht c hc; cases List.mem_singleton.1 ht; cases hc
  universes := by
    intro envT' h
    refine ⟨.succ .zero, ?_, ?_, ?_⟩
    · intro t ht; cases List.mem_singleton.1 ht; exact ⟨rfl, Nat.le_refl _⟩
    · intro t ht c hc; cases List.mem_singleton.1 ht; cases hc
    · rintro ⟨r, hr, hu⟩; cases List.mem_singleton.1 hr; exact absurd hu (by simp [recVal])
  recs_elim := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨.inl rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa [recVal] using hi
    subst this
    exact ⟨motiveTy, rfl, rfl⟩
  rec_params := by intro r hr; cases List.mem_singleton.1 hr; rfl
  ctors_params := by intro t ht c hc; cases List.mem_singleton.1 ht; cases hc
  ctors_result := by intro t ht c hc; cases List.mem_singleton.1 ht; cases hc
  ctors_positive := by intro t ht c hc; cases List.mem_singleton.1 ht; cases hc
  recs_over_block := by
    intro r hr; cases List.mem_singleton.1 hr
    exact ⟨typeVal, List.mem_singleton_self _, rfl⟩
  rec_counts := by
    intro r hr; cases List.mem_singleton.1 hr
    exact ⟨rfl, rfl, fun t ht _ => by cases List.mem_singleton.1 ht; rfl⟩
  rec_shape := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨rfl, ?_, nofun, 0, Nat.zero_lt_one, ⟨_, rfl, E, rfl, ⟨[], rfl⟩, _, rfl, rfl⟩, rfl⟩
    intro i hi
    have : i = 0 := by simpa [recVal] using hi
    subst this
    exact ⟨motiveTy, rfl, ⟨.zero, rfl⟩, rfl⟩
  rules_nodup := by intro r hr; cases List.mem_singleton.1 hr; simp [recVal]
  rules_ctor := by intro r hr ru hru; cases List.mem_singleton.1 hr; cases hru
  types_have_rec := by
    intro t ht; cases List.mem_singleton.1 ht
    exact ⟨recVal, List.mem_singleton_self _, rfl⟩
  rules_total := by
    intro r hr t ht _ c hc; cases List.mem_singleton.1 hr; cases List.mem_singleton.1 ht; cases hc
  rule_shape := by intro r hr ru hru; cases List.mem_singleton.1 hr; cases hru
  rules_wf := by intro _ _ r hr ru hru; cases List.mem_singleton.1 hr; cases hru

/-- The fixture is well formed. -/
theorem wf' : VEnv.WF' [.induct decl] env := .decl (.induct decl_wf env_eq) .empty

/-- **`FirstOrderInd` is inhabited**: the fixture's empty `Type`-valued type former is
first-order, at the closure that accepts exactly it. -/
theorem firstOrderInd_E : FirstOrderInd env E := by
  refine ⟨(· = E), fun J hJ => ⟨decl, ⟨_, wf', List.mem_singleton_self _⟩, ?_, typeVal,
    List.mem_singleton_self _, hJ ▸ rfl⟩, rfl⟩
  exact { mono := rfl
          informative := fun t ht => by cases List.mem_singleton.1 ht; exact ⟨.zero, rfl⟩
          noIndices := fun t ht => by cases List.mem_singleton.1 ht; rfl
          fields := fun t ht c hc => by cases List.mem_singleton.1 ht; cases hc }

end FOModel

end LeanToLambdaBox
