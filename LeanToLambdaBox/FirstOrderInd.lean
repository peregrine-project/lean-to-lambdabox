import LeanToLambdaBox.ErasesCorrect.Steps

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
`not_erasable_of_informative` (`Origin.lean`, stated once and used twice), and what remains
is the constructor congruence.

`mono` (monomorphic) and `noIndices` (index-free) are **declared scope restrictions**: they
reject types that are first-order and box-free, and they are booked to this development, not
to Letouzey's Def. 14 or to MetaRocq's `firstorder_ind`. `informative` is the result-sort
half of Def. 6 in the **successor** shape — a declared scope restriction too, and one the
monomorphy clause makes cheap. It implies the semantic relevance the target-facing relations
read, `InformativeInd`, whose criterion is that the declared result level never evaluates to
zero; the checker computes the successor shape as `succSortB`.

The two theorems' only premise beyond MetaRocq's own list is `UpstreamAsks env`:
`fOFields_of_asks` derives the source-theory typing of a first-order constructor value from
asks 9 and 10 and ask 2's declaration-level uniqueness. `firstorder_no_box` is of the
**erasure**, not of the lowered value; the induction returns the image's shape, `FOSpine`, and
`noBox_lower_of_foSpine` is box-freedom of the lowered one at it. `firstOrderIndB`'s soundness
against `FirstOrderInd` is **not** in the tree: `firstOrderIndB_step` is its table-side half,
and the model-side half needs the inversion of `Lean4Lean.TrEnv'` at an inductive name that is
filed ask 4, so `FirstOrderInd` is reached today only through `FOModel.firstOrderInd_E`.
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
  obtain ⟨decl, ⟨ds, hds, hd⟩, -, t, hmem, hname⟩ := hcl _ hI
  exact ⟨ds, decl, t, hds, hd, hmem, hname⟩

/-- A first-order type former is informative: its declared type — the block's own, read off
the environment the block produced — lands in a successor sort. -/
theorem FirstOrderInd.informativeInd {env : VEnv} {I : Name} (h : FirstOrderInd env I) :
    InformativeInd env I := by
  obtain ⟨fo, hcl, hI⟩ := h
  obtain ⟨decl, ⟨ds, hds, hd⟩, hdecl, t, hmem, hname⟩ := hcl _ hI
  obtain ⟨e₀, e₁, -, hadd, hle⟩ := wf'_induct_origin hds hd
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hfind := VEnv.addTypes_find hT t hmem
  have hle' : envT ≤ env :=
    ((VEnv.addCtors_le hC).trans ((VEnv.addRecs_le hR).trans (VEnv.addRules_le hP))).trans hle
  exact informativeInd_of_succ ⟨_, hname ▸ hle'.constants hfind, hdecl.informative t hmem⟩

set_option linter.unusedVariables false in
/-- Upstream ask 6 at a first-order type former: a spine headed by it is definitionally
equal to no sort and to no Π-type. `A` is unused since the pin: the body now cites
`Lean4Lean.VEnv.IsDefEqU.const_arity_inv` directly, and the parameter stays to keep
`firstorder_erases_core`'s call site unchanged. -/
theorem FirstOrderInd.notSortNotPi {env : VEnv} {I : Name} (A : UpstreamAsks env) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hfo : FirstOrderInd env I)
    {ius : List VLevel} {iargs : List VExpr}
    (hisT : ∃ V, env.HasType U Γ (VExpr.mkApps (.const I ius) iargs) V) :
    (∀ u, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const I ius) iargs) (.sort u)) ∧
    (∀ X Y, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const I ius) iargs) (.forallE X Y)) := by
  obtain ⟨ds, decl, t, hds, hdecl, hmem, rfl⟩ := hfo.indDeclOf
  exact VEnv.IsDefEqU.const_arity_inv hds hΓ hdecl hmem hisT

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
landing in a syntactic successor sort, declaring the same block, and with every constructor
binder a first-order field type. The relevance test is `succSortB`, the fragment's stricter
one, matching `FirstOrderDecl.informative`; `informativeB` is the never-zero test that
matches `InformativeInd`. -/
def foMemberB (tbl : SourceTable) (own : List Name) (rec : Name → Bool) (J : Name) : Bool :=
  match tbl.ind? J with
  | none => false
  | some Jval =>
    Jval.levelParams.isEmpty && Jval.numIndices == 0 && Jval.all == own &&
      succSortB Jval &&
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
        succSortB Jval = true ∧
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
  | iota _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihcont => exact ihcont
  | proj _ _ _ _ _ _ _ _ ihcont => exact ihcont
  | lit _ _ ih => exact ih

/-- **`SEval.svalue` fires** at its constructor arm: the nullary constructor of `Erases`'s
one-block fixture evaluates to itself, and the shape read off that evaluation is
`SValue.ctor`. -/
theorem svalue_ctor_fires {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Δ : VLCtx} {us : List Level} : SValue blkEnv (.const blkMk us) :=
  (SEval.ctorVal (bo := bo) (Us := Us) (fl := fl) (Δ := Δ) (us := us) (args := [])
    (argsv := []) blk_ctorOf blk_indInfo (by simp) rfl (by simp)).svalue

/-! ## The fields of a first-order value -/

/-- The field condition is monotone in the closure. -/
theorem FOType.widen {own : List Name} {fo fo' : Name → Prop} (h : ∀ K, fo K → fo' K) :
    ∀ {A : VExpr}, FOType own fo A → FOType own fo' A
  | .const .., hA => hA.imp id (h _)
  | .bvar .., hA | .sort .., hA | .app .., hA | .lam .., hA | .forallE .., hA => hA

/-- A first-order block stays first-order at a wider closure. -/
theorem FirstOrderDecl.widen {own : List Name} {fo fo' : Name → Prop} {decl : VInductDecl}
    (h : ∀ K, fo K → fo' K) (hd : FirstOrderDecl own fo decl) :
    FirstOrderDecl own fo' decl where
  mono := hd.mono
  informative := hd.informative
  noIndices := hd.noIndices
  fields := fun t ht c hc i hi =>
    let ⟨A, hA, hfo⟩ := hd.fields t ht c hc i hi
    ⟨A, hA, FOType.widen h hfo⟩

/-- **Every type former of a first-order block is first-order.** `FOClosed` accepts the names
of `fo`, and a block's own formers need not be among them; widening `fo` by the block's names
keeps the post-fixed point, since the closure occurs only positively in `FirstOrderDecl`. -/
theorem firstOrderInd_of_own {env : VEnv} {fo : Name → Prop} {decl : VInductDecl} {J : Name}
    (hcl : FOClosed env fo) (hd : HasInduct env decl)
    (hfd : FirstOrderDecl (decl.types.map (·.name)) fo decl)
    (hJ : J ∈ decl.types.map (·.name)) : FirstOrderInd env J := by
  refine ⟨fun K => fo K ∨ K ∈ decl.types.map (·.name), fun K hK => ?_, .inr hJ⟩
  rcases hK with hK | hK
  · obtain ⟨d, hdd, hfdd, t, ht, hname⟩ := hcl K hK
    exact ⟨d, hdd, hfdd.widen (fun _ h => .inl h), t, ht, hname⟩
  · obtain ⟨t, ht, hname⟩ := List.mem_map.1 hK
    exact ⟨decl, hd, hfd.widen (fun _ h => .inl h), t, ht, hname⟩

/-- **The source theory's typing of a first-order constructor value**: every argument of a
well-typed constructor value of a first-order inductive is itself typed at a first-order type
former. Three kernel facts carry it, and each is a field of `UpstreamAsks`: the constructor's
own former is the value's by ask 10 (`indSpineInj`) against the result spine `peel_piSpine_head`
reaches; the block `FOClosed` exhibits is the block `CtorOf` exhibits by ask 2's
declaration-level uniqueness, which is what lets `FirstOrderDecl.fields` name the field's
former; and the spine's typing peels without ask 9, since a *translated* spine carries its
argument typings in `TrExprS`'s own `app` arm (`trExprS_spine_peel`). -/
theorem fOFields_of_asks {env : VEnv} {Us : List Name} (henv : env.WF) (A : UpstreamAsks env) :
    ∀ {I I' c : Name} {k i : Nat} {us : List Level} {cargs : List Expr} {vv a : VExpr}
      {ius : List VLevel} {iargs : List VExpr},
    FirstOrderInd env I → CtorOf env c I' k →
    TrExprS env Us [] (mkApps (.const c us) cargs) vv →
    env.HasType Us.length [] vv (VExpr.mkApps (.const I ius) iargs) →
    i < cargs.length → TrExprS env Us [] cargs[i]! a →
    ∃ (J : Name) (jus : List VLevel) (jargs : List VExpr),
      FirstOrderInd env J ∧ env.HasType Us.length [] a (VExpr.mkApps (.const J jus) jargs) := by
  intro I I' c k i us cargs vv a ius iargs hfo hct hwt hty hilt htra
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓ : OnCtx (VLCtx.toCtx ([] : VLCtx)) (env.IsType Us.length) := hΔ.toCtx
  obtain ⟨iid, np, nfs, hi⟩ := hct.indInfo
  have hdI' : IndDeclOf env I' := IndInfo.indDeclOf A hi
  have hdI : IndDeclOf env I := hfo.indDeclOf
  obtain ⟨cci, nind, hcst, hres⟩ := hct.ctorResult_at A hi.arity
  obtain ⟨_, htrhead⟩ := trExprS_spine_head _ hwt
  cases htrhead with
  | const hci₂ hmap hlen =>
    rename_i cus'
    obtain rfl : cci = _ := Option.some.inj (hcst.symm.trans hci₂)
    have hlen' : _ = cci.uvars := ((List.mapM_eq_some.1 hmap).length_eq).symm.trans hlen
    have hT := hasType_const (Γ := VLCtx.toCtx ([] : VLCtx)) hcst
      (VLevel.WF.of_mapM_ofLevel hmap) hlen'
    obtain ⟨V, vargs, hvlen, hvarg, hveV, hpeel⟩ :=
      trExprS_spine_peel henv hΔ _ (.const hci₂ hmap hlen) hT hwt
    obtain ⟨u, hu⟩ := hT.isType henv hΓ
    have hVI : env.IsDefEqU Us.length (VLCtx.toCtx []) V (VExpr.mkApps (.const I ius) iargs) :=
      VEnv.IsDefEq.uniqU henv hΓ hveV hty
    have hspine : PiSpine I' (np + nfs[k]!) (cci.type.instL cus') :=
      (piSpine_of_piBody hres.1 (by obtain ⟨us₀, idx, -, h⟩ := hres.2; exact ⟨us₀, _, h⟩)).instL
    have hvlen' : vargs.length = np + nfs[k]! :=
      peel_piSpine henv A hΓ hdI' hdI vargs hspine ⟨_, hu⟩ hpeel hVI
    obtain ⟨jus₀, jargs₀, hVI'⟩ := peel_piSpine_head henv hΓ vargs hspine hvlen' ⟨_, hu⟩ hpeel
    obtain rfl : I' = I := A.indSpineInj hΓ hdI' hdI
      (VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hVI') hVI)
    -- the block `FOClosed` exhibits is the block the constructor comes from
    obtain ⟨fo, hcl, hI⟩ := hfo
    obtain ⟨decl, hdhas, hfd, t, ht, hname⟩ := hcl _ hI
    obtain ⟨ds₂, env₀, decl₂, t₂, ctor, hds₂, hd₂, hle₂, hmem₂, hname₂, hk, hcn⟩ := id hct
    obtain ⟨ds₁, hds₁, hd₁⟩ := hdhas
    have hblk : IndBlockBelow env decl := ⟨ds₁, env, hds₁, .rfl, hd₁⟩
    obtain rfl : decl₂ = decl :=
      indBlock_uniq A ⟨ds₂, env₀, hds₂, hle₂, hd₂⟩ hblk ⟨t₂, hmem₂, hname₂⟩ ⟨t, ht, hname⟩
    obtain rfl : t₂ = t := indBlockBelow_type_uniq hblk hmem₂ ht (hname₂.trans hname.symm)
    have hctor : ctor ∈ t₂.ctors := List.mem_of_getElem? hk
    -- the constructor's declared type is the type the head is typed at
    obtain ⟨e₀, e₁, -, hadd, hle₁⟩ := wf'_induct_origin hds₂ hd₂
    obtain ⟨envT, envC, envR, hT₀, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
    have hcstc : env.constants c = some ctor.toVConstant :=
      hcn ▸ hle₂.constants (hle₁.constants
        (((VEnv.addRecs_le hR).trans (VEnv.addRules_le hP)).constants
          (VEnv.addCtors_find hC t₂ hmem₂ ctor hctor)))
    obtain rfl : cci = ctor.toVConstant := Option.some.inj (hcst.symm.trans hcstc)
    -- the field's own type former
    have hipi : i < ctor.type.piArity := by
      have : ctor.type.piArity = np + nfs[k]! := hres.1
      omega
    obtain ⟨Afld, hbind, hfoty⟩ := hfd.fields t₂ ht ctor hctor i hipi
    obtain ⟨J, jus₀, rfl⟩ : ∃ J jus, Afld = .const J jus := by
      cases Afld <;> first
        | exact ⟨_, _, rfl⟩
        | exact absurd hfoty (by simp [FOType])
    have hmaj : MajorPremiseAt J i (ctor.toVConstant.type.instL cus') :=
      (majorPremiseAt_of_piBinders hbind).instL
    obtain ⟨jus, jargs, htyv⟩ := peel_major henv hΓ i vargs hmaj ⟨_, hu⟩ hpeel (by omega)
    refine ⟨J, jus, jargs, ?_, VEnv.HasType.defeqU_l henv hΓ
      (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) (hvarg i hilt) htra) htyv⟩
    rcases hfoty with hJ | hJ
    · exact firstOrderInd_of_own hcl ⟨ds₁, hds₁, hd₁⟩ hfd hJ
    · exact ⟨fo, hcl, hJ⟩

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

/-! ## The shape of a first-order value's image -/

/-- **The λ□ image of a first-order value**: an applied-form constructor tree. A `.construct`
node carries no arguments on the emitted output (F-ETA2), so the tree is built by `.app`, and
these two rules are the whole predicate. -/
inductive FOSpine : LBTerm → Prop
  | ctor {iid : InductiveId} {k : Nat} : FOSpine (.construct iid k [])
  | app {f a : LBTerm} : FOSpine f → FOSpine a → FOSpine (.app f a)

/-- Non-vacuity: the λ□ peano numeral `1`, applied form, is a constructor tree. -/
example {iid : InductiveId} :
    FOSpine (.app (.construct iid 1 []) (.construct iid 0 [])) := .app .ctor .ctor

/-- A constructor tree holds no box: neither rule introduces one. -/
theorem FOSpine.noBox {t : LBTerm} (h : FOSpine t) : NoBox t := by
  induction h with
  | ctor => trivial
  | app _ _ ihf iha => exact ⟨ihf, iha⟩

/-- A nullary constructor node applied to constructor trees is one. -/
theorem FOSpine.mkApps {iid : InductiveId} {k : Nat} :
    ∀ {ts : List LBTerm}, (∀ x ∈ ts, FOSpine x) →
      FOSpine (LBTerm.mkApps (.construct iid k []) ts) := by
  have key : ∀ (ts : List LBTerm) (f : LBTerm), FOSpine f → (∀ x ∈ ts, FOSpine x) →
      FOSpine (LBTerm.mkApps f ts) := by
    intro ts
    induction ts with
    | nil => intro f hf _; exact hf
    | cons a rest ih =>
        intro f hf hall
        exact ih _ (.app hf (hall a (by simp))) (fun x hx => hall x (by simp [hx]))
  intro ts hall; exact key ts _ .ctor hall

/-- The head of a constructor tree is its nullary constructor node. -/
theorem FOSpine.spineHead {t : LBTerm} (h : FOSpine t) :
    ∃ iid k, LBTerm.spineHead t = .construct iid k [] := by
  induction h with
  | @ctor iid k => exact ⟨iid, k, rfl⟩
  | app _ _ ihf _ => exact ihf

/-- **A constructor tree has a constructor tree for a lowered image.** The `.construct` arm
goes through `Lower.source_construct`, which excludes all three block arms itself by
`Lower.ne_block_image` — a constructor node is neither a constant nor a λ — and returns a
zero-length argument list; the `.app` arm goes through `Lower.source_app`, whose `elimApp`
disjunct is refuted on the head, a `.const` there and a `.construct` here. The nullary route
`Lower.source_construct_nil`, which keeps a `.fix` disjunct, is not used. -/
theorem FOSpine.lower {Γ : GlobalDeclarations} {s t : LBTerm}
    (hs : FOSpine s) (h : Lower Γ s t) : FOSpine t := by
  induction hs generalizing t with
  | @ctor iid k =>
      obtain ⟨args', rfl, hlen, -⟩ := Lower.source_construct h rfl
      rw [List.eq_nil_of_length_eq_zero hlen]; exact .ctor
  | @app f a hf' ha' ihf iha =>
      rcases Lower.source_app h rfl with ⟨f', a', rfl, hf, ha⟩ |
        ⟨kn, iid, np, dp, nfs, pre, disc, minors, -, -, -, heq⟩
      · exact .app (ihf hf) (iha ha)
      · exfalso
        obtain ⟨iid', k', hsh⟩ := (FOSpine.app hf' ha').spineHead
        rw [heq, LBTerm.spineHead_mkApps] at hsh
        exact LBTerm.noConfusion hsh

/-- **Box-freedom of the lowered first-order value.** The shape `firstorder_erases_core`
concludes is what makes the transport go through: `NoBox` alone does not transport along
`Lower`, whose `fixConst` arm relates a box-free `.const` to a block whose definitions carry
their own boxes (`noBox_lower_needs_noFix`). -/
theorem noBox_lower_of_foSpine {Γspec : GlobalDeclarations} {tv₀ tv : LBTerm}
    (hfo : FOSpine tv₀) (hlow : Lower Γspec tv₀ tv) : NoBox tv :=
  (hfo.lower hlow).noBox

/-! ## Uniqueness and box-freedom at a first-order value -/

/-- **The erasure of a first-order value is unique and a constructor tree.** One induction
over the value's shape: a λ is excluded because its type is a Π and a first-order spine is not
(`Lean4Lean.VEnv.IsDefEqU.const_arity_inv`); a sort, a Π-type and a type-former spine are
excluded because they are erasable and a first-order value is not
(`not_erasable_of_informative`); and a
constructor spine erases by the congruence alone — its boxed readings by the same fact, its
head by `constOrigin_not_ctorOf`, its arguments by the induction hypothesis at the field
typings `fOFields_of_asks` supplies. `FOSpine.noBox` reads box-freedom off the shape. -/
theorem firstorder_erases_core {env : VEnv} {Us : List Name} (henv : env.WF)
    (A : UpstreamAsks env) :
    ∀ {v : Expr}, SValue env v →
      ∀ {I : Name} {ius : List VLevel} {iargs : List VExpr} {vv : VExpr} {t : LBTerm},
        FirstOrderInd env I → TrExprS env Us [] v vv →
        env.HasType Us.length [] vv (VExpr.mkApps (.const I ius) iargs) →
        Erases env Us [] v t → FOSpine t ∧ ∀ t', Erases env Us [] v t' → t' = t := by
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
      (not_erasable_of_informative henv A hΓ hfo.indDeclOf hfo.informativeInd hty)
  | forallE =>
    intro I ius iargs vv t hfo hwt hty _
    exact absurd (Erases.forallE_erasable henv hΔ hwt)
      (not_erasable_of_informative henv A hΓ hfo.indDeclOf hfo.informativeInd hty)
  | @ind c iid np nfs us args hi _ _ =>
    intro I ius iargs vv t hfo hwt hty _
    obtain ⟨hve, htrh⟩ := trExprS_spine_head args hwt
    exact absurd (erasable_mkApps henv hΔ args hwt htrh (Erases.indInfo_erasable henv hΔ hi htrh))
      (not_erasable_of_informative henv A hΓ hfo.indDeclOf hfo.informativeInd hty)
  | @ctor c I' k us cargs hc _ ihargs =>
    intro I ius iargs vv t hfo hwt hty her
    obtain ⟨iid, np, nfs, hi⟩ := hc.indInfo
    have hnotEr : ¬ Erasable env Us.length (VLCtx.toCtx []) vv :=
      not_erasable_of_informative henv A hΓ hfo.indDeclOf hfo.informativeInd hty
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
    -- each argument's erasure is unique and a constructor tree
    have harg : ∀ a ∈ cargs, ∀ (x : LBTerm), Erases env Us [] a x →
        FOSpine x ∧ ∀ y, Erases env Us [] a y → y = x := by
      intro a ha x hx
      obtain ⟨i, hilt, rfl⟩ := Lower.mem_getElem! ha
      obtain ⟨w, htrw⟩ := trExprS_spine_mem cargs hwt _ ha
      obtain ⟨J, jus, jargs, hfoJ, hJty⟩ := fOFields_of_asks henv A hfo hc hwt hty hilt htrw
      exact ihargs i hilt hfoJ htrw hJty hx
    obtain ⟨ts, hts, rfl⟩ := hshape her
    refine ⟨?_, fun t' ht' => ?_⟩
    · refine FOSpine.mkApps (fun x hx => ?_)
      obtain ⟨a, ha, hax⟩ := forall₂_mem_right hts x hx
      exact (harg a ha x hax).1
    · obtain ⟨ts', hts', rfl⟩ := hshape ht'
      rw [forall₂_unique (fun a ha x y hx hy => ((harg a ha x hx).2 y hy).symm) hts' hts]

/-- **First-order erasure is deterministic** `[S §7.3]`: at a value of a first-order
inductive type the relation `Erases` has one image. -/
theorem firstorder_erases_deterministic {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {I : Name} {us : List VLevel} {args : List VExpr} {v : Expr} {vv : VExpr}
    {t₁ t₂ : LBTerm} (henv : env.WF) (A : UpstreamAsks env)
    (hfo : FirstOrderInd env I) (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env bo Us fl [] v v) (h₁ : Erases env Us [] v t₁)
    (h₂ : Erases env Us [] v t₂) : t₁ = t₂ :=
  (firstorder_erases_core henv A hval.svalue hfo hwt hty h₂).2 t₁ h₁

/-- **The erasure of a first-order value holds no box** `[L Def. 6]`. Of the erasure, not of
its lowered image: box-freedom does not transport along `Lower`, whose `fixConst` arm relates
a box-free constant to a block whose definitions carry their own boxes. What does transport is
the shape the same induction returns — `noBox_lower_of_foSpine`. -/
theorem firstorder_no_box {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {I : Name} {us : List VLevel} {args : List VExpr} {v : Expr} {vv : VExpr}
    {t : LBTerm} (henv : env.WF) (A : UpstreamAsks env)
    (hfo : FirstOrderInd env I) (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env bo Us fl [] v v) (h : Erases env Us [] v t) : NoBox t :=
  (firstorder_erases_core henv A hval.svalue hfo hwt hty h).1.noBox

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
