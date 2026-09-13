# MetaCoq / MetaRocq certified erasure — reference analysis for the rework

**Source.** M. Sozeau, Y. Forster, M. Lennon-Bertrand, J. B. Nielsen, N. Tabareau, T. Winterhalter,
*Correct and Complete Type Checking and Certified Erasure for Coq, in Coq*, J. ACM 72(1), Article 8,
January 2025 (74 pp.). Formalization: MetaCoq v1.2 for Coq 8.16,
`https://github.com/MetaCoq/metacoq/tree/v1.2-8.16`. Section references below are to the article.
Text read in full; §7 (pp. 8:59–8:64) read line by line, together with everything §7 depends on:
§3.1 (syntax/environments), §3.5 (typing, `checker_flags`), §3.6 (well-formed environments,
positivity, cumulative inductives, allowed eliminations), §4.2.1 (reduction, syntactic equality),
§5.4 (subject reduction), §5.5 (normalization axiom), §5.6 (weak call-by-value standardization,
values, progress), §5.7 (canonicity/classification), §6.2 (abstract computational environment),
§6.4 (type inference and *retyping*), §8 (related work: CertiCoq, ConCert, Forster et al. OCaml),
§9 (future work), and Tables 1–2 (judgment forms).

Everything quoted below in `code` blocks is transcribed from the article text verbatim, including
its own elisions (`(* . . . *)`). Where the article prints a figure as an image and the extracted
text does not contain it, this is flagged explicitly — those are the places where the rework must
consult the Coq sources rather than the paper.

---

## 1. Summary

MetaCoq's erasure is organised as a four-layer construction, and *the layering is the design*:

1. **A target language, λ□**, that is syntactically PCUIC minus the type-only subterms plus one
   extra constructor `□` (Fig. 16), with a **weak call-by-value big-step semantics** obtained from
   PCUIC's `⇓` by *three* extra rules that say what happens when a `□` reaches an eliminator
   position (application, case, fix).
2. **An erasure *relation*** `Σ; Γ ⊢ t ⇝E t'` (Fig. 18) which is a plain congruence over the source
   syntax **plus one non-deterministic rule** `erases_box : isErasable Σ Γ t → Σ; Γ ⊢ t ⇝E □`, with
   *exactly one* side condition anywhere in the relation: `Subsingleton Σ ci.(ci_ind)` on the `tCase`
   rule. The relation exists because the erasure *function* is **not** closed under evaluation (the
   `(fun X : Type ⇒ (1, fun x : X ⇒ x)) Type` counterexample, §7.3): reduction can expose erasability
   that was not visible before.
3. **An erasure *function*** `E Γ Ht t` (Fig. 17), defined by `Equations` over the syntax, gated by a
   decision procedure `is_erasableb` that reflects `isErasable`; it is built on the **retyping**
   algorithm of §6.4 and runs against an **abstract global environment** `X` connected to a
   specification environment by `X ∼ext Σ`. The bridge is the single lemma `erases_erase`: the graph
   of the function is contained in the relation.
4. **Correctness**: a forward simulation `erases_correct` for the *relation* against `⇓`, and then a
   *collapse* of the relation onto the function on **first-order values**
   (`firstorder_erases_deterministic`), giving the observational capstone
   `erase_correct_firstorder`. Optimisations (§7.4) are **not** inlined into the eraser: they are
   separate λ□→λ□ passes (`optimize`) proven to preserve evaluation, and the semantics is
   parameterized by `WcbvFlags` so that the pass can be shown to *discharge* a semantic rule
   (rule (2)) rather than merely to commute with it.

The two structural lessons for the rework are (a) **the premise budget is tiny** — `wf Σ`,
`welltyped Σ t`, `axiom_free Σ`, `firstorder_ind Σ i`, and the environment relation, nothing else —
and (b) **anything that is not a congruence rule of the source syntax is a separate pass over the
target with its own theorem**, not an extra premise or an extra constructor of the erasure relation.

---

## 2. Formal objects

### 2.1 The target calculus λ□ (§7.1, Fig. 16)

Transcribed verbatim:

```coq
Inductive E.term : Set :=
| □            : E.term
| E.tRel       : N → E.term
| E.tLambda    : name → E.term → E.term
| E.tLetIn     : name → E.term → E.term → E.term
| E.tApp       : E.term → E.term → E.term
| E.tConst     : kername → E.term
| E.tConstruct : inductive → N → E.term
| E.tCase      : (inductive ∗ N) → E.term → list (N ∗ E.term) → E.term
| E.tProj      : projection → E.term → E.term
| E.tFix       : mfixpoint E.term → N → E.term
| E.tCoFix     : mfixpoint E.term → N → E.term.
```

Notes taken from the text around the figure:

* "λ□ is syntactically similar to PCUIC. It has the same constructors, but subterms which can only
  contain types are left out (because they would be erased anyway)." Concretely: `tSort`, `tProd`,
  `tInd` disappear; `tLambda` loses its domain annotation; `tLetIn` loses its type annotation;
  `tConst`/`tConstruct` lose the `universe_instance`; `tCase` keeps only `(inductive * N)` (the
  inductive and the number of parameters) instead of a full `predicate term`, and branches become
  `N ∗ E.term` (arity of the branch + body) instead of `branch term`.
* "Technically, the code shares the same syntax as that for PCUIC, but inside a different module."
  The `E.` prefix is presentational.
* **`tCoFix` is retained.** λ□ is the target of Coq erasure, and Coq has coinductives.
* **Note for Peregrine**: the on-disk λ□ of `peregrine-tool` (`EAst`) is this datatype, with
  branches carrying a `list name` (the `E (bcontext x)` of Fig. 18) rather than a bare arity `N`,
  and with a later `tPrim` node. Fig. 16 is the JACM snapshot; MetaRocq's `EAst` has drifted
  slightly (primitive values). See §5 "Requirements".

### 2.2 λ□ evaluation (§7.1)

The article does **not** print the λ□ evaluation rules. It says (verbatim): "The weak call-by-value
(big-step) evaluation relation for λ□ is defined like for PCUIC (see Section 5.6), with three
amendments" — and footnote 29: "We present only the changes for big-step evaluation."

The three amendments, verbatim:

```
(1) If Σ ⊢ a ⇓ □ then Σ ⊢ E.tApp a t ⇓ □.
(2) If Σ ⊢ a ⇓ □ and Σ ⊢ t □ · · · □ ⇓ v then Σ ⊢ E.tCase (i, p) a [(n,t)] ⇓ v.
                          |    {z    }
                             n times
(3) The E.tFix rule is similarly extended to also apply if the principal argument evaluates to □.
```

The article's own reading of these rules (verbatim, lightly re-wrapped):

* Rule (1) "corresponds to the fact that applying a type or a proof to an argument will be a type or
  proof."
* Rule (2) "corresponds to the fact that if a case analysis is not erased to □, this is because it
  returns something computational, and consequently the case analysis on the proof which was erased
  to □ has to come from a subsingleton elimination (Section 3.6.3). Due to this, the rule actually
  covers all possible eliminations from tProp to produce a computational value. This will be explicit
  in the proof of correctness of erasure (Section 7.3)."
* Rule (3) "allows the unfolding of fixpoints computing a value by recursion on proofs."

Observe the shape of rule (2): the case must have **exactly one branch** `[(n,t)]`, and the branch
body is applied to exactly `n` boxes — i.e. the arity `n` recorded in the branch is used to
manufacture the erased constructor arguments. This is the semantic counterpart of subsingleton
elimination, and it is the rule that §7.4's `optimize` pass makes unnecessary.

`WcbvFlags` (§7.4, verbatim):

```coq
Class WcbvFlags := { with_prop case : B ; (* other flags not described in this paper *) }.

Definition disable_prop cases fl := {| with_prop case := false ; (* . . . *) |}.
```

so evaluation is written `eval fl Σ t v` when the flags matter.

**PCUIC-side ⇓ (§5.6).** Also not printed: "Since it is entirely standard to derive the definition
from the definition of reduction, we omit it in the article and refer the reader to the Coq code."
The article *does* give the ingredients it is built from:

* one-step weak cbv reduction `Σ ⊢ t ⇝wcbv t'` (Fig. 11 — **image, not in the extracted text**),
  described as "a restriction of `Σ ; Γ ⊢ t ⇝ t'` for closed terms t", with no local context because
  "weak call-by-value reduction ensures that reduction of closed term will never have to consider
  open terms";
* values (Fig. 12, transcribed verbatim):

```coq
Definition atom t :=          Variant value_head (nargs : N) : term → Type :=
 match t with                 | value_head_cstr ind c u mdecl idecl cdecl :
 | tInd _ _                     declared_constructor Σ (ind, c) mdecl idecl cdecl →
 | tConstruct _ _ _             nargs ≤ cstr_arity mdecl cdecl →
 | tFix _ _                     value_head nargs (tConstruct ind c u)
 | tCoFix _ _                 | value_head_ind ind u : value_head nargs (tInd ind u)
 | tLambda _ _ _              | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
 | tSort _                    | value_head_fix mfix idx rarg fn :
 | tProd _ _ _                  cunfold_fix mfix idx = Some (rarg, fn) →
 | tPrim _ ⇒ true               nargs ≤ rarg →
 | _ ⇒ false                    value_head nargs (tFix mfix idx).
 end.
                              Inductive value : term → Type :=
                              | value_atom t : atom t → value t
                              | value_app_nonnil f args : value_head #|args| f → args ≠ [] →
                                                          All value args → value (mkApps f args).
```

  "'call-by-value' means that arguments are always fully evaluated before a function or fixpoint
  application, and 'weak' refers to the fact that abstraction and fixpoint are treated as values,
  without evaluating their bodies first."
* auxiliary results the standardization proof relies on, listed verbatim: "that weak call-by-value
  reduction steps do not change the value under evaluation; that evaluation is included in the
  reflexive transitive closure of reduction; and also that subject reduction applies to evaluation.
  Furthermore, it relies on the fact that results of evaluation are values, and values evaluate to
  themselves."

### 2.3 Erasability (§7.2)

Verbatim:

```coq
Definition isErasable Σ Γ t := { T & Σ ; Γ ⊢ t : T × (isArity T + Σ ; Γ ⊢ T : tProp) }.
```

"specifying that a term t is erasable when it is typeable with some type T which is either an arity
(an n-ary dependent function type ending with a sort) – so when t is a type – or typeable itself with
sort tProp – so when t is a proof."

`isArity` is defined in footnote 13 of §3.6: "Arities are the subset of n-ary dependent products and
let-ins whose final codomain is a sort."

So `isErasable` is a **disjunction of two genuinely different phenomena**:
*type formers* (`isArity T`, i.e. `t` is a type/type-former: `t : T` and `T` is an arity) and
*proofs* (`Σ; Γ ⊢ T : tProp`). Both are erased to the *same* `□`.

**The `prop_sub_type` flag.** Immediately after Fig. 16 the article states (verbatim):

> "Note that, like in the extraction currently implemented in Coq, the rule Prop ≤ Type has to be
> disabled for type checking (using the flag structure explained at the end of Section 3.5) to ensure
> that erasability is stable by expansion."

From §3.5, verbatim:

```coq
Class checker_flags := {
 check_univs : B ;
 (* default true, setting to false adds the (inconsistent) Type : Type rule *)
 prop_sub_type : B ;
 (* default true, false for extraction, enables Prop <: Type *)
 indices_matter : B ;
 (* default false, lets indices matter for the type universe of an inductive *)
 lets_in_constructor_types : B
 (* default true, allows constructor types to contain lets *) }.
```

and "The theory we develop assumes in general that … the Prop ≤ Type rule is available (**except for
the erasure correctness proofs**)".

**`is_erasableb` and its soundness (§7.2).** Verbatim, condensed:

* "Its implementation is based on a decision procedure `is_erasableb` which checks whether a
  well-typed term is erasable. The implementation relies on the **retyping** function which correctly
  reconstructs the type of merely well-typed terms, along with **weak-head reduction** to inspect
  types. We leave out the implementation of `is_erasableb` as we only need that it **reflects** the
  property `isErasable`."
* The hard half of the reflection proof: "This boolean reflection proof in particular involves
  proving that if `isErasable Σ Γ T → ⊥` then `is_eraseableb` returns false. This requires
  meta-theoretic properties beyond those proved already for the system, as it focuses on proof terms
  specifically (those whose sort is `tProp`) and essentially quantifies over all possible types for
  T. In particular, it is necessary to show that if a term is typeable by a type which can have sort
  `tProp`, then for all other terms that are syntactically smaller or equal to it up to universes and
  are typeable, they must also have sort `tProp`."
* The obstruction and its fix (verbatim): "This is a generalization of principality that is
  particularly tricky to prove in presence of cumulative inductive types, as for example `nil@{i} N`
  and `nil@{j} N` are in this relation but can have unrelated sorts … To solve this issue, we devise
  an alternative, coarser version of the cumulativity relation (in PCUIC: `CumulProp`), named **sort
  quality equivalence**, that identifies all `Type@{_}` sorts, becoming symmetric. Cumulativity is
  hence a subrelation of sort quality equivalence. We can then prove a theorem that essentially says
  that two typeable terms that are in the syntactical inequality up to universes relation have sort
  quality equivalent types. From this, it follows that if one has sort `tProp`, then the other must
  have it too, establishing a **unique sort quality** principle."

This is the paper's *oracle-soundness* story: the eraser's decision procedure is justified by a
unique-sort-quality metatheorem, not assumed.

### 2.4 The erasure function E (§7.2, Fig. 17)

Verbatim:

```coq
Equations E Γ (Ht : ∀ Σ, X ∼ext Σ → welltyped Σ Γ t) : E.term :=
 E Γ HΓ t with (is_erasableb X Γ t Ht) :=
 { | left is_er := □;
   | right not_is_er with t := {
      | tRel i := E.tRel i
      | tConst kn u := E.tConst kn
      | tLambda na b b' := E.tLambda na.(binder_name) (E (Γ , na : b) b' _)
      | tApp f u := E.tApp (E Γ f _) (E Γ u _)
     (* . . . *) }}.
```

Reading, verbatim: "It starts by looking at the result of `is_erasableb`. When the decision procedure
says that the term is erasable, it simply returns `□`. When the term is not erasable, it proceeds by
induction on the syntax of the term, coarsely by simply applying the erasure functions on
sub-arguments and removing some type information (such as the universe instance `u` in the `tConst`
case). Note the use of `Equations` to defer the definition of complex arguments such as the proof
that a sub-term is well-typed using underscores."

Three structural facts worth pinning down:

* The function is **total by construction on well-typed input**: its argument `Ht` is a proof of
  well-typedness *for every* concrete `Σ` in relation with the abstract `X`, squashed so that no
  computational content of `Σ` leaks in. It is not a partial/`Option` function and it is not
  fuel-driven.
* The recursion is **structural on the term**, with the well-typedness proofs for subterms
  reconstructed by inversion (the `_` holes).
* The **box test comes first, at every node**. There is no "erasable" pre-pass and no separate
  relevance analysis: `is_erasableb` is called on every subterm.

### 2.5 The erasure relation (§7.3, Fig. 18)

Verbatim, including the article's own elision:

```coq
Inductive Σ; Γ ⊢ _ ⇝E _ : term → E.term → Prop :=
| erases_tRel : ∀ i : N, Σ; Γ ⊢ tRel i ⇝E E.tRel i
| erases_tLambda : ∀ (na : name) (b t : term) (t' : E.term),
   Σ; (Γ , na : b) ⊢ t ⇝E t' → Σ; Γ ⊢ tLambda na b t ⇝E E.tLambda na t'
| erases_tApp : ∀ (f u : term) (f' u' : E.term),
   Σ; Γ ⊢ f ⇝E f' → Σ; Γ ⊢ u ⇝E u' → Σ; Γ ⊢ tApp f u ⇝E E.tApp f' u'
| erases_tConst : ∀ (kn : kername) (u : universe_instance),
   Σ; Γ ⊢ tConst kn u ⇝E E.tConst kn
| erases_tCase : ∀ (ci : case_info) (p : predicate term)
   (c : term) (brs : list (branch term)) (c' : E.term) (brs′ : list (list name × E.term)),
   Subsingleton Σ ci.(ci_ind) →
   Σ; Γ ⊢ c ⇝E c' →
   All2 (fun (x : branch term) (x' : list name × E.term) ⇒
    Σ; Γ ++ inst_case_branch_context p x ⊢ bbody x ⇝E snd x' × E (bcontext x) = fst x') brs brs′ →
   Σ; Γ ⊢ tCase ci p c brs ⇝E E.tCase (ci.(ci_ind), ci.(ci npar)) c' brs′
(* . . . *)
| erases_box : ∀ t : term, isErasable Σ Γ t → Σ; Γ ⊢ t ⇝E □.
```

The elided `(* . . . *)` covers `tLetIn`, `tConstruct`, `tProj`, `tFix`, `tCoFix` (and, in the
current MetaRocq sources, `tPrim`). The paper is explicit that these are *congruences*: "Essentially,
the relation extends the erasure function by nondeterministic rules allowing not to erase a certain
part of a term which could be erased. **The only exception here is the tCase rule.**"

Key design points, verbatim:

* Why the relation at all: "Ideally, we would like to prove that if `Σ ⊢ t ⇓ v`, then we have
  `E Σ ⊢ E [] t ⇓ E [] v` … However, this already fails on simple counter-examples: the Coq term
  `(fun X : Type ⇒ (1, fun x : X ⇒ x)) Type` has type `N ∗ (Type → Type)` and evaluates to the value
  `(1, fun x : Type ⇒ x)`. Erasing the term yields `(fun X ⇒ (1, fun x ⇒ x)) □`, with value
  `(1, fun x ⇒ x)`. Erasing the value however yields `(1, □)`, because `fun x : Type ⇒ x` is a type
  former of type `Type → Type`, which is an arity and thus erased to `□`. This means intuitively that
  **the erasure function can erase more parts of the term after it has been reduced**."
* The relation is what is **closed under weak call-by-value evaluation**; the function is not.
* Why `tCase` carries `Subsingleton`: "If the `tCase` matches on a proof of a proposition which is
  not a `Subsingleton` (i.e., there is more than one branch in the case analysis), the whole case
  analysis has to be erased. This is necessary because **erased discriminees do not contain any
  information about which branch to use during evaluation**. For subsingleton propositions, there is
  at most one branch where all arguments are proofs and thus can be erased, they can thus be still
  evaluated (by picking the one available branch, if any)."
* Structural metatheory of the relation (verbatim): "We can prove **global weakening, weakening and
  substitutivity** of the erasure relation."
* On first-order data, "the relation and the function agree, and we can still get the strongest
  result described above on such first-order types."

`Subsingleton` itself is not printed in §7; §3.6.3 defines the criterion it names (verbatim): "An
inductive in sort P is considered a subsingleton when it has **at most one constructor**, where **all
arguments have sort Prop** again, i.e., are of type `P : Prop` for some `P`." Formalised in the
environment as `ind_kelim : allowed_eliminations` with

```coq
Inductive allowed_eliminations : Set := IntoProp | IntoAny.

Fixpoint elim_sort_prop_ind (ind_ctors_sort : list (list Universe)) :=
 match ind_ctors_sort with
 | [] ⇒ IntoAny
 | [ tProp :: s ] ⇒ elim_sort_prop_ind [s]
 | _ ⇒ IntoProp
 end.
```

"For an inductive definition to be valid, its allowed eliminations, recorded in the field
`ind_kelim`, should be at least as restrictive as the minimal one computed using
`elim_sort_prop_ind`." Note `[] ⇒ IntoAny` — the empty inductive (`False`) eliminates into anything;
`[ tProp :: s ]` peels one all-Prop constructor.

### 2.6 Erasure of global environments (§7.3, §7.4)

Two definitions, both in the article:

* **The naive one**, `Σ ⇝E Σ'`, listed in Table 2 as "Pointwise extension of ⇝E". Verbatim from
  §7.3: "It can be defined in a straightforward way by pointwise extension of the erasure relation.
  Concretely, we however use an alternative definition which drops unneeded dependencies in Σ′ (e.g.,
  type definitions), we discuss this in detail in Section 7.4."
* **The real one**, `erases_deps Σ Σ' t'` (§7.4), verbatim: "we use an inductive predicate
  `erases_deps Σ Σ' t'` stating that the global environment Σ' is obtained from applying erasure
  **recursively and selectively** to Σ by considering only the **dependencies of the erased term t'**,
  in a **bottom-up** fashion. Note that this is where we need the `abs_pop_decls` primitive that
  removes a declaration from the global context. **This models the `Recursive Extraction <term>`
  command of Coq.**"

Motivation, verbatim: "the erasure process as explained here is too inefficient to be executed on
realistic examples. The reason is that applying the erasure function pointwise to the global
environment will perform retyping and yield numerous constants that are erased to □ but not used
everywhere. This is because dependency on proofs disappears, as all proof are erased, but also
because in practice a term usually only depends on a small subset of the global environment it is
defined in."

Cost of the design, verbatim: "The correctness proof requires fairly involved reasoning with an
**accumulator** to account for these dependencies. It also requires particular **inversion lemmas
which have to be set up very carefully, accounting for the non-determinism of the erasure relation**."

**Environment representation (§3.6, verbatim):**

```coq
Inductive global_decl :=
| ConstantDecl : constant_body → global_decl
| InductiveDecl : mutual_inductive_body → global_decl.

Definition global_declarations := list (kername ∗ global_decl).

Record global_env :=
 { universes : LevelSet ∗ UnivConstraintSet; declarations : global_declarations }.

Record constant_body := { cst_type : term; cst_body : option term; cst_universes : universes_decl }.

Record mutual_inductive_body := {
 ind_finite : recursivity_kind; ind_npars : N ; ind_params : context;
 ind_universes : universes_decl; ind_variance : option (list Variance);
 ind_bodies : list one_inductive_body }.

Record one_inductive_body := {
 ind_name : ident; ind_indices : context; ind_sort : Universe; ind_type : term;
 ind_kelim : allowed_eliminations ;
 ind_ctors : list constructor_body ; ind_projs : list projection_body }.

Record constructor_body := { cstr_name : ident; cstr_args : context; cstr_indices : list term }.
Record projection_body := { proj_name : ident; proj_type : term }.
```

`wf Σ` is the well-formedness predicate: "all names should be globally unique"; "For constants, the
declared type should be typeable by a sort and the optional constant body should be typeable using
the declared type"; for inductive blocks, everything well-typed **plus** strict positivity (§3.6.1,
Fig. 3), the cumulative-variance conditions (§3.6.2), and the allowed-elimination condition (§3.6.3).
Note that the *declaration list is ordered by dependency*: "a list of declarations, properly ordered
according to dependencies".

**Abstract environment (§6.2, Fig. 14, verbatim):**

```coq
Class abs_env_struct (abs_env_impl abs_env_ext_impl : Type) := {
 ∼ : abs_env_impl → global_env → Prop;
 ∼ext : abs_env_ext_impl → global_env_ext → Prop;
 abs_env_init cs : on_global_univs cs → abs_env_impl;
 abs_env_add_decl X kn decl : (∀ Σ, X ∼ Σ → ∥ on_global_decls Σ kn decl ∥) → abs_env_impl;
 abs_env_add_udecl X udecl : (∀ Σ, X ∼ Σ → ∥ on_udecl Σ.(universes) udecl ∥) → abs_env_ext_impl ;
 abs_pop_decls : abs_env_impl → abs_env_impl ;
 abs_env_lookup : abs_env_ext_impl → kername → option global_decl;
 abs_env_level_mem : abs_env_ext_impl → Level → B;
 abs_env_leqb_level_n : abs_env_ext_impl → Z → Level → Level → B;
 abs_env_is_consistent : abs_env_impl → LevelSet ∗ UnivConstraintSet → B ;
 abs_env_guard : abs_env_ext_impl → FixOrCoFix → context → mfixpoint term → B}.
```

and the properties (Fig. 15, partially transcribed in the text):

```coq
Class abs_env_prop (abs_env_impl abs_env_ext_impl: Type) : Prop := {
 abs env ∃ X : ∥ {Σ & X ∼ Σ} ∥;
 abs_env_wf X Σ : X ∼ Σ → ∥ wf Σ ∥;
 abs_env_irr X Σ Σ' : X ∼ Σ → X ∼ Σ' → Σ = Σ';
 ... }
```

verbatim gloss: "Every abstract environment must be in relation to **exactly one** well-formed global
environment … Note here the use of the **squash** operator to prevent computational access to the
concrete global environment." And on `abs_pop_decls`: "This operation is used during erasure in order
to remove propositions from the environment, in order to keep only relevant content in it
(Section 7.4)."

This is the paper's answer to the question "how does an *executable* eraser talk about a
specification-level environment it must not compute with": one abstract carrier, a squashed
`∼`-relation, an irrelevance law making the specification environment unique, and lookup as the only
query.

### 2.7 First-order inductive types (§7.3)

Verbatim: "An inductive `i` is first-order in a global context Σ, written `firstorder_ind Σ i`, if
all its parameters, indices, and constructor arguments have a type which is syntactically of the
shape `mkApps (tInd i' u) args` where `i'` is again first-order."

and the crucial semantic consequence, verbatim: "The crucial property is that **values of first-order
types are just nested constructor applications where neither proofs nor types can occur**. Thus, on
those terms, the erasure relation and the erasure function coincide, because they both just erase the
type information to get an `E.term`."

### 2.8 The `optimize` pass (§7.4)

Verbatim:

```coq
optimize Σ (E.tCase ind c brs) := let brs ′ := map (on_snd (optimize Σ)) brs in
 if isprop_ind Σ ind then
    match brs ′ with
    | [(a, b)] ⇒ substl (repeat □ #|a|) b
    | _ ⇒ E.tCase ind (optimize Σ c) brs ′
    end
 else E.tCase ind (optimize Σ c) brs ′
```

"a function `optimize` that is essentially the identity function but for `E.tCase` where it performs
the optimization discussed above. The function `isprop_ind` checks whether an inductive definition
lives in Prop, in which case, when there is only one (optimized) branch, it directly returns that
branch where every argument is substituted by `□` (using the function `substl`)." Plus: "we also need
to extend `optimize` on environments because we need to optimize the body of definitions"
(`optimize_env`).

Why it is a *pass* and not part of the eraser, verbatim: "The erasure function defined in Letouzey's
PhD thesis and the definition described by Sozeau et al. [2019b] **immediately inline** an
optimization on case analysis … This is necessary for extraction, because `□` … cannot be extracted
to a constructor application as it must obey rule (1) from Page 60, thus a case analysis on it will
fail or get stuck in most target languages. … **However, this direct expansion of cases considerably
complicates the correctness proof of erasure, as it relies on typing invariants and inversion
principles. We decide not to include it into the erasure function, and instead define it as a second
pass.**"

And on future passes, verbatim: "In the same spirit, we plan on including other passes in the future,
e.g., optimization passes removing parameters from inductives. **If efficiency becomes a concern, we
can always inline these passes again in a new erasure function and prove that it yields the same
result as first running the erasure function as defined in this article and then the propagation
pass.**"

### 2.9 Supporting PCUIC-side objects the erasure theorems consume

| Object | Where | Content |
|---|---|---|
| `wf Σ`, `wf_ext Σ` | §3.6 | well-formed global environment (typing + universes + positivity + variance + kelim) |
| `welltyped Σ Γ t` | §7 | squashed `{T & Σ ; Γ ⊢ t : T}` |
| `axiom_free Σ` | §5.6 | `∀ c decl, declared_constant Σ c decl → cst_body decl ≠ None` |
| `Σ ; Γ ⊢ t ⇝ u`, `⇝∗` | §4.2.1 | one-step reduction (`red_beta`, `red_iota`, congruences) and its refl-trans closure |
| `progress` | §5.6 | `wf Σ → axiom_free Σ → Σ ; [] ⊢ t : T → {t' & Σ ⊢ t ⇝wcbv t'} + (value Σ t)` |
| `SN_to_WN` | §5.6 | `Acc (cored Σ []) t → Σ;[] ⊢ t : A → {v & Σ ⊢ t ⇓ v}` |
| `wcbv_standardization` | §5.6 | see §3 below |
| `normalization` | §5.5 | **axiom**: `wf_ext Σ → welltyped Σ Γ t → Acc (cored Σ Γ) t` |
| subject reduction | §5.4 | used for "subject reduction applies to evaluation" |
| `whnf_progress`, `classification`, `pcuic_canonicity` | §5.7 | closed inhabitants of inductive types are constructor/cofix headed |
| retyping | §6.4 | "takes a term and a proof that this term is well typed and computationally infers an explicit type for it … **This retyping algorithm is used by extraction, to detect types and proofs in the term that can be erased.**" |

---

## 3. Theorems and proof structure

### 3.1 `erases_erase` — the function refines the relation

Verbatim:

```coq
Lemma erases_erase Γ t (wt : ∀ Σ, X ∼ext Σ → welltyped Σ Γ t) :
 ∀ Σ, X ∼ext Σ → Σ ; Γ ⊢ t ⇝E E Γ t wt.
```

(The article's rendering drops the `⇝` glyph in places; the judgment is `Σ ; Γ ⊢ t ⇝E E Γ t wt`.)
This is the *entire* bridge between implementation and specification: one lemma, by induction
following the `Equations` structure of `E`, using soundness of `is_erasableb` in the `left` branch
(giving `erases_box`) and the congruence rules in the `right` branch. Note it is quantified over
*all* `Σ` related to the abstract `X`; combined with `abs_env_irr` that `Σ` is unique.

### 3.2 `simple_erases_correct` — the forward simulation, in its clean form

Verbatim:

```coq
Lemma simple_erases_correct : ∀ Σ t t' v Σ', wf Σ → welltyped Σ t →
 Σ ⊢ t ⇓ v → Σ; [] ⊢ t ⇝E t' → Σ ⇝E Σ' →
 ∃ v', Σ ; [] ⊢ v ⇝E v' ∧ ∥ Σ' ⊢ t' ⇓ v' ∥.
```

with the explicit caveat, verbatim: "**Note that this lemma is not proven in our development as we
directly prove the more complex optimized one instead (Section 7.4).**"

Shape to internalise: hypotheses are exactly `wf Σ`, `welltyped Σ t`, source evaluation, *some*
erasure of the term, *some* erasure of the environment; conclusion is existence of an erasure of the
*value* together with target evaluation to it. The value's erasure is **existentially quantified**
and generally **not** the erasure function applied to `v` — that is the whole point of using a
relation (§2.5 counterexample).

### 3.3 `erases_correct` — the theorem actually proven

Verbatim:

```coq
Lemma erases_correct Σ t t' v Σ' : wf Σ → welltyped Σ t →
 Σ ⊢ t ⇓ v → Σ; [] ⊢ t ⇝E t' → erases_deps Σ Σ' t' →
 ∃ v', Σ; [] ⊢ v ⇝E v' ∧ ∥ Σ' ⊢ t' ⇓ v' ∥.
```

Identical to `simple_erases_correct` except that `Σ ⇝E Σ'` is replaced by `erases_deps Σ Σ' t'`.

**Proof structure** (as described, plus what the text forces):

* Induction on the source evaluation `Σ ⊢ t ⇓ v`, with inversion on the erasure derivation
  `Σ; [] ⊢ t ⇝E t'` at each step. Because the relation is non-deterministic, **each** evaluation case
  splits into "the term was erased structurally" and "the term was erased to `□` by `erases_box`".
* The `erases_box` cases are where λ□'s three amendment rules are used: if the function/discriminee/
  fix principal argument erased to `□`, the target still evaluates, by rules (1)/(2)/(3). Rule (2) is
  where `Subsingleton` from `erases_tCase` is consumed — the article says explicitly the coverage of
  "all possible eliminations from tProp to produce a computational value" "will be explicit in the
  proof of correctness of erasure (Section 7.3)".
* Erasability must be **preserved by evaluation in the right direction**: values can be *more*
  erasable than terms, never less; this is why the conclusion quantifies over a *new* `v'`. This is
  also what forces `prop_sub_type := false` ("to ensure that erasability is stable by expansion").
* Subject reduction (§5.4) supplies well-typedness of intermediate terms so that `isErasable` premises
  can be re-established after each step; weakening/substitutivity of `⇝E` (§7.3) supply the
  congruence steps (β needs substitutivity, δ needs global weakening).
* `erases_deps` adds "fairly involved reasoning with an accumulator" and carefully staged inversion
  lemmas "accounting for the non-determinism of the erasure relation".

### 3.4 `firstorder_erases_deterministic` — relation collapses to function on first-order values

Verbatim:

```coq
Lemma firstorder_erases_deterministic : ∀ v v' i u args
 (wv : ∀ Σ, X ∼ext Σ → welltyped Σ [] v) Σ, X ∼ext Σ →
 firstorder_ind Σ i → Σ ; [] ⊢ v : mkApps (tInd i u) args →
 Σ ⊢ v ⇓ v → Σ ; [] ⊢ v ⇝E v' →
 v' = E [] v wv.
```

Note the hypothesis `Σ ⊢ v ⇓ v` — *`v` evaluates to itself*, i.e. `v` is a value. This is the
uniqueness / observational-determinism ingredient: on a first-order value, **every** erasure
derivation produces the term the function produces. Justification, verbatim: "values of first-order
types are just nested constructor applications where neither proofs nor types can occur".

### 3.5 `erase_correct_firstorder` — the capstone

Verbatim (the article's text drops some `⇝` glyphs; reconstructed reading in brackets):

```coq
Lemma erase_correct_firstorder : ∀ t v i u args Σ, X ∼ext Σ → axiom_free Σ →
 firstorder_ind Σ i →
 Σ ; [] ⊢ t : mkApps (tInd i u) args →
 Σ ; [] ⊢ t ⇝∗ v → ¬ { v' & Σ ; [] ⊢ v ⇝ v'} →
 ∃ wv', ∥ E Σ ⊢ E [] t wt ⇓ E [] v wv' ∥.
```

Verbatim gloss: "That is, if a closed term `t` of first-order inductive type reduces to a value `v`,
using the non-deterministic reduction `⇝∗` defined in Section 4.2, then the erasure of `t` evaluates
to the erasure of that value."

And the reason for `axiom_free`, verbatim: "Because the proof of correctness is based on **progress**
(Section 5.6), its statement has to be restricted to axiom free global environments."

**Proof structure** (composition, per the article):

1. `wcbv_standardization` (§5.6, verbatim):
   ```coq
   Lemma wcbv_standardization : ∀ Σ T t v, wf Σ → axiom_free Σ →
     Σ ; [] ⊢ t : T → Σ ; [] ⊢ t ⇝∗ v → ¬ {t' & Σ ; [] ⊢ v ⇝ t'} →
     {v' & Σ ⊢ t ⇓ v' ∗ Σ ; [] ⊢ v' ⇝∗ v}.
   ```
   turns the *non-deterministic* reduction hypothesis of the capstone into a big-step `⇓`. Its own
   proof: `normalization` axiom → `SN_to_WN` (which uses `progress`) gives `Σ ⊢ t ⇓ v'`; evaluation
   entails reduction; confluence with the assumed `t ⇝∗ v` plus irreducibility of `v` gives `v = v''`.
2. `erases_erase` turns `E [] t wt` into an erasure derivation.
3. `erases_correct` (with `erases_deps`) yields *some* `v'` with `v ⇝E v'` and target evaluation.
4. `firstorder_erases_deterministic` identifies that `v'` with `E [] v wv'`.

**Separate compilation corollary**, verbatim: "In particular, this observation entails that our type
and proof erasure function supports **separate compilation**: Let `Σ; Γ ⊢ mkApps f L : T`, where `T`
is a first-order type. Then the value of `mkApps (E f) (E L)` is the erasure of the value of
`mkApps f L`."

### 3.6 `optimize_correct`

Verbatim:

```coq
Lemma optimize_correct Σ t v : wf Σ → closed t →
 eval fl Σ t v →
 eval (disable_prop cases fl) (optimize_env Σ) (optimize Σ t) (optimize Σ v).
```

Verbatim gloss: "The correctness theorem for the propositional case expansion pass states that it
does not change the evaluation of a term … **The proof is direct as it just inlines the reduction
rule (2).**" Note the conclusion *strengthens the flags*: the pass eliminates the need for the
`with_prop case` rule. Hypotheses: `wf Σ` and `closed t` only — no typing, because this is a λ□→λ□
pass.

### 3.7 Trusted computing base

The article's own TCB accounting, verbatim from §1:

* "our formalization assumes strong normalization of the reduction, although most of the meta-theory
  is developed without using that axiom."
* "the assumed normalization with its accompanying requirements on the guard condition is the **only
  Achilles heel** of our formalization: if it holds, then there is no error in the implementation. So,
  this article proposes to switch from a **trusted code base to a trusted theory base paradigm**!
  Moreover, if one of the assumed properties were false, the implementation might be wrong, but there
  would be a much more serious problem to fix in Coq's meta-theory."
* "the equivalence between the declarative and algorithmic presentations of PCUIC is **axiom free**."
* "this axiom is propositional, so we also know that none of the programs we develop can rely on its
  computational content, and it can be safely erased by extraction."
* The guard condition is "abstract: we formalize it as a parameter of the theory which implies strong
  normalization, and we collect on the way the syntactic requirements it should fulfill for the
  meta-theory to satisfy important properties such as subject reduction."
* Scope exclusions stated up front: no module system, no template polymorphism, no η-conversion, no
  primitive integers/floats/arrays, no nested inductive types in the positivity judgment,
  SProp present but definitional proof irrelevance work in progress.

Downstream (§8): "an end-to-end correctness theorem for CertiCoq would be composed of an end-to-end
theorem connecting the weak call-by-value evaluation relation of λ□ to the operational semantics of
the compiled C program **and our correctness theorem for the erasure function**." — i.e. the λ□ `⇓`
relation *is* the composition interface, and `erase_correct_firstorder` is the intended left factor.
Same for Forster et al. (OCaml) and ConCert (Elm/Rust).

---

## 4. Lean-specific adaptations

The rework must mirror the paper's *architecture*, not transliterate PCUIC. Concrete divergences:

### 4.1 Source syntax and what the erasure relation may be a congruence over

`Lean.Expr` has: `bvar, fvar, mvar, sort, const, app, lam, forallE, letE, lit, mdata, proj`. Compared
with PCUIC's `term`:

* **No `tCase`, no `tFix`, no `tCoFix`, no `tConstruct` node.** Pattern matching is `casesOn`/`rec`
  applications (`Expr.const` heads); structural recursion is `brecOn`/`WellFounded.fix`; constructors
  are `Expr.const` heads. Coinduction does not exist.
* **`Expr.lit`** (`natVal`, `strVal`) has no PCUIC counterpart in Fig. 16 (`tPrim` was added to
  MetaRocq's `EAst` later).
* **`Expr.mdata`** is semantically transparent.
* **`Expr.proj`** corresponds to `tProj`.
* **`Expr.fvar` + local context**: MetaCoq's `E` is purely de Bruijn with a context `Γ`; a `MetaM`
  eraser is locally nameless. The relation must thread a `VLCtx`-like context exactly as lean4lean's
  `TrExprS` does (the current `Erases` already does this and that part is right).

**Consequence, and this is the single most important adaptation:** in MetaCoq, *every* λ□ constructor
except `□` is produced by a congruence rule over a *source constructor of the same name*. In Lean
that is false for `.construct`, `.case`, `.fix`. If those are produced by rules of the erasure
relation, the relation stops being "PCUIC syntax + box" and becomes "PCUIC syntax + box + a compiler",
which is exactly the epicyclic drift the review diagnosed (rules keyed on a 12-column registry with no
well-formedness predicate). The paper's own methodology says what to do instead (§7.4): **do not
inline the optimisation into the eraser; make it a separate pass over the target with its own
theorem, and parameterize the target semantics by flags so the pass can be shown to discharge a rule.**

So the principled layering for Lean is:

| Layer | Object | Mirrors |
|---|---|---|
| L0 | λ□ syntax + `WcbvEval` with box rules (1)(2)(3) + flags | §7.1 |
| L1 | `Erases : VLCtx → Expr → LBTerm → Prop`, a strict congruence over `Expr` + `erases_box`; recursors/constructors erase as `.const`-headed applications | Fig. 18 |
| L2 | `erase`/`visitExpr` and `erases_erase` | Fig. 17 + `erases_erase` |
| L3 | `erases_correct` forward simulation against lean4lean's evaluation/defeq | `erases_correct` |
| L4 | λ□→λ□ passes: **constructor blocking**, **`casesOn`→`.case`**, **`brecOn`/`WellFounded.fix`→`.fix`**, **`Nat` literal lowering**, **`@[csimp]`/`@[extern]` remapping** — each with an `optimize_correct`-shaped theorem | §7.4 |
| L5 | first-order collapse + capstone | §7.3 end |

That layering also makes the `.attr`-driven constructor-reordering and remapping story (see the
Peregrine CLAUDE.md) expressible as L4 passes rather than as premises.

### 4.2 Erasability

* `isArity T` transfers verbatim: `∀ …, Sort u` after `whnf`/ζ.
* `Σ ; Γ ⊢ T : tProp` becomes `T : Prop`, i.e. `Sort 0`. Lean's `Prop` is proof-irrelevant
  **definitionally**, which is *stronger* than Coq's Prop — good for the box rule (any two proofs are
  interchangeable, so erasing them to a common `□` is semantically justified more easily).
* **Lean has no `Prop ≤ Type` cumulativity at all.** There is no sort subtyping in Lean's defeq. So
  the paper's `prop_sub_type := false` requirement is *automatically satisfied*, and the whole
  `CumulProp` / "sort quality equivalence" apparatus of §7.2 is unnecessary in the Lean setting.
* What *is* still needed for oracle soundness is the Lean analogue of the paper's unique-sort-quality
  principle: **if `Γ ⊢ t : T` and `Γ ⊢ t : T'` then `T` and `T'` are defeq, and defeq preserves
  "is a Prop" / "is an arity"**. In lean4lean that is `TrExprS.uniq` and `VEnv.IsDefEq.uniqU` — which
  is exactly the cluster the current development reports as the inherited `sorryAx` boundary
  (memory: `lean4lean-sorry-boundary`). This is the *right* place for the trust boundary: it is where
  the paper needs a metatheorem too. It should be stated once, as a named hypothesis/axiom bundle,
  not smeared.
* **`Lean.Meta.isProof` / `whnf` in `MetaM`** is the analogue of `is_erasableb`. It is not a decision
  procedure with a proved reflection lemma; the honest formulation is an *interface* in the style of
  `abs_env_struct`: an oracle with a **soundness obligation** (`isProof e = true → Erasable Γ e`) and,
  separately, a **completeness obligation** used only to show the *function* does not box too little.
  Only soundness is needed for `erases_erase`; the paper needs completeness for nothing in §7.3
  either — it needs it to *state* that `is_erasableb` reflects `isErasable`, and the hard half is the
  negative one. Split the two, and be explicit about which is discharged.

### 4.3 Environment / declarations

* Lean's `Environment` ≈ `global_env`; `ConstantInfo` (`defnInfo`, `thmInfo`, `axiomInfo`,
  `opaqueInfo`, `inductInfo`, `ctorInfo`, `recInfo`, `quotInfo`) ≈ `global_decl`.
* `erases_deps` transfers **directly and should be adopted**: the shipping `#erase` command already
  walks the dependency closure of the requested constant bottom-up. This is a place where the Lean
  frontend's actual behaviour matches the paper better than a pointwise environment erasure would.
* `abs_pop_decls` has no Lean analogue and needs none: the Lean eraser builds the output environment
  incrementally rather than pruning.
* `thmInfo` (theorems) are exactly the "constants erased to `□` but not used everywhere" the paper's
  §7.4 discussion is about; the dependency-selective definition is what keeps them out.

### 4.4 Axioms

`axiom_free Σ` as stated is **unusable in Lean**: `propext`, `Quot.sound`, `Classical.choice` appear
in the dependency closure of essentially every realistic program (this is precisely why the review
found 0/5 benchmark programs covered by the capstones' hypotheses). The correct generalisation, and
one the paper itself gestures at in §9 ("Currently, we support axioms which do not block
call-by-value evaluation"), is:

> **`erasable_axioms Σ`**: every axiom in the dependency closure is either (a) `isErasable` (its type
> is a `Prop` — true for `propext` and `Quot.sound`), so it is erased to `□` and can never be a stuck
> head in a *relevant* position; or (b) explicitly remapped by an L4 pass to a target implementation
> (this is the `Eq.rec`/`False.rec`/`@[extern]` story), with the remapping's correctness as an
> assumption of the pass, clearly labelled.

`Classical.choice` is *not* Prop-typed and *is* computationally relevant; but any program that
actually runs is `noncomputable`-free, so the condition to check is "no `Classical.choice` in the
closure of the *erased* term", which `erases_deps`-style dependency tracking gives for free. Making
this hypothesis **discharged by a decidable check on real benchmark programs** is the concrete
antidote to the "never jointly inhabited" complaint.

### 4.5 Evaluation and the first-order capstone

* The paper's capstone hypothesis is `Σ ; [] ⊢ t ⇝∗ v` with `v` irreducible, converted to `⇓` by
  `wcbv_standardization`, which needs `progress` (needs `axiom_free`) and the **normalization axiom**.
* lean4lean has no progress/canonicity/standardization theorem. Two honest options:
  1. **Mirror the paper's conditional form**: take source evaluation (or reduction-to-irreducible) as
     a *hypothesis*, exactly as `erases_correct` does, and state the capstone as "if the Lean term
     evaluates to `v`, the erased term evaluates to the erasure of `v`". This is what the paper
     proves modulo an axiom anyway.
  2. State the missing pieces as a **named, single, documented axiom bundle** in the style of §5.5's
     `normalization` — one axiom, propositional, with the paper's own justification ("if it fails
     there is a much more serious problem in the theory").
  Option 1 plus a decidable side-check on benchmarks is strictly preferable to the current situation
  of many mutually independent premises.
* `firstorder_ind` transfers verbatim to Lean inductives (parameters, indices, constructor argument
  types all headed by first-order inductives). It covers `Nat`, `Bool`, `List Nat`, `Nat × Nat`,
  binary trees — i.e. the benchmark observables. **This is the definition to adopt**, and the
  benchmark coverage claim should be `firstorder_ind`-checked mechanically.
* `firstorder_erases_deterministic`'s hypothesis `Σ ⊢ v ⇓ v` ("v is a value") should be mirrored as a
  `Value`-predicate on Lean terms, not as an ad-hoc "is a nested constructor application" statement.

### 4.6 Structural vs well-founded recursion, `let`, `mdata`, universes, literals

* **Structural recursion** in Lean surfaces as `brecOn`/`below`/recursor applications; **well-founded
  recursion** as `WellFounded.fix` plus `WellFounded.rec` (which is `Acc.rec`, an eliminator of a
  `Prop` inductive into `Type` — a *subsingleton elimination*, and hence precisely the case that λ□
  rule (2) / `optimize` exists for; §5.1 of the paper notes "while accessibility is a Prop-valued
  relation, Coq's subsingleton criterion allows" the elimination). This means: the box-case rule (2)
  is not exotic for Lean — **it is exactly what makes `WellFounded.fix` erasable and runnable**, and
  it should be first-class in the semantics from day one, with `optimize` as the pass that discharges
  it. Any design that excludes `Acc.rec` by a premise is excluding the main use case.
* **`Expr.letE`** maps to `E.tLetIn`; ζ must be in both semantics.
* **`Expr.mdata`** should be erased transparently (`erases_mdata : Erases Γ e t → Erases Γ (.mdata d e) t`)
  — this is a genuine extra rule with no PCUIC counterpart, and it is harmless because it is a
  congruence with an identity target.
* **Universes**: Lean is universe-polymorphic like PCUIC; `.const kn us ⇝E .const kn` mirrors
  `erases_tConst` exactly (levels dropped).
* **Literals**: `Expr.lit (.natVal n)` has no Fig. 16 node. Either (a) erase to the unary
  `Nat.succ`/`Nat.zero` chain the kernel means (correct, catastrophic performance), or (b) target
  MetaRocq's later `tPrim` and make literal lowering an L4 pass with its own correctness statement
  relating unary and machine `Nat`. The paper explicitly excludes primitive integers from PCUIC, so
  there is no guidance here — this is Lean-specific and must be carried as an explicitly *unverified
  or separately-verified* pass, never silently inside the eraser.
* **`Quot`**: `Quot.mk/lift/ind` are kernel primitives with no PCUIC analogue; `Quot.lift f h (Quot.mk a) ≡ f a`
  must be either in the source semantics or handled by an L4 remapping pass.

---

## 5. Requirements for the rework

Checkable conditions for "the rework follows Sozeau et al. §7".

**R1 — One target, one semantics.** λ□ is a single datatype with a single `WcbvEval` relation
containing the three box amendments (1)(2)(3), parameterized by a `WcbvFlags`-style record so that
rule (2) can be switched off. No forked target semantics; no second evaluation relation "for the
capstone".

**R2 — One source-evaluation relation.** Exactly one relation plays the role of `Σ ⊢ t ⇓ v`
(the review counted eight forks). If a fragment must be carved out temporarily, it is a *hypothesis
on the derivation*, not a different relation — and it must be a definitional restriction with an
inclusion lemma into the full one.

**R3 — The erasure relation is a congruence + `erases_box`, and nothing else.** One rule per source
constructor, targeting the same-named λ□ constructor; one non-deterministic `box` rule with a genuine
`Erasable` premise; **at most one side condition anywhere**, the `Subsingleton` condition on the
elimination rule, and it must be the real subsingleton-elimination criterion of the environment
(`elim_sort_prop_ind`'s Lean analogue: at most one constructor, all fields in `Prop`), *not* a
predicate that names the counterexamples it must exclude. In particular: no rule may be indexed by
the shipping eraser's own registry, and every index the relation carries must have a
well-formedness predicate relating it to the real `Environment`.

**R4 — Relation ⊇ graph of the function, as one lemma.** A single `erases_erase`-shaped statement
connecting the shipping eraser to the relation, quantified over all specification environments
related to the abstract/`MetaM` one. The `MetaM` oracle (`isProof`, `whnf`, `inferType`) enters as an
**interface with named obligations** in the style of `abs_env_struct`/`abs_env_prop` — squashed
connection relation, uniqueness (`abs_env_irr`), lookup as the only query — not as ad-hoc axioms
scattered per call site.

**R5 — `erases_correct` in the paper's exact shape.** Hypotheses: well-formed environment,
well-typedness of the source term, source evaluation, *some* erasure of the term, and the
environment-dependency relation. Conclusion: **existentially quantified** erasure of the value plus
target evaluation to it. No hypothesis outside this list. Nothing named "Relevant"/"Supported"/
"IotaRelevant" may appear.

**R6 — `erases_deps`, not pointwise environment erasure.** The environment relation is the
bottom-up, dependency-selective inductive predicate over the *erased* term. It should be the only
environment relation in the development.

**R7 — First-order collapse as a separate lemma.** `firstorder_ind` defined syntactically as in §7.3;
`firstorder_erases_deterministic` proved (every erasure derivation of a first-order *value* equals the
function's output); capstone obtained by composition, not by a bespoke induction.

**R8 — Capstone hypotheses must be jointly inhabited, and demonstrably so.** For each of the five
benchmark programs, produce a checked instantiation: `firstorder_ind` of the result type, the
axiom-closure condition of §4.4, well-typedness, and an actual source evaluation. If a hypothesis
cannot be discharged for any benchmark, it is the wrong hypothesis.

**R9 — Optimisations are passes, not eraser cases.** Everything Lean-specific that MetaCoq does not
do — constructor blocking, `casesOn`→`.case`, `brecOn`/`WellFounded.fix`→`.fix`, `Nat` literals,
`@[csimp]`/`@[extern]`/`Eq.rec` remapping, constructor reordering — is a λ□→λ□ pass with an
`optimize_correct`-shaped statement (`wf Σ → closed t → eval fl Σ t v → eval fl' (pass_env Σ) (pass t) (pass v)`),
and passes that are *not* proven must be listed as such in one place, exactly as Peregrine's
`extra_unsafe_transforms` are.

**R10 — Trust boundary stated once.** One documented bundle (the lean4lean unique-typing cluster, the
`MetaM` oracle obligations, any normalization/progress assumption), in the style of §5.5's single
`normalization` axiom and §1's "trusted theory base" paragraph — measured by `#print axioms` on the
capstone, and with a one-line justification of why each element is a theory-level rather than
code-level assumption. Four separate "trust bundles" is three too many.

**R11 — Compare `Erases` to MetaRocq's `erases`.** Since the output must be byte-compatible with
`peregrine-tool`'s `EAst`, the Lean `Erases` relation should come with a written, rule-by-rule
correspondence table against Fig. 18 (this document is the source for it), and any rule with no
counterpart (e.g. `mdata`, `lit`, recursor-driven rules if they survive in L1) must be justified
explicitly. The λ□ syntax used must be MetaRocq's `EAst` as `peregrine-tool` serialises it — including
whether branches carry `list name` (Fig. 18) or an arity `N` (Fig. 16).

**R12 — No changelog docstrings.** Docstrings state what an object *is*, in the style of the paper's
prose. History belongs in git.

---

## 6. Open questions

1. **Where do `.case`/`.fix`/`.construct` come from?** The recommendation in §4.1 is L4 passes over
   λ□. But the shipping `visitExpr` produces them *directly*. Either the shipping eraser is refactored
   to emit recursor applications and a pass introduces `.case`/`.fix` (clean, but changes shipping
   code — and CLAUDE.md's rule is to *report* implementation issues, not silently patch), or the
   bridge `visitExpr_refines_erases` must be proven against `L1 ; L4`-composed, i.e. the theorem
   becomes "visitExpr = optimize ∘ erase" up to the relation. Which of the two is the plan of record?
2. **`Subsingleton` for Lean.** Lean's `casesOn` for a `Prop` inductive eliminating into `Type` is
   permitted exactly under Lean's subsingleton criterion, but Lean also has `Acc.rec`, `Eq.rec`,
   `False.rec`, `Quot.ind` and `K`-like behaviours. Does lean4lean expose a predicate that *is*
   `elim_sort_prop_ind`'s analogue, or must it be defined here (and then: is that Lean kernel theory,
   which the discrimination rule sends to lean4lean)?
3. **Rule (2)'s arity.** MetaCoq's rule (2) applies to a case with exactly one branch `[(n,t)]` and
   substitutes `n` boxes. For Lean, the erased `Acc.rec`/`casesOn` application's minor premise arity
   must be recoverable from the erased term alone. In Fig. 16 the branch carries `N`; in Fig. 18 it
   carries `list name`. Which does the Peregrine `.ast` format carry, and does the semantics used here
   agree?
4. **`erases_deps` vs. `#erase`'s actual traversal.** Is the shipping command's dependency closure
   bottom-up and *identical* to what `erases_deps` would admit (in particular for mutual blocks,
   recursors, and `Quot`)? If not, which is wrong?
5. **Literals.** Is machine-`Nat` lowering to be modelled at all in this rework, or explicitly
   declared out of scope with a stated (unproven) refinement obligation? The paper gives no guidance;
   this is the largest genuinely-Lean design decision.
6. **Which λ□ is canonical here?** MetaRocq's `EAst` has drifted from Fig. 16 (`tPrim`, branch
   contexts, block-vs-applied constructors). `peregrine-tool/theories/PAst.v` + peregrine-tool's format document is the
   on-disk contract. The rework's λ□ should be pinned to *that*, with Fig. 16 as the semantic
   reference — but the block/applied constructor convention (CLAUDE.md's recurring cross-repo bug)
   must be decided once and recorded in the semantics, not per-lemma.
7. **Do we want the paper's `simple_erases_correct` at all?** MetaCoq skips it and proves only the
   `erases_deps` version. Proving the simple one first is cheap documentation value but is dead code
   by the paper's own choice.
8. **Progress/canonicity.** Is a Lean analogue of §5.6's `progress` in scope for lean4lean (kernel
   theory) or does the capstone stay in the conditional "if it evaluates" form (§4.5, option 1)?

---

## Appendix — figures in the article that the extracted text does not contain

These must be read from the Coq sources or the PDF figures if the rework needs their detail:

* **Fig. 11** — one-step weak call-by-value reduction `Σ ⊢ t ⇝wcbv t'` (PCUIC side). Rendered as an
  image; not in the text file.
* **Fig. 15** — full `abs_env_prop` property list (only the first three fields appear in the text).
* **Figs. 19–21** — full cumulativity and typing specifications (appendix; partially rendered).
* The λ□ big-step `⇓` rules themselves are **never printed** in the article (footnote 29); only the
  three amendments are. The PCUIC-side `⇓` is likewise omitted ("entirely standard to derive … we
  omit it in the article and refer the reader to the Coq code"). Anyone re-deriving the λ□ semantics
  from this paper alone is reconstructing, not transcribing — the authoritative source is
  MetaRocq's `EWcbvEval`.
