# Letouzey, *A New Extraction for Coq* (TYPES 2002) — reference analysis for the rework

Source: `references/A_New_Extraction_for_Coq.pdf` (HAL `hal-00150914`), Pierre Letouzey,
LNCS/TYPES 2002, 17 pages + 3 appendices. Read from the rendered PDF pages (the shipped
`.txt` extraction is font-garbled and must not be trusted; page numbers below are the
*paper's* numbers, PDF page = paper page + 1).

Everything quoted between the rule/definition markers is transcribed from the paper, with
only notational transliteration (`E` for the calligraphic ε, `◄` for the paper's triangle,
`→_x` for subscripted arrows). Where I could not read a glyph with certainty I say so.

---

## 1. Summary

This is the origin paper of λ□. It does three things.

1. **It fixes the target language**: `CIC□` = the CIC term syntax *plus one constant `□`*,
   **untyped**, with the same reduction rules as CIC, `□` being non-reducible — plus, later,
   two ad-hoc additions forced by the metatheory: a `□`-reduction `(□ u) →_□ □`
   (Def. 5) and a modified ι-reduction that lets `Cases` and `Fix` proceed when the
   scrutinee/guard has become `□` (Def. 8). This is exactly the λ□ that MetaCoq's `EAst`
   and Peregrine's `LBTerm` inherit, box rule included.

2. **It fixes the erasure function** `E` (Def. 3): a *pruning* function. Two source-side
   classes go to `□` — terms of sort `Prop` (logical parts) and **type schemes** (Def. 1,
   arities/type-formers) — and every other node is traversed **structurally, with the
   term's shape preserved exactly**. "Clearly, `E` is a 'pruning' function: it only
   replaces some sub-terms by `□`. In particular no modification of the structure can
   occur." Context/environment erasure is four rules (nil/def/ax/ind). Every
   structure-changing operation (η-expansion of fixpoints, removal of dummy lambdas,
   removal of singleton eliminations, `sig`-collapsing, `nat_rec` inlining) is deliberately
   **outside** the verified core and lives in §4 "Implementation Considerations".

3. **It proves correctness against a relation, not against the function.** `E` does *not*
   commute with reduction (Example 4: after β-steps the source becomes "more boxable" than
   the image records), so Letouzey introduces a *pruning invariant* `(Γ,t) ◄ (Γ₀,t₀)`
   (Def. 10) with four clauses, shows `E`'s graph is inside it (Lemma 11), and proves two
   simulation squares (Thms 12, 13) plus an observational result on first-order data
   (Thm 15). The clause structure of `◄` is the interesting part for us: it is indexed by
   *typing facts about the source* (`◄₃`: every `□` sits over a `Prop`-sorted term or a type
   scheme) and by *one well-formedness condition on the target's `Cases` nodes* (`◄₄`) —
   not by any registry produced by the extractor.

The paper also states honestly what is *not* covered: axioms are excluded outright,
strong reduction is given up in favour of weak reduction, and §4's optimizations are
unproved.

---

## 2. Formal objects

### 2.1 Source language (CIC), §3.1, p. 5

Contexts and environments are **unified**: a context is a sequence of generic objects,
each being an assumption `(x : T)`, a definition `(x := t : T)`, or an inductive
declaration `Ind_n(Γ_I := Γ_C)` where `n` is the number of parameters, `Γ_I` declares the
inductive types (e.g. `nat : Set`) and `Γ_C` the constructors (e.g. `O : nat :: (S : nat → nat)`).

Term syntax (transcribed):

```
t ::= s | x | (x : t)t | [x : t]t | [x := t]t | (t t)
    | < t > Cases t of t ... t end
    | Fix x_i {x_1/k_1 : t := t  ...  x_n/k_n : t := t}
```

`s` is a sort, either `Set`, `Prop` or `Type`. `[x : t]t` is lambda, `(x : t)t` product,
`[x := t]t` let-in. The `<t>` annotation on `Cases` gives the type of the case elimination
(the *motive*). In a fixpoint, for each `i`, `k_i` is a number expressing that the component
`x_i` expects at least `k_i` arguments, **the last one being the "guard" argument, i.e. an
inductive argument used to control the reduction of the fixpoint**. Co-fixpoints exist in
Coq but are not considered.

Typing judgement `Γ ⊢ t : T`. `t` "has sort `s` in `Γ`" iff there exists `T` with
`Γ ⊢ t : T` and `Γ ⊢ T : s`. Unicity of type and of sort **do not hold** ("an object of
sort `Prop` is at the same time of sort `Type`").

Reductions (transcribed verbatim, p. 5):

```
(beta)   ([x : X]t u) →_β t{x/u}
(delta)  c →_δ t                      if the current context Γ contains (c := t : T)
(zeta)   [x := t]u →_ζ u{x/t}
(iota)   <P> Cases C_i p_1 ... p_k u_1 ... u_n of f_1 ... f_n end →_ι f_i u_1 ... u_n
             if C_i is the i-th constructor of an inductive type with k parameters
(iota)   Let F be the declarations f_1/k_1:A_1:=t_1 ... f_n/k_n:A_n:=t_n. Then:
             (Fix f_i {F} u_1 ... u_{k_i}) →_ι (t_i{f_j/Fix f_j {F}}_∀j u_1 ... u_{k_i})
             if u_{k_i} (the "guard" argument) begins with a constructor.
```

CIC reductions are **strong** (any position, by the usual compatibility rules). *Weak*
reduction = "reductions occurring only at head positions". `→_r` abbreviates one step of
any of `→_β, →_δ, →_ι, →_ζ`.

### 2.2 Type schemes and stability, §3.1, p. 6

> **Definition 1.** *An type scheme is a well-typed term accepting at least one type of the
> form* `(x_1 : X_1)...(x_n : X_n)s` *with `s` a sort.*

"In other words, a type scheme is a term that will become a type (that is something of type
a sort) when applied to enough arguments." (`n = 0` is allowed, so types are type schemes.)

> **Lemma 2 (Stability Lemma).** *We have the following results:*
> - *(Subject Reduction) When a term `t` reduces to `u`, if `T` is a type of `t`, then it is
>   also a type of `u`. And if `s` is a sort of `t`, than it is also a sort of `u`.*
> - *Secondly, when substituting a variable in a term, type might change. But there are some
>   critical cases for which we have stability:*
>   - *if `t` has sort `Prop`, so has `t{x/u}`*
>   - *if `t` has an inductive type, so has `t{x/u}`*
>   - *if `t` is a type scheme, so is `t{x/u}`*
> - *Lastly, concerning applications, if `t` has sort `Prop`, so has `(t u)`, and if `t` is a
>   type scheme, so is `(t u)`.*

Remark following it: unlike previous extractions "we can now have an application `(t u)` of
sort `Prop` without `t` having sort `Prop`. This comes from the `Type` universe: consider
for example `([X : Type][x : X]x True)`." — i.e. **erasability is not a syntax-directed
property of the head**; it must be decided by typing at each node.

### 2.3 Target language CIC□, §3.2, p. 6

> Let `CIC□` be `CIC` plus one constant `□`. Unlike `CIC` the new `CIC□` is **untyped**.
> But the reductions in `CIC□` are exactly the same as in `CIC` with `□` being
> non-reducible.

Two later amendments to that ("exactly the same"):

> **Definition 5.** *The `□`-reduction is defined by the following rule:* `(□ u) →_□ □`

> **Definition 8 (New ι-reduction).** *The ι-reduction upon `CIC□` terms is now:*
> ```
> (iota) <P> Cases C_i p_1 ... p_k u_1 ... u_n of f_1 ... f_n end →_ι f_i u_1 ... u_n
> (iota) <P> Cases_n □ of f end →_ι f □ ... □        (n boxes)
> (iota) Let F be the declarations f_1/k_1:A_1:=t_1 ... f_n/k_n:A_n:=t_n. Then:
>            (Fix f_i {F} u_1 ... u_{k_i}) →_ι (t_i{f_j/Fix f_j {F}}_∀j u_1 ... u_{k_i})
>            if u_{k_i} is equal to □ or begins with a constructor.
> ```

The `Cases_n` annotation is introduced just above Def. 8: "If the type of `t` is a singleton
inductive type whose sole constructor expects `n` logical arguments, then
`<...>Cases t of f end` will now be noted `<...>Cases_n t of f end`. These new annotations
should be kept by the `E` function."

> **Definition 9 (Weak Reductions).** *The reductions* `→_βw, →_ιw, →_δw, →_ζw` *and*
> `→_□w` *are defined from the same base cases as* `→_β, →_ι, →_δ, →_ζ, →_□` *respectively,
> and from the following restricted compatibility rules:*
> ```
>        u →_? v                       u →_? v
>   ─────────────────            ─────────────────
>    (u t) →_? (v t)              (t u) →_? (t v)
>
>                       u →_? v
>   ────────────────────────────────────────────────────
>    <P> Cases u of ... end →_? <P> Cases v of ... end
> ```
> *And as for* `→_r`*, the full weak reduction* `→_rw` *is* `→_βw ∪ →_ιw ∪ →_δw ∪ →_ζw`*.*

Note the shape: this weak reduction is **nondeterministic** — it may reduce the function or
the argument or the scrutinee — and Letouzey says so explicitly: "this `→_rw` can be seen as
a generalization of both Objective Caml CBV strategy and Haskell CBN strategy. The last main
step toward the actual reduction strategy of these languages is to fix an evaluation order."
`□`-reduction is deliberately kept **out** of `→_rw`; it appears only as the separate
`→_□w`, and results are stated over `→*_{rw □w}` (the union, starred).

**No-axiom restriction** (p. 10, load-bearing): "from now on to the end of this paper we will
only consider contexts with no assumptions. This restriction is needed because reduction in
presence of an axiom is analog to strong reduction under a lambda. In particular we may loose
the fundamental fact that a closed inductive term will necessarily reduce to a term beginning
with a constructor."

### 2.4 The extraction function `E`, §3.2, Def. 3, p. 7

> **Definition 3.** *The extraction function `E` is defined by structural induction over any
> term `t` typable in a context `Γ`:*
>
> ```
> (□)  If t is a type scheme or has sort Prop in context Γ, then E_Γ(t) = □
> ```
> *Otherwise we proceed structurally:*
> ```
> (id)     E_Γ(x) = x
> (lam)    E_Γ([x : T]t) = [x : □]E_{Γ'}(t)             where Γ' = Γ :: (x : T)
> (let)    E_Γ([x := t]u) = [x := E_Γ(t)]E_{Γ'}(u)      where Γ' = Γ :: (x := t : T)
>                                                        and T is a type of t
> (app)    E_Γ(u v) = (E_Γ(u) E_Γ(v))
> (cases)  E_Γ(<P> Cases e of f_1 ... f_n end) =
>              <□> Cases E_Γ(e) of E_Γ(f_1) ... E_Γ(f_n) end
> (fix)    E_Γ(Fix f_i {f_1/k_1 : A_1 := t_1 ... f_n/k_n : A_n := t_n}) =
>              Fix f_i {f_1/k_1 : □ := E_{Γ'}(t_1) ... f_n/k_n : □ := E_{Γ'}(t_n)}
>              where Γ' = Γ :: (f_1 : A_1) :: ... :: (f_n : A_n)
> ```
> *And the extraction of a context is defined by:*
> ```
> (nil)  E([]) = []
> (def)  E(Γ :: (c := t : T)) = E(Γ) :: (c := E_Γ(t) : □)
> (ax)   E(Γ :: (x : T))      = E(Γ) :: (x : □)
> (ind)  E(Γ :: Ind_n(Γ_I := Γ_C)) = E(Γ) :: Ind_n(E(Γ_I) := E(Γ_C))
> ```

Observations that matter for the rework:

- The `(□)` clause is checked **first at every node**, and is the *only* source of `□`.
  It is a **two-disjunct** test: `Prop`-sorted **or** type scheme. (This is precisely
  MetaCoq's `isErasable` and the repo's `Erasable`.)
- Binder *types* are replaced by `□` (`[x : □]`), not deleted — the target is untyped, the
  annotation is vestigial. Likewise `<□>` for the motive and `f_i/k_i : □` for fixpoint types.
- **Arities are kept**: the fixpoint keeps its `k_i` guard indices; the abstraction count
  is unchanged. §4's "Removing Dummy Arguments" changes this and is *not* part of the theory.
- Constructors are not a term former here: they are variables (`x`) declared in `Γ_C`, so
  applied-vs-block constructor form is a **non-question** in the paper; `E` preserves whatever
  the source has. The block form is a later (MetaCoq) representation choice.
- The `(ind)` clause erases the *declaration* by erasing the types in `Γ_I` and `Γ_C`
  pointwise — i.e. constructor arities are preserved, no argument dropping.

### 2.5 Logical vs informative; where boxes obstruct reduction, §3.3, p. 7–8

Three (four, counting subcases) situations in which a CIC redex has a CIC□ **non-redex** as
counterpart — the complete inventory of what erasure can break:

> 1. a β-redex `([x : X]t u)` corresponding to a non-redex `(□ u')`
> 2. a ι-redex `<...>Cases e of ... end` corresponding to a non-redex `<...>Cases □ of ... end`
> 3. a fixpoint redex `(Fix f_i {...} u_1 ... u_n)` corresponding to a non-redex, either
>    (a) `(□ u'_1 ... u'_n)`
>    (b) `(Fix f_i {...} u_1 ... □)` (the "guard" argument is now a blocking `□`)

Case 1 is repaired by the `□`-reduction (Def. 5). Case 2 arises because "the CIC typing system
allows a `Cases` logical elimination to produce something informative when the elimination is
performed upon a term whose logical inductive type has either:
> 1. zero constructor (empty inductive)
> 2. one constructor whose arguments are all logical, parameters put aside (singleton inductive)"

Case 3b is "the 'guard' argument of a fixpoint can be of a logical inductive type whereas the
whole fixpoint term is informative" — the `Acc`/`Acc_rec` situation, illustrated by the `loop`
example (p. 9):

```
loop = [Ax : (Acc nat gt O)]
         Fix F {F/2 : (a : nat)(Acc nat gt a) → nat :=
                  [a : nat][b : (Acc nat gt a)](F (S a) H)}
         O Ax
E(loop) = [Ax : □]
            Fix F {F/2 : □ := [a : nat][b : □](F (S a) □)}
            O □
```
with `H = (Acc_inv a b (S a) (gt_Sn_n a))`. "If we remove the 'guard' condition here, then this
term is strongly reducible even without being applied, and gives `[Ax : □]Fix F {...} (S O) □`
and so on ..." — this is *the* reason the paper abandons strong reduction for weak reduction.

The intermediate systems `CIC⁻` / `CIC□⁻` used only in §3.3 are CIC/CIC□ restricted by:
> (i) Logical empty elimination should not produce informative terms.
> (ii) Logical singleton elimination should not produce informative terms.
> (iii) For every component `f_i` of a fixpoint, its "guard" argument should not be logical
>       when the type of `f_i` is not.

§3.4 then *removes* these restrictions: (i) is harmless ("ι-reduction upon an empty inductive
will never happen", and those `Cases` are translated to exceptions); (ii) and (iii) are paid
for by the `Cases_n`/`□`-guard clauses of Def. 8 **plus** the move to weak reduction. The
`cast` example (p. 9) shows why strong reduction plus singleton elimination is unsound in the
target (a `Cases` would be handed an `O` where a boolean is expected): "Clearly, if we forbid
reduction under lambdas, the problem disappears."

### 2.6 Logic-free types and data-types

> **Definition 6.** *A type `T` is said to be logic-free if for all closed normal term `t` of
> type `T` we have `E(t) = t`*

> **Definition 14.** *A data-type is an inductive type `D` whose constructors expect only
> arguments of type `D` or of type another data-type.*

"In practice, the logic-free data-type condition is not so restrictive. The usual data types
like `bool`, `nat`, or `Z` verify it. And anyway we can state a generalized result for any type
using an ad-hoc observational equivalence: plunged into a boolean context, `t` and `E(t)` will
compute to the same value."

### 2.7 The pruning invariant `◄`, §3.4, Def. 10, p. 11

> **Definition 10.** *Let `Γ₀` and `t₀` be a context and a term of `CIC`. Let `Γ` and `t` be a
> context and a term in `CIC□`. We say that `(Γ,t) ◄ (Γ₀,t₀)` iff:*
> - `(◄₁)` `t₀` *is well-typed in context* `Γ₀`
> - `(◄₂)` `t` *and* `t₀` *differ only at positions where* `t` *contains* `□`*, and* `Γ` *and*
>   `Γ₀` *differ only at positions where* `Γ` *contains* `□`
> - `(◄₃)` *any sub-term in* `t₀` *and* `Γ₀` *corresponding to a* `□` *in* `t` *or* `Γ` *has
>   sort* `Prop` *or is a type scheme*
> - `(◄₄)` *all* `Cases` *(or* `Cases_n`*) in* `t` *and* `Γ` *are upon inductive types that are
>   either informative or logical singleton or empty.*

This is the paper's central design decision and the one the rework should copy: the correctness
statement is about a **relation between a source configuration and a target configuration**,
whose clauses are (1) source well-typedness, (2) a purely structural "same tree modulo boxes",
(3) a *typing* justification for every box, and (4) a *well-formedness* side condition on the
target's case nodes. Nothing in `◄` mentions the extractor, its state, or any table it built.

Why a relation at all, in Letouzey's own words (p. 10): "Studying `E` directly is not a good
choice, since `E` does not behave well with respect to reduction: if `t →_r u`, we might not
have `E(t) →_r E(u)`, see for example term `t` of Ex. 4."

> **Example 4.**
> ```
> t    = ([X : Type][f : nat → X][g : X → nat](g (f O))  Prop  [_ : nat]True)
> E(t) = ([X : □][f : □][g : □](g (f O))  □  □)  →*_β  [g : □](g (□ O))
> ```
Here the *source* reduct has an informative `(f O)` whose `X` instantiates to `Prop`, so the
reduct's erasure would box more than the reduct of the erasure does; `◄` tolerates the
mismatch, `E` cannot.

---

## 3. Theorems and proof structure

### Lemma 11 (`erases_erase`: the function's graph is inside the relation)

> **Lemma 11.** *If `t` is a `CIC` term typable in context `Γ`, then*
> `(E(Γ), E_Γ(t)) ◄ (Γ, t)`.

No proof given in the paper (it is immediate by induction: `(◄₁)` is the hypothesis, `(◄₂)`
holds because `E` is pruning, `(◄₃)` is Def. 3's `(□)` clause, `(◄₄)` is CIC's elimination
rule for the `Cases` nodes present).

### Theorem 12 (target step ⇒ source steps⁺; the *reflection* / termination direction)

> **Theorem 12.** *If `(Γ,t) ◄ (Γ₀,t₀)` and `t →_rw u`, then there exists `u₀` such as
> `t₀ →_rw+ u₀` and `(Γ,u) ◄ (Γ₀,u₀)`.*
>
> ```
>        t₀ ⋯⋯ r_w+ ⋯⋯▸ u₀
>        ▼               ▼      (vertical arrows are ◄, pointing t ◄ t₀)
>        t ── r_w ─────▸ u
> ```
> *Proof.* See Appendix A.

Note the `+`: **at least one** source step per target step. That is exactly what makes
Theorem 15's termination argument work.

Proof (Appendix A, p. 16), by case on the reduction used:

- **Singleton `ι_w` step** `<...>Cases_n □ of f end →_ι (f □ ... □)`. The compatibility rules
  for `→_ιw` **combined with the no-axiom hypothesis** imply the counterpart `a₀` of the
  eliminated `□` is well-typed in an assumption-free context; since `a₀` has an inductive type
  it reduces (weakly) to `(C p_1 ... p_k v_1 ... v_n)`; `C` is the unique constructor of the
  singleton type and has exactly `n` non-parameter arguments; so `<...>Cases_n a₀ of f₀ end`
  reduces to `(f₀ v_1 ... v_n)` in **at least one** `→_rw` step. To conclude, one checks
  `(f □ ... □) ◄ (f₀ v_1 ... v_n)`, "trivial, since in particular all `v_i` are logical as
  arguments of a singleton constructor".
- **Fixpoint `ι_w` step with `□` guard.** The corresponding guard `g₀` in `t₀` has a logical
  inductive type and reduces, as above, to a term `h₀` beginning with a constructor; then the
  fixpoint reduces in `t₀`, and the results are still linked by `◄`.
- **`β_w` step.** By `(◄₂)` the β-redex in `t` has a β-redex counterpart in `t₀`; reduce it;
  `u ◄ u₀` follows from:

> **Lemma 16.** *If `a ◄ a₀` and `b ◄ b₀` then `a{x/b} ◄ a₀{x/b₀}`*
>
> *Proof.* `(◄₁)` and `(◄₂)` are clear. For `(◄₃)`: let `c₀` be the counterpart in `a₀{x/b₀}`
> of a `□` in `a{x/b}`; this `□` comes from a previous `□` either in `a` or in `b`; let `d₀`
> be its counterpart in `a₀` or `b₀`; then either `c₀ = d₀` or `c₀ = d₀{x/b₀}`; hypothesis
> `(◄₃)` on `a` and `b` gives that `d₀` is a type scheme or `Prop`-sorted; **using the
> stability Lemma 2**, `c₀` is also a type scheme or `Prop`-sorted. For `(◄₄)`: any `Cases`
> of `a{x/b}` comes from a previous `Cases` in `a` or `b`, and the inductive sub-term
> eliminated by this `Cases` cannot change of sort under substitution. ∎

- Remaining cases (`→_δw`, `→_ζw`, and the rest of `→_ιw`) are "similar to the `→_βw` case".

### Theorem 13 (source step ⇒ target step, *or* box steps; the forward simulation)

> **Theorem 13.** *Suppose that `(Γ,t) ◄ (Γ₀,t₀)` and `t₀ →_rw u₀`. Then there exists `u` such
> as `(Γ,u) ◄ (Γ₀,u₀)` and either `t →_rw u` or `t →_□w u`.*
>
> ```
>        t₀ ── r_w ────▸ u₀
>        ▼               ▼
>        t ⋯⋯ r_w|□_w* ⋯▸ u
> ```
> *Proof.* See Appendix B.

(The prose says "either `t →_rw u` or `t →_□w u`"; the *diagram* labels the bottom arrow
`r_w|□_w *`, and Appendix B's fixpoint case 3a needs "some `□`-reductions", plural, and the
second bullet needs `u = t` (zero steps). The faithful statement is therefore: `t` reduces to
`u` by **one** `→_rw` step **or** by **zero or more** `→_□w` steps.)

Proof (Appendix B, p. 17), by position of the redex `r` reduced in `t₀`:

- If `r` corresponds to a similar redex in `t`, reduce it there.
- If `r` is completely inside a sub-term of `t₀` corresponding to a `□` of `t`, take `u = t`.
- Otherwise `r` is at one of the intermediate positions of §3.3:
  - **β-redex**: the only situation is `r = ([x : X]a b)` in `t₀` corresponding to `(□ b')` in
    `t`; simulate the β-step by a `□`-step (Def. 5). *(This is case 1.)*
  - **δ- or ζ-redex**: no intermediate situation.
  - **`Cases` ι-redex**: the remaining situation is `<P>Cases e of ... end` in `t₀`
    corresponding to `<P'>Cases □ of ... end` in `t`. By `(◄₄)` this `Cases` is informative,
    empty or singleton. Informative is impossible: `e` would then have an informative
    inductive type, contradicting `(◄₂)`. Empty cannot be reduced (no constructor). So it is a
    singleton elimination, reducible by the **new ι-rule** of Def. 8. *(This is where `(◄₄)`
    earns its place — it is the only clause used to exclude a stuck target.)*
  - **`Fix` ι-redex**: two sub-cases. Case 3a (the `Fix` has disappeared from `t` but not all
    the arguments): simulate via some `□`-reductions. Case 3b (the `Fix` is there but the
    guard is `□`): reduce via the new fixpoint ι-rule of Def. 8.

### Theorem 7 (the `CIC⁻` warm-up, strong reduction)

> **Theorem 7.** *Let `t` be a well-typed closed `CIC⁻` term whose type `T` is logic-free.
> Then all reductions of `E(t)` terminate on the `CIC⁻` normal form of `t`.*

Not proved in the paper ("somehow less important than incoming Theorem 15, whereas the proofs
of these two theorems are similar"). Notable: under Restrictions (i)–(iii), **no `□`-reduction
is needed**, and *strong* reduction is sound. Restrictions removed ⇒ weak reduction + `□` rules.

### Theorem 15 (the observational result — the ancestor of `erase_correct_firstorder`)

> **Theorem 15.** *Let `t` be a well-typed closed `CIC` term whose type `T` is a logic-free
> data-type. Then all derivations of `E(t)` via `→*_{rw □w}` terminate on the `CIC` normal
> form of `t`.*

Proof (Appendix C, p. 17):

1. First, `a ◄ b` and `a →_□ c` imply `c ◄ b`. (`□`-steps refine the invariant.)
2. Given a derivation of `E(t)` via `→*_{rw □w}`, build an associated `r_w`-derivation of `t`
   by using **alternately Theorem 12** (for `r_w` steps of the target) **or step 1** (for `□_w`
   steps). Each `r_w` step of `E(t)` costs **at least one** `r_w` step of `t`. Since CIC's
   `r_w`-reductions are always finite (strong normalization of the source), the target
   derivation contains finitely many `r_w` steps; and it cannot contain infinitely many
   consecutive `□_w` steps "since they decrease the size of the term". Hence every derivation
   of `E(t)` **terminates** (this is the whole termination argument: a lexicographic descent on
   (source reduction sequence, target size)).
3. Let `u` be such a normal term reached from `E(t)`, and `u₀` the associated CIC term reached
   from `t`. **Because of the definition of a data-type**, `u₀` can still be `r_w`-reduced,
   zero or more times, toward the CIC normal form `t₀` of `t`. By Theorem 13, `u` reduces
   accordingly via `r_w|□_w*` — except that `u` is already normal, so nothing is done — and we
   get `u ◄ t₀`. By the **logic-free** hypothesis `E(t₀) = t₀`, i.e. `t₀` has no `Prop`-sorted
   and no type-scheme sub-terms. So there cannot exist any `□` in `u`, and finally `u = t₀`. ∎

So the final statement is genuinely *observational*: the extracted program, under **any**
weak strategy (CBV, CBN, or any interleaving), terminates, and its normal form is **literally
equal** to the source's normal form — not merely related. The two hypotheses doing the work
are `logic-free` (kills residual boxes in the answer) and `data-type` (guarantees the
value is reachable by *weak* reduction alone).

### §4 — implementation, explicitly *outside* the proved core

- **Removing singleton eliminations.** The `Cases_n` device is theoretical; in practice all
  singleton `Cases_n` are eliminated *during extraction* via the more general rule
  `<...>Cases_n e of f end → (f □ ... □)`, **used even under lambdas**. Justification given:
  "We can prove that type error possibilities showed in Sect. 3.4 are avoided because all
  other reductions are still used in a weak way."
- **Implementing `□`.** After that removal, "`□` now never comes in head position during lazy
  evaluation of an informative term", so Haskell can implement `□` as an error. OCaml is
  strict, so `(□ u) →_□ □` may really be needed: a unit value is inappropriate; use
  `let rec x = Obj.magic □` (`Obj.magic` needed because the term is not well-typed). "Gladly,
  most of the time the type of the sub-term replaced by `□` shows it could be applied only to
  a limited number of arguments. Then a term like `fun _ ... _ -> ()` can be used."
- **Implementing fixpoints.** Two mismatches with the theoretical weak fixpoint ι-rule: the
  real reduction has no control of the argument number — emulated by translating a component
  `f/n` to a function with at least `n` arguments, **η-expanding if necessary** (`Fix f {f/1 : A := t}`
  gives `let rec f x = (E(t) x)` if `t` does not begin with a lambda), so that an
  under-applied fixpoint stays blocked; and there is no control on the guard — but OCaml's
  strategy evaluates the guard to a value first, and "the only values possible for inductive
  terms begin with a constructor"; in Haskell the guard "will evaluate necessarily to a
  constructor as soon as it is used".
- **Removing dummy arguments.** `E` preserves arity, so `E(f) : E(A) → □ → E(B)`. The
  implementation removes external dummy lambdas from constant bodies, "always leave[s] at least
  one lambda to protect against undue evaluation and `False_rec` problem", and compensates at
  call sites: `(f a p)` becomes `(f E(a))`, and a partial `(f a)` becomes `fun _ -> (f E(a))`.
- **Code optimizations.** Collapse `sig`-like inductives (one constructor, one informative
  argument) to the identity; inline functions that may not need all arguments in a strict
  language (typically `nat_rec`); simplify `<bool>Cases e of true true end → true` (such terms
  "may appear in proofs, when the logical part of the proof has needed such an elimination").
- Implementation size: ~3,000 lines OCaml in Coq 7.3 `contrib/extraction` — **900 lines for the
  theoretical core and 700 for the optimizations**.

### §2 — the design constraints that produced `□` (worth keeping in mind)

- Removing logical *arguments* outright changes evaluation order: `(f t)` and `(f t p)` would
  get the same extraction and both behave like the latter; and with `False_rec` translated to
  an exception, `(f O)` (legal in Coq only because the second argument `O ≠ O` is unprovable)
  would *raise* after extraction. "Our new extraction solve this problem by leaving some dummy
  abstractions (`fun _ -> ...`) when needed."
- Hybrid terms like `if b then nat else True` are well-typed in `Type` and are neither purely
  logical nor purely informative; the old extraction refused sort `Type` outright, "this
  drastic restriction allows a complete elimination of logical parts". The new one instead uses
  "a dummy constant (noted `□` in this paper) to fill all logical places that remains, like the
  `True` place above. Our approach is here quite similar to 'pruning' methods."
- The `Prop`/`Set` split is **declarative, by the user**, not inferred: "our extraction relies
  on a declarative distinction made by the user"; "although we do not eliminate informative dead
  code, we can simplify parts that do not satisfy the dead code criterion (see in particular the
  logical singleton elimination)".

---

## 4. Lean-specific adaptations

1. **The `(□)` clause transfers verbatim, and it is already what the repo has.** Lean's
   erasability predicate must be exactly Letouzey's disjunction: *the term is `Prop`-sorted*
   (a proof) **or** *the term is a type scheme* (Def. 1 — in Lean: its type is an arity
   `∀ …, Sort u`, i.e. `isTypeFormer`/`isArity`). The repo's `Erasable env … ve` = "proof ∨
   type-former" is the right notion; the rework must keep the two disjuncts separate in the
   proofs, because Lemma 2's stability facts are proved separately for them.

2. **Lemma 2 is the load-bearing lemma and must exist on the Lean side.** Concretely the
   rework needs: subject reduction (from lean4lean), and closure of "is `Prop`-sorted" and "is
   a type scheme" under (a) substitution/instantiation and (b) application. Lean gives (a) via
   `TrExprS.instN`/`inst` plus `HasType` substitution, and (b) needs a small lemma about
   arities. Without it, Lemma 16 (`◄` closed under substitution) — hence the whole β case — is
   unavailable. This is the honest replacement for ad-hoc premises: it is a *provable* lemma,
   not a hypothesis.

3. **Lean has no `Fix` with a guard index; it has recursors and `WellFounded.fix`.** Letouzey's
   case 3b (blocking `□` guard) reappears in Lean as: `Acc.rec`/`WellFounded.fix` applied to a
   boxed accessibility proof, and `Eq.rec`/`False.elim` applied to boxed proofs. λ□'s `tFix`
   has a *recursive argument index* and MetaCoq's `EWcbvEval` requires that argument to be a
   constructor block — so the eraser must never place a boxed argument at the guard position.
   Letouzey's answer (Def. 8's third clause: guard "equal to `□` or begins with a constructor")
   is *not* available in MetaRocq's λ□; the modern replacement is `optimize`/`Erasure`'s
   case-on-prop and the requirement that fixpoints be produced only from genuinely structural
   Lean recursion. **The rework must state which of the two it does, and prove it.**

4. **Lean's subsingleton elimination = Letouzey's cases 1 and 2, exactly.** Lean permits large
   elimination from a `Prop` inductive iff it is empty (`False`, `Empty`-like), or has one
   constructor all of whose fields are `Prop`s (plus `Eq`, `HEq`, `Acc`, `And`, `Iff`, …).
   That is verbatim Letouzey's "zero constructor (empty inductive)" and "one constructor whose
   arguments are all logical, parameters put aside". Hence `(◄₄)` in Lean reads: *every
   `.casesOn`/`.rec` node in the target is on an inductive that is informative, or a
   `Prop`-singleton, or `Prop`-empty* — and this is **derivable from Lean's kernel elimination
   rule**, i.e. it need not be a premise; it should be a lemma over the erased environment.

5. **The `Cases_n □ → f □ … □` rule versus MetaRocq's λ□.** MetaRocq's `EWcbvEval` has
   `eval_iota_sing`/the `optimize` pass for exactly this (case on a box in a `Prop`-singleton
   inductive reduces to the single branch applied to boxes), and `eval_box` for `(□ u) → □`.
   The repo already pins block-mode/`appliedFlags` variants of `WcbvEval`. Requirement: the
   `□`-application rule and the singleton-case rule must both be *present in the one semantics*
   the rework uses — they are not optional; Theorems 13 and 15 are false without them.

6. **`Prop` in Lean is definitionally proof-irrelevant**, which makes `(◄₃)` cheaper than in
   Coq: any two proofs of the same `Prop` are already equal, so "the value erases more than the
   term" (Ex. 4, and §7.3's `(1,□)` example in the J.ACM paper) is handled by defeq rather than
   by an extra argument. But Lean's `Type`/`Prop` distinction is **not** the `Set`/`Prop`
   distinction: Lean has no `Set`, and a Lean `Type u` term whose type is an arity is a type
   scheme regardless of universe. Type-scheme detection must not be universe-sensitive.

7. **No-axiom restriction ⇒ a "computable environment" restriction in Lean.** Letouzey forbids
   assumptions in the context because a closed inductive term must reduce to a constructor.
   Lean's analogue: `Classical.choice` is an *informative* axiom (`Nonempty α → α`) and breaks
   canonicity; `propext` and `Quot.sound` are `Prop`-valued and harmless; `Quot.mk/lift/ind`
   compute and need their own ι-rule. The rework's closed-term hypothesis must be stated as
   "the environment contains no informative axiom / the term is `noncomputable`-free", and this
   is *checkable* rather than a bespoke premise.

8. **Constructors: applied vs block.** A non-issue for Letouzey (constructors are context
   variables and `E` preserves the spine), and a real issue for Peregrine (Lean emits applied
   form, CertiCoq wants blocks). Consequence: the *pruning* theorem should be proved for the
   form the eraser actually emits (applied), and block-ification treated as a separate
   transformation with its own correctness — mirroring the paper's split between the 900-line
   core and the 700-line optimizations.

9. **What §4 says about arity/dummy arguments applies directly to the Lean frontend's argmasks.**
   Letouzey removes dummy lambdas *only* in the implementation, and compensates at every call
   site, and always leaves one lambda. The Lean frontend's `argmask`-driven argument dropping is
   the same optimization — and the paper is clear that this is **not covered by Theorems
   12/13/15**. So: either the rework proves `E` in the arity-preserving form and treats the mask
   as a post-pass, or it must prove the mask-preserving simulation itself. The current
   relation's "exact when the argmask is all-`keep`" caveats are a symptom of having merged the
   two layers.

10. **Literals and machine `Nat`.** Not in the paper. Under Def. 14 a machine integer type is
    not a data-type built from constructors, so Theorem 15's conclusion (`u = t₀` syntactically)
    does not transfer; a remapped `Nat` needs a *separate* observational statement (a refinement
    between the peano tower and the machine value), not a premise.

---

## 5. Requirements for the rework

R1. **One erasure function, pruning-only.** Define `E` (or its Lean equivalent as the shipping
    eraser's model) so that it *only* replaces sub-terms by `□`: same tree, same arities, same
    number of binders, same spine lengths. Any structural change (block constructors, argmasks,
    η-expansion, casesOn→case, singleton removal) is a **separate pass** with a separate
    theorem, exactly as §4 is separate from §3.

R2. **One box criterion, two disjuncts, decided by typing at every node**: `Prop`-sorted **or**
    type scheme (Def. 1). Nothing else may produce `□`. The criterion must not be head-directed
    (see the `([X : Type][x : X]x True)` remark).

R3. **A `◄`-style invariant, indexed by typing facts only.** The correctness relation must have
    Def. 10's four clauses and nothing else: source well-typedness, "same tree modulo boxes",
    "every box is justified by `Prop`-sort or type-scheme-hood of its source counterpart", and a
    well-formedness condition on case nodes. **No column of the eraser's registry may appear in
    it.** Registry facts, if needed, belong in the *bridge* from the shipping function to the
    relation, not in the relation.

R4. **`(◄₄)` must be present in some form and must be discharged, not assumed.** It is the sole
    clause that rules out a stuck target in the `Cases`-on-`□` case (Appendix B). In Lean it
    should be *derived* from the kernel's subsingleton-elimination rule over a well-formed
    environment — i.e. it becomes the well-formedness predicate the review found missing.

R5. **Prove Lemma 11 (`erases_erase`).** The shipping eraser's graph must be shown to be inside
    the relation, for *all* typable terms — no `Supported` fragment carve-out at the statement
    level if avoidable; if a fragment is needed, it must be a syntactic, decidable predicate on
    the input, and the fragment's inhabitation must be exhibited on real programs.

R6. **Prove Lemma 16 (substitution) from a Lean Stability Lemma (Lemma 2), not from premises.**
    `a ◄ a₀ → b ◄ b₀ → a{x/b} ◄ a₀{x/b₀}`. This is the pivot of the β case and must be a
    theorem.

R7. **Prove both squares, in both directions.**
    - Thm 12: a target step is matched by **one or more** source steps (needed for termination
      transfer — the `+` is essential).
    - Thm 13: a source step is matched by **one target step or zero-or-more box steps**.
    Only having the forward one (as the current `erases_correct` does) is not enough for the
    observational theorem.

R8. **One source evaluation relation and one target evaluation relation.** Letouzey has exactly
    `→_rw` (nondeterministic weak, generalizing CBV and CBN) on the source, and
    `→_rw ∪ →_□w` on the target. The rework must not fork the source relation per feature; if a
    fragment is unavailable upstream, the fragment is a *restriction of the one relation*, not a
    new relation.

R9. **The target semantics must contain the box rules.** `(□ u) → □` (Def. 5) and the
    `Prop`-singleton case rule (Def. 8, clause 2), and the fixpoint clause must be reconciled
    with λ□'s constructor-block guard (see adaptation 3). These are not optional extras: Thm 13's
    β and `Cases` cases depend on them.

R10. **State the terminal theorem observationally, on a logic-free data-type.** Target statement
     (Lean shape of Thm 15): *for a closed, well-typed Lean term `t` whose type is a logic-free
     data-type in an informative-axiom-free environment, every `→*_{rw □w}` derivation of the
     erased term terminates, and its normal form is the erasure-image of `t`'s value — with no
     residual `□`.* The fallback for non-logic-free types is the paper's boolean-context
     observational equivalence, which should be stated too.

R11. **The termination argument must be reproduced**, not assumed: source strong normalization
     (from lean4lean) + "each target `r_w` step costs ≥ 1 source step" (Thm 12) + "`□` steps
     decrease term size". This is what turns a simulation into a *total-correctness*
     observational result, and it is cheap.

R12. **Hypotheses must be jointly inhabited on the benchmark programs.** Letouzey's hypotheses
     are `closed`, `well-typed`, `logic-free data-type`, `axiom-free context` — all four
     checkable by inspection on `bool`, `nat`, `Z`. The rework's analogues must be equally
     checkable, and the paper's own standard (a benchmark suite of >6,000 lines of extracted
     code, §4) is the standard to meet: at least the five benchmark programs must satisfy the
     capstone's hypotheses, demonstrably.

R13. **Separate the environment erasure and prove it by the four context rules** (`nil`, `def`,
     `ax`, `ind`), giving a global-environment statement (`erases_global`) that the term-level
     theorem is *not* conditioned on as a free parameter — Letouzey's `E(Γ)` is a definition,
     not a hypothesis about an unknown `E`.

R14. **Document what is out of the core, as §4 does.** Machine `Nat`, `@[extern]`, `csimp`,
     argmasks, block constructors, dummy-argument removal: each gets a one-line statement of
     what it changes and whether it is proved. The paper's honesty about its own 700
     unverified lines is the model.

---

## 6. Open questions

Q1. **Thm 13's box branch: one step or many?** The prose says "either `t →_rw u` or `t →_□w u`",
    the diagram says `r_w|□_w *`, and Appendix B's fixpoint case 3a needs several `□`-steps while
    its second bullet needs zero. Take the starred reading; flag if any Lean statement is
    sensitive to the difference.

Q2. **Which λ□ fixpoint discipline does the rework adopt?** Letouzey's Def. 8 lets a `□` guard
    fire the fixpoint; MetaRocq's `EWcbvEval` requires a constructor block. Under the latter,
    what is the Lean-side argument that a boxed argument never lands at the guard index
    (`Acc.rec`, `WellFounded.fix`, `Eq.rec`)? This is Letouzey's case 3b and it is not optional.

Q3. **Is Lean's `Quot` a "data-type" (Def. 14)?** `Quot.mk` is a constructor-like former with an
    ι-rule for `Quot.lift`; `Quot.sound` is `Prop`-valued. Does the observational theorem's
    "closed inductive term reduces to a constructor" premise survive quotients?

Q4. **Does `Classical.choice` need the no-axiom restriction to be strengthened, or does Lean's
    `noncomputable` marker already discharge it?** Letouzey forbids *all* assumptions "for
    simplicity"; Lean can afford a finer criterion.

Q5. **Where does the Peregrine middle-end's own box/lazy-force pass sit relative to Def. 5?**
    §4's `let rec x = Obj.magic □` and `fun _ … _ -> ()` are the OCaml realizations of `□`;
    peregrine-tool's `extra_unsafe_transforms` (admitted obligations) appear to be the modern
    descendants. The frontend's theorem should say explicitly which `□` behaviour it assumes of
    the backend.

Q6. **Type schemes in Lean with universe polymorphism**: is "accepts at least one type of the
    form `∀ x₁ … xₙ, Sort u`" decidable at erasure time for a `Lean.Expr` in a `VLCtx`, and is
    it stable under the level substitution the eraser performs? Lemma 2's third bullet is stated
    for term substitution only.

Q7. **Def. 6 (logic-free) is stated over *closed normal terms of type `T`*, i.e. it is a
    semantic property of a type.** What is the Lean-side decision procedure, and is
    "first-order value" (the current capstones' notion) equivalent to "logic-free data-type",
    stronger, or weaker? This should be settled before reusing the name.
