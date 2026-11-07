import EraseProof.Final
import EraseProof.Simulation.Ind

/-!
# The final theorem on first-order values

On a first-order value (`FirstOrderValue`: a tree of saturated constructor applications of
inductives whose declared sort is never zero, with leaves that λ□ erases to `□`) the λ□ value
of the final theorem is determined: it is the value's structural erasure `foErase`
(`erase_correct_firstorder`). `Erases.firstOrder` shows that an erasure of a first-order value that
is a λ□ evaluation result is its structural erasure: `□` is excluded on the constructor nodes
(`SimInd.ctor_not_erasable`, through `IsErasable.ctor_not`), `Erases.ctor_inv` fixes their shape,
and the leaves erase to `□` (`Erases.ctorProp_box`, `Erases.atomSpine_box`).
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

/-- A first-order value of `σ`.
* `ctor`: a constructor of an inductive whose declared type is an arity with a sort that is never
  zero, applied to exactly its parameters and fields, all of them first-order values. The sort test
  is on the declaration (as `Erases.proj` and the fragment test read it), so a universe-polymorphic
  inductive in `Sort u`, whose instances at `u := 0` are proofs, is not first-order.
* `proof`: a constructor of an inductive declared in `Prop` (`EvalEnv.propInd`), applied to its
  parameters and fields, which are arbitrary: a proof field.
* `atom`: an atom spine (an inductive type or other type former, or a theorem, axiom or opaque
  proof of an evident proposition, applied to arguments): a type parameter or a proof field.
Reference: `firstorder_value` (`MR P/PCUICFirstorder.v:115`), which asks every argument, parameters
included, to be a first-order value and the inductive not to be propositional. MetaRocq's
first-order inductives have no type parameters and no proof fields (`firstorder_con`,
`MR P/PCUICFirstorder.v:52`); `proof` and `atom` admit them, as leaves erased to `□` (DV-27). -/
inductive FirstOrderValue (σ : EvalEnv) : Expr → Prop
  | ctor {c : Name} {us : List Level} {as : List Expr} {cv : ConstructorVal} {iv : InductiveVal}
      {n : Nat} {u : Level} :
      findDecl σ.decls c = some (.ctorInfo cv) →
      findDecl σ.decls cv.induct = some (.inductInfo iv) →
      arityShape iv.type = some (n, u) → u.isNeverZero = true →
      as.length = cv.numParams + cv.numFields → (∀ a ∈ as, FirstOrderValue σ a) →
      FirstOrderValue σ (mkAppN (.const c us) as.toArray)
  | proof {c : Name} {us : List Level} {as : List Expr} {cv : ConstructorVal} :
      findDecl σ.decls c = some (.ctorInfo cv) → σ.propInd cv.induct = true →
      as.length = cv.numParams + cv.numFields →
      FirstOrderValue σ (mkAppN (.const c us) as.toArray)
  | atom {e : Expr} : AtomSpine σ e → FirstOrderValue σ e

/-- The structural erasure of a value, with the erasures `acc` of the arguments already peeled
off its spine: a constructor of an inductive not declared in `Prop` is the λ□ constructor of its
block (`IndIdOf`) applied to the erased arguments, parameters included (DV-23); everything else is
`□`. Reference: `compile_value_erase` (`MR E/ErasureFunctionProperties.v:2860`), with
`erase` on the constructor (`MR E/ErasureFunction.v:1014`). -/
def foErase (σ : EvalEnv) : Expr → List LBTerm → LBTerm
  | .app f a, acc => foErase σ f (foErase σ a [] :: acc)
  | .const c _, acc =>
    match findDecl σ.decls c with
    | some (.ctorInfo cv) =>
      if σ.propInd cv.induct then .box
      else match IndIdOf σ cv.induct with
        | some iid => mkApps (.construct iid cv.cidx []) acc
        | none => .box
    | _ => .box
  | _, _ => .box

/-- The structural erasure of a spine erases its arguments. -/
theorem foErase_foldl (σ : EvalEnv) :
    ∀ (as : List Expr) (f : Expr) (acc : List LBTerm),
      foErase σ (as.foldl .app f) acc = foErase σ f (as.map (foErase σ · []) ++ acc)
  | [], _, _ => rfl
  | a :: as, f, acc => by
    rw [List.foldl_cons, foErase_foldl σ as (.app f a) acc, List.map_cons, foErase]
    rfl

/-- The structural erasure of an atom spine is `□`. -/
theorem foErase_atomSpine {σ : EvalEnv} {e : Expr} (h : AtomSpine σ e) :
    ∀ acc, foErase σ e acc = .box := by
  induction h with
  | @const c us ha =>
    intro acc
    unfold EvalEnv.isAtom at ha
    cases hc : findDecl σ.decls c with
    | none => rw [hc] at ha; cases ha
    | some ci =>
      rw [hc] at ha
      cases ci <;> first
        | (simp [OwnRules] at ha; done)
        | (rw [foErase, hc])
  | app _ ih => intro acc; rw [foErase]; exact ih _

/-- An erasure of a first-order value that is a λ□ evaluation result is the value's structural
erasure. Reference: `firstorder_erases_deterministic` (`MR E/ErasureFunctionProperties.v:2079`),
on the relation instead of the erasure function. -/
theorem Erases.firstOrder {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}
    (henv : ProgEnv P ζ E B) (hE : Metalean.EnvWF E) (hsub : SubEnv σ.decls P) {v : Expr}
    (hv : FirstOrderValue σ v) :
    ∀ {s vb : LBTerm}, Erases E B lps σ .nil [] v vb → LBEval defaultFlags lenv s vb →
      vb = foErase σ v [] := by
  induction hv with
  | @ctor c us as cv iv n u hc hiv har hnz hlen _ ih =>
    intro s vb h hev
    rcases Erases.ctor_inv hc (Nat.le_of_eq hlen.symm) h with ⟨-, hb⟩ | ⟨iid, as', hid, rfl, hlen', hall⟩
    · exact absurd hb (SimInd.ctor_not_erasable henv hE hsub hiv har hnz hc hlen)
    have hprop : σ.propInd cv.induct = false := by
      cases hz : EvidentZero u
      · simp only [EvalEnv.propInd, hiv, har, hz]
      · rw [SimInd.isNeverZero_of_evidentZero hz] at hnz; cases hnz
    have hargs : as' = as.map (foErase σ · []) := by
      apply List.ext_getElem (by rw [List.length_map, hlen'])
      intro i h1 h2
      have ha : as[i]? = some as[i] := List.getElem?_eq_getElem (by rw [hlen']; exact h1)
      have ha' : as'[i]? = some as'[i] := List.getElem?_eq_getElem h1
      rw [List.getElem_map]
      exact ih _ (List.getElem_mem _) (hall i _ _ ha ha')
        (SimInd.construct_args hev _ _ _ rfl _ (List.getElem_mem h1))
    rw [mkAppN_toArray, foErase_foldl, List.append_nil, foErase, hc]
    simp only [hprop, hid, Bool.false_eq_true, ite_false]
    rw [hargs]
  | @proof c us as cv hc hp hlen =>
    intro s vb h _
    rw [Erases.ctorProp_box hc (PropInductive.of_propInd henv hE hsub hp)
      (Nat.le_of_eq hlen.symm) h, mkAppN_toArray, foErase_foldl, foErase, hc]
    simp only [hp, ite_true]
  | atom hsp =>
    intro s vb h hev
    rw [Erases.atomSpine_box hsp h hev, foErase_atomSpine hsp]

/-- The final theorem on first-order values: under the hypotheses of `erase_correct`, if the value
`v` is a first-order value, the main term of the emitted program evaluates in λ□ to the structural
erasure of `v`. Reference: `erase_correct_strong` (`MR E/ErasureFunctionProperties.v:2269`). -/
theorem erase_correct_firstorder {P decls : List ConstantInfo} {ζ : Metalean.Sigs}
    {E : Metalean.Env ζ} {B : Binds ζ} {view : EnvView} {cfg : ErasureConfig} {lps : List Name}
    {e v : Expr} {t : Metalean.Expr ζ lps.length 0} {p : Program} {inl : List Kername}
    (henv : ProgEnv P ζ E B) (hwf : Metalean.EnvWF E) (hview : ViewAgrees view P)
    (he : TrM E B lps .nil [] e t) (hty : ∃ T, E[.nil] ⊢ t : T)
    (hfrag : collectDeps view cfg e = .ok decls) (hrun : eraseEntry view cfg e = pure (p, inl))
    (hev : SrcEval (evalEnvOf view cfg P) e v) (hfo : FirstOrderValue (evalEnvOf view cfg P) v) :
    ∃ lenv tb, p = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg P) v []) := by
  obtain ⟨lenv, tb, vb, hp, hv, hlb, -⟩ := erase_correct henv hwf hview he hty hfrag hrun hev
  have hsub : SubEnv (evalEnvOf view cfg P).decls P := fun _ => CollectSub.findDecl_of_view hview
  rw [← Erases.firstOrder henv hwf hsub hfo hv hlb]
  exact ⟨lenv, tb, hp, hlb⟩

end EraseProof
