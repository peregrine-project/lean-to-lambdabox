import EraseProof.Core.Assemble
import EraseProof.Core.Glue
import EraseProof.Core.CollectSpec
import EraseProof.Oracle.Det
import EraseProof.Semantics.Sound
import EraseProof.Simulation.Main

/-!
# The final theorem

`erase_correct` composes, over the closure `decls` the fragment test returns:

1. `eraseEntry_pure`: the entry point's result is the pure path's result on `decls`;
2. `collectDeps_sub`, `collectDeps_spec`, `coreEnv_of`: `decls` is part of the program, with
   injective kernames and λ□ block names, syntactic arities, and the shape facts of an accepted
   program;
3. `erasePure_erases`: the pure path's output erases the marked input, with erased
   dependencies, in a closed λ□ environment, without certificates;
4. `erases_correct`: the main term evaluates in λ□ to an erasure of the source value;
5. `srcEval_sound`: the source value means what the input means;
6. `Erases.toCert`, `ErasesDeps.toCert`: the erasure of the main term and of the bodies is
   certified, the marks of the input by `hcert`'s second conjunct, the markings of the values the
   traversal erases by its third, which is every marking of them (`markOf_det`).

Adapted from `ML-V Final.lean`, with `srcEval_sound` in place of `SrcEval.defeq` and the
certified conjuncts.
-/

open Lean Erasure

namespace EraseProof

namespace Final

/-- `MarksCert` of a left-nested application: of the head and of each argument. Reference: none. -/
theorem marksCert_foldl {env : ConLeche.Env} {Γ : List CtxBinder} :
    ∀ {as : List Expr} {f : Expr},
      MarksCert env Γ (as.foldl .app f) ↔ MarksCert env Γ f ∧ ∀ a ∈ as, MarksCert env Γ a
  | [], f => by simp
  | a :: as, f => by
    rw [List.foldl_cons, marksCert_foldl]
    simp only [MarksCert, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- The marks of an argument of a spine are certified if those of the spine are. Reference:
none. -/
theorem marksCert_arg {env : ConLeche.Env} {Γ : List CtxBinder} {f a : Expr} {as : List Expr}
    (hm : MarksCert env Γ (mkAppN f as.toArray)) (ha : a ∈ as) : MarksCert env Γ a :=
  ((mkAppN_toArray f as ▸ marksCert_foldl).1 hm).2 a ha

/-- A proof certificate is a certificate: `CLVerdict`'s proof disjunct. Reference: none
(DV-32). -/
theorem CLCertProof.cert {env : ConLeche.Env} {Γ : List CtxBinder} {s : Expr}
    (h : CLCertProof env Γ s) : CLCert env Γ s := by
  obtain ⟨c, d, c', T₀, T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨c, d, c', T₀, T, h1, h2, h3, h4, .inr h5⟩

/-- An erasure without certificates is an erasure with con-leche's certificates if every mark of
the term is certified in the context of its enclosing binders (`MarksCert`): the `box` rule asks
`CLCert` of an `erase` mark, and `casesReduced` asks it of the discriminant of a `reduced` mark,
which `MarksCert` certifies as a proof; the contexts of `MarksCert` are those of `Erases`.
Reference: none (DV-32). -/
theorem Erases.toCert {env : ConLeche.Env} {σ : EvalEnv} {Γ : List CtxBinder} {e : Expr}
    {t : LBTerm} (h : Erases noCert σ Γ e t) (hm : MarksCert env Γ e) :
    Erases (CLCert env) σ Γ e t :=
  Erases.rec (motive_1 := fun Γ e t _ => MarksCert env Γ e → Erases (CLCert env) σ Γ e t)
    (motive_2 := fun Γ k e br _ => MarksCert env Γ e → ErasesAlt (CLCert env) σ Γ k e br)
    (fun _ => .bvar) (fun _ => .fvar) (fun _ ih hm => .lam (ih hm)) (fun _ ih hm => .etaLam (ih hm))
    (fun _ _ ihv ihb hm => .letE (ihv hm.1) (ihb hm.2))
    (fun hns _ _ ihf iha hm => .app hns (ihf hm.1) (iha hm.2))
    (fun h1 h2 h3 _ => .const h1 h2 h3)
    (fun h1 h2 h3 h4 h5 _ ih hm => .ctor h1 h2 h3 h4 h5 fun i a a' x y =>
      ih i a a' x y (marksCert_arg hm (List.mem_of_getElem? x)))
    (fun h1 h2 h3 h4 _ h6 h7 _ h9 _ ihm iha ihe hm => .cases h1 h2 h3 h4
      (ihm (marksCert_arg hm (by simp)))
      h6 h7 (fun i cn alt br k x y z w => iha i cn alt br k x y z w
        (marksCert_arg hm (by simp [List.mem_of_getElem? y]))) h9
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun _ h1 h2 h3 h4 h5 _ h7 _ iha ihe hm => .casesReduced
      (CLCertProof.cert (marksCert_arg (a := markReduced _) hm (by simp))) h1 h2 h3 h4 h5
      (iha (marksCert_arg hm (by simp))) h7
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun h1 h2 h3 _ ih hm => .proj h1 h2 h3 (ih hm)) (fun h _ => .litZero h)
    (fun h _ ih _ => .litSucc h (ih trivial))
    (fun h1 h2 _ h4 _ iha ihe hm => .quotMk h1 h2 (iha (marksCert_arg hm (by simp))) h4
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun h1 h2 _ _ h5 _ ihf ihq ihe hm => .quotLift h1 h2 (ihf (marksCert_arg hm (by simp)))
      (ihq (marksCert_arg hm (by simp))) h5
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun h1 h2 h3 h4 h5 h6 h7 _ h9 _ _ h12 _ ihm ihi ihj ihe hm => .recLet h1 h2 h3 h4 h5 h6 h7
      (fun i a a' x y => ihm i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x]))) h9
      (fun i a a' x y => ihi i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
      (ihj (marksCert_arg hm (by simp))) h12
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun h1 h2 h3 h4 h5 h6 h7 _ h9 h10 _ _ h13 _ ihm ihi ihj ihe hm => .recFix h1 h2 h3 h4 h5 h6
      h7 (fun i a a' x y => ihm i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
      h9 h10 (fun i a a' x y => ihi i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
      (ihj (marksCert_arg hm (by simp))) h13
      fun i a a' x y => ihe i a a' x y (marksCert_arg hm (by simp [List.mem_of_getElem? x])))
    (fun _ hm => .box hm) (fun _ ih hm => .done (ih hm)) (fun _ ih hm => .lam (ih hm))
    (fun _ ih hm => .etaLam (ih hm)) h hm

/-- A λ□ body related to a constant without certificates is related with con-leche's
certificates if every marking of the constant's value is certified, when the traversal erases it
(`ErasedValue`). Reference: none (DV-32). -/
theorem ErasesDecl.toCert {env : ConLeche.Env} {σ : EvalEnv} {ci : ConstantInfo}
    {cb : ConstantBody}
    (hd : ErasedValue σ.decls ci → ∀ v, ci.value? (allowOpaque := true) = some v →
      ∀ vM, MarkOf σ.decls σ.cfg [] v vM → MarksCert env [] vM)
    (h : ErasesDecl noCert σ ci cb) : ErasesDecl (CLCert env) σ ci cb := by
  unfold ErasesDecl at h ⊢
  split at h
  · exact h
  · rename_i v hv
    rcases h with h | ⟨ha, he, hex, b', hb, hall⟩
    · exact .inl h
    · exact .inr ⟨ha, he, hex, b', hb, fun vM hM => Erases.toCert (hall vM hM) (hd he v hv vM hM)⟩

/-- Erased dependencies without certificates are erased dependencies with con-leche's
certificates if every marking of the value of every constant of `σ` that the traversal erases
(`ErasedValue`) is certified. Reference: none (DV-32). -/
theorem ErasesDeps.toCert {env : ConLeche.Env} {σ : EvalEnv} {lenv : GlobalDeclarations}
    {t : LBTerm}
    (hd : ∀ c ci, findDecl σ.decls c = some ci → ErasedValue σ.decls ci → ∀ v,
      ci.value? (allowOpaque := true) = some v → ∀ vM, MarkOf σ.decls σ.cfg [] v vM →
        MarksCert env [] vM)
    (h : ErasesDeps noCert σ lenv t) : ErasesDeps (CLCert env) σ lenv t := by
  induction h with
  | box => exact .box
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hf hl hdecl _ ih => exact .const hf hl (ErasesDecl.toCert (hd _ _ hf) hdecl) ih
  | construct hi hind _ ih => exact .construct hi hind ih
  | case hi hind _ _ ihd ihb => exact .case hi hind ihd ihb
  | proj hi hind _ ih => exact .proj hi hind ih
  | fix _ ih => exact .fix ih

/-- Over a closure without free variables, every marking of the value of one of its constants
that the traversal erases (`ErasedValue`) is certified: `ProgCert` certifies one, and the marking
is a function of the value (`markOf_det`). Reference: none (DV-32, DV-37). -/
theorem marksCert_of_progCert {env : ConLeche.Env} {decls : List ConstantInfo}
    {cfg : ErasureConfig} {ê : Expr} (hcert : ProgCert env decls cfg ê)
    (hcl : ClosedDecls decls = true) {c : Name} {ci : ConstantInfo}
    (hf : findDecl decls c = some ci) (he : ErasedValue decls ci) {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v)
    {vM : Expr} (hM : MarkOf decls cfg [] v vM) : MarksCert env [] vM := by
  have hci := (Decls.findDecl_eq_some hf).1
  obtain ⟨vM', hM', -, hC⟩ := hcert.2.2 ci hci he v hv
  have hfv : FVarsIn (fun _ => False) v := by
    have h := (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hcl ci hci).2
    rw [hv] at h
    simp only [Option.all_some, Bool.not_eq_true'] at h
    exact OracleRen.fvarsIn_of_hasFVar h
  rw [← markOf_det hcl hfv hM' hM]
  exact hC

/-- The closure of a program con-leche accepts carries no mark key: `DeclsOf?` asks it of the
program. Reference: none (DV-39). -/
theorem noMarkKeysDecls_of {P decls : List ConstantInfo} {env : ConLeche.Env}
    (hacc : ConLecheAccepts P env) (hsub : SubEnv decls P) : NoMarkKeysDecls decls = true := by
  obtain ⟨ds, hds, -⟩ := hacc
  unfold DeclsOf? at hds
  split at hds
  · rename_i hc
    have hP := hc.2
    unfold NoMarkKeysDecls
    rw [List.all_eq_true] at hP ⊢
    exact fun ci hci => hP ci (findDecl_mem (hsub ci hci)).1
  · cases hds

end Final

open Final in
/-- The final theorem: partial correctness of `#erase` on the fragment, against con-leche
(statement and scope: `erase_correct_statement`). Adapted from `ML-V Final.lean:52`. Reference:
`erase_correct` (`MR E/ErasureFunctionProperties.v:657`), which composes the erasure's correctness
with `erases_correct` (`MR E/ErasureCorrectness.v:51`); MC §7.3–7.4. -/
theorem erase_correct : erase_correct_statement.{w} := by
  intro P decls env view cfg e ê v p inl hacc hty hclean hview hfrag hnopre hrun hmark hcert hev
  have hsub := collectDeps_sub hacc hview hty hfrag hnopre
  have hG := coreEnv_of hacc hsub hnopre hfrag
  obtain ⟨hinj, -, -, hbn, har⟩ := collectDeps_spec hacc hview hty hfrag
  obtain ⟨lenv, tb, rfl, her, hdeps, hlc⟩ := erasePure_erases hacc hsub hnopre hfrag
    (eraseEntry_pure hfrag hrun)
    (fun ci hci he v hv => (hcert.2.2 ci hci he v hv).imp fun _ h => h.1)
    hmark
  obtain ⟨vb, hvb, hlb⟩ := erases_correct (σ := evalEnvOf view cfg decls) hinj hbn har hG.ctors
    hG.natShaped hG.natCtors hG.recs hlc her hdeps hev
  exact ⟨lenv, tb, vb, rfl, Erases.toCert her hcert.2.1,
    ErasesDeps.toCert
      (fun _ _ hf he _ hv _ hM => marksCert_of_progCert hcert hG.closed hf he hv hM)
      hdeps,
    hvb, hlb, srcEval_sound hacc hsub hty hclean (noMarkKeysDecls_of hacc hsub) hmark hev⟩

end EraseProof
