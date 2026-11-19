import EraseProof.Final

/-!
# The final theorem on first-order values

On a first-order value (`FirstOrderValue`: a tree of saturated constructor applications with
frozen and literal leaves) the λ□ value of the final theorem is determined: it is the value's
structural erasure `foErase` (`erase_correct_firstorder`). `Erases.firstOrder` shows that an
erasure of a first-order value is its structural erasure: a constructor node erases by
`Erases.ctor` only (`Erases.ctor_inv`), a frozen leaf to `□` only (`SimCases.box_inv`) and a literal
to its Peano numeral (`Erases.lit_peano`). `SrcEval.certValue` shows that every evaluation result
carries con-leche's certificates on its data (`CertValue`), whence `CertValue.firstOrder`: a
first-order value is typed by con-leche and its frozen leaves are erasable. Adapted from
`ML-V FirstOrder.lean`: `□` is related to `erase`-marked terms only, so the λ□ part needs no λ□
evaluation result and no exclusion of `□` on constructor nodes.
-/

open Lean Erasure

namespace EraseProof

namespace FirstOrder

variable {σ : EvalEnv}

/-! ## The λ□ value -/

/-- The structural erasure of a spine erases its arguments. Copy of `ML-V FirstOrder.lean:66`. -/
theorem foErase_foldl (σ : EvalEnv) :
    ∀ (as : List Expr) (f : Expr) (acc : List LBTerm),
      foErase σ (as.foldl .app f) acc = foErase σ f (as.map (foErase σ · []) ++ acc)
  | [], _, _ => rfl
  | a :: as, f, acc => by
    rw [List.foldl_cons, foErase_foldl σ as (.app f a) acc, List.map_cons, foErase]
    rfl

/-- An erasure of a Nat literal is its Peano numeral (`Erases.litZero`, `Erases.litSucc`). -/
theorem Erases.lit_peano {cert : BoxCert} {Γ : List CtxBinder} (k : Nat) :
    ∀ {tb : LBTerm}, Erases cert σ Γ (.lit (.natVal k)) tb →
      ∃ iid, IndIdOf σ ``Nat = some iid ∧ tb = peanoLB iid k := by
  induction k with
  | zero =>
    intro tb h
    generalize hx : Expr.lit (.natVal 0) = y at h
    cases h with
    | litZero hid => exact ⟨_, hid, rfl⟩
    | litSucc => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases SimCases.spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
  | succ k ih =>
    intro tb h
    generalize hx : Expr.lit (.natVal (k + 1)) = y at h
    cases h with
    | litZero => cases hx
    | litSucc hid ht =>
      cases hx
      obtain ⟨iid', hid', rfl⟩ := ih ht
      rw [hid] at hid'; cases hid'
      exact ⟨_, hid, rfl⟩
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases SimCases.spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx

/-- An erasure of a first-order value is its structural erasure: a constructor node erases by
`Erases.ctor` only (`Erases.ctor_inv`), a frozen leaf to `□` only (`box_inv`), a literal to its
Peano numeral (`Erases.lit_peano`). Adapted from `ML-V FirstOrder.lean:96`: `□` is related to
`erase`-marked terms only, so no λ□ evaluation result is needed. Reference:
`firstorder_erases_deterministic` (`MR E/ErasureFunctionProperties.v:2079`). -/
theorem Erases.firstOrder {cert : BoxCert} {Γ : List CtxBinder} {v : Expr}
    (hv : FirstOrderValue σ v) : ∀ {vb : LBTerm}, Erases cert σ Γ v vb → vb = foErase σ v [] := by
  induction hv with
  | @ctor c us as cv hc _ _ ih =>
    intro vb h
    obtain ⟨iid, as', hid, rfl, hlen', hall, hp, -⟩ := Erases.ctor_inv hc h
    have hargs : as' = as.map (foErase σ · []) := by
      apply List.ext_getElem (by rw [List.length_map, hlen'])
      intro i h1 h2
      rw [List.getElem_map]
      exact ih _ (List.getElem_mem _)
        (hall i _ _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem h1))
    rw [mkAppN_toArray, foErase_foldl, List.append_nil, foErase, hc]
    simp only [hp, hid, Bool.false_eq_true, ite_false]
    rw [hargs]
  | frozen => intro vb h; rw [SimCases.box_inv h]; rfl
  | lit =>
    intro vb h
    obtain ⟨iid, hid, rfl⟩ := Erases.lit_peano _ h
    rw [foErase, hid]; rfl

/-! ## The certificates of a first-order value -/

/-- A source value with con-leche's certificates on its data: `SrcValue`, whose constructor
spines and literals are typed by con-leche (`CLTyped`) and whose frozen terms are erasable
(`CLErasable`). -/
inductive CertValue (env : ConLeche.Env) (σ : EvalEnv) : Expr → Prop
  | lam : CertValue env σ (.lam n A b bi)
  | etaLam : CertValue env σ (markEta (.lam n A b bi))
  | sort : CertValue env σ (.sort u)
  | forallE : CertValue env σ (.forallE n A B bi)
  | spine : AtomSpine σ e → CertValue env σ e
  | ctor {args : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      CLTyped env (mkAppN (.const c us) args.toArray) → (∀ a ∈ args, CertValue env σ a) →
      CertValue env σ (mkAppN (.const c us) args.toArray)
  | lit : CLTyped env (.lit (.natVal k)) → CertValue env σ (.lit (.natVal k))
  | quotMk : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor →
      CertValue env σ (mkAppN (.const c us) [α, r, a].toArray)
  | frozen : CLErasable env s → CertValue env σ (markErase s)

variable {env : ConLeche.Env}

/-- A certified constructor spine is typed and its arguments are certified values. -/
theorem CertValue.ctor_inv {c : Name} {us : List Level} {cv : ConstructorVal} {args : List Expr}
    (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (h : CertValue env σ (mkAppN (.const c us) args.toArray)) :
    CLTyped env (mkAppN (.const c us) args.toArray) ∧ ∀ a ∈ args, CertValue env σ a := by
  have hfn := getAppFn_mkAppN_const c us args
  generalize hx : mkAppN (.const c us) args.toArray = x at h hfn ⊢
  cases h with
  | lam | etaLam | sort | forallE | lit | frozen => cases hfn
  | spine hs =>
    obtain ⟨c', us', h1, h2⟩ := AtomSpine.head hs
    rw [hfn] at h1; cases h1
    rw [isAtom_ctor hc] at h2; cases h2
  | ctor _ ht hargs =>
    obtain ⟨-, -, rfl⟩ := mkAppN_const_inj hx
    exact ⟨ht, hargs⟩
  | quotMk hq =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    rw [hc] at hq; cases hq

/-- A certified frozen term is erasable. -/
theorem CertValue.frozen_inv {s : Expr} (h : CertValue env σ (markErase s)) : CLErasable env s := by
  generalize hx : markErase s = x at h
  cases h with
  | frozen h => cases hx; exact h
  | spine hs =>
    subst hx
    obtain ⟨_, _, h1, -⟩ := AtomSpine.head hs
    cases h1
  | ctor | quotMk => cases SimCases.spine_fn hx
  | lam | etaLam | sort | forallE | lit => cases hx

/-- A certified literal is typed. -/
theorem CertValue.lit_inv {k : Nat} (h : CertValue env σ (.lit (.natVal k))) :
    CLTyped env (.lit (.natVal k)) := by
  generalize hx : Expr.lit (.natVal k) = x at h ⊢
  cases h with
  | lit h => exact h
  | spine hs =>
    subst hx
    obtain ⟨_, _, h1, -⟩ := AtomSpine.head hs
    cases h1
  | ctor | quotMk => cases SimCases.spine_fn hx
  | lam | etaLam | sort | forallE | frozen => cases hx

/-- A certified value that does not block `appCong` is an atom spine. Adapted from
`SrcValue.atomSpine`. -/
theorem CertValue.atomSpine {e : Expr} (h : CertValue env σ e) (hb : ¬ BlocksCong σ e) :
    AtomSpine σ e := by
  cases h with
  | spine hs => exact hs
  | lam | etaLam | sort | forallE | lit | frozen => exact absurd trivial hb
  | ctor hc _ _ => exact absurd (blocksCong_ctor (getAppFn_mkAppN_const _ _ _) hc) hb
  | quotMk hc hk => exact absurd (blocksCong_quot (getAppFn_mkAppN_const _ _ _) hc hk) hb

/-- Evaluation results are certified values: the rules that build data carry `CLOk` (`ctor`,
`lit`) or `CLErasable` (`frozen`, `frozenApp`, `projFrozen`), and a projection returns an argument
of a certified constructor value. Adapted from `SrcEval.value`. -/
theorem SrcEval.certValue {e v : Expr} (hev : SrcEval env σ e v) : CertValue env σ v := by
  induction hev with
  | beta | etaBeta | zeta | delta | casesIota | casesLitZero | casesLitSucc | casesFrozen
    | quotLift | recIota => assumption
  | constAtom h => exact .spine (.const h)
  | @ctor c cv us as vs hc hl hlv _ hok ih =>
    refine .ctor hc hok.1 fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i as[i] _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
  | quotMk hc hk => exact .quotMk hc hk
  | proj _ hcv hfs _ ihm =>
    obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
    exact (CertValue.ctor_inv hC ihm).2 _ (List.mem_append_right _ (List.mem_of_getElem? hfs))
  | projFrozen _ _ h => exact .frozen h
  | frozen h => exact .frozen h
  | frozenApp _ _ _ h => exact .frozen h
  | lit h => exact .lit h.1
  | appCong _ _ hb _ _ ihf _ => exact .spine (.app (ihf.atomSpine hb))
  | atom h =>
    rename_i e
    cases e <;> first | exact .lam | exact .sort | exact .forallE | exact absurd h id
  | etaLam => exact .etaLam

/-- A frozen leaf of a spine is one of its head or of an argument. -/
theorem frozenLeaf_foldl {s : Expr} : ∀ {as : List Expr} {f : Expr},
    FrozenLeaf (as.foldl .app f) s → FrozenLeaf f s ∨ ∃ a ∈ as, FrozenLeaf a s
  | [], _, h => .inl h
  | a :: as, f, h => by
    rw [List.foldl_cons] at h
    rcases frozenLeaf_foldl h with h | ⟨b, hb, h⟩
    · cases h with
      | appFn h => exact .inl h
      | appArg h => exact .inr ⟨a, List.mem_cons_self .., h⟩
    · exact .inr ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- A certified first-order value is typed by con-leche and its frozen leaves are erasable. -/
theorem CertValue.firstOrder {v : Expr} (hfo : FirstOrderValue σ v) :
    CertValue env σ v → CLTyped env v ∧ ∀ s, FrozenLeaf v s → CLErasable env s := by
  induction hfo with
  | @ctor c us as cv hc _ _ ih =>
    intro h
    obtain ⟨ht, hargs⟩ := CertValue.ctor_inv hc h
    refine ⟨ht, fun s hs => ?_⟩
    rw [mkAppN_toArray] at hs
    rcases frozenLeaf_foldl hs with hs | ⟨a, ha, hs⟩
    · cases hs
    · exact (ih a ha (hargs a ha)).2 s hs
  | frozen =>
    intro h
    have he := CertValue.frozen_inv h
    obtain ⟨c, F, T, hc, hi, -⟩ := id he
    refine ⟨⟨c, F, T, hc, hi⟩, fun s' hs => ?_⟩
    cases hs
    exact he
  | lit => intro h; exact ⟨CertValue.lit_inv h, fun s hs => by cases hs⟩

end FirstOrder

open Final FirstOrder in
/-- The final theorem on first-order values (statement: `erase_correct_firstorder_statement`):
the composition of `erase_correct` without its certified conjuncts (`erasePure_erases` at the
closure values' markings `hvals`, `erases_correct`, `srcEval_sound`), with `Erases.firstOrder` on
the λ□ value and `CertValue.firstOrder` on the source value. Adapted from
`ML-V FirstOrder.lean:132`. Reference: `erase_correct_strong`
(`MR E/ErasureFunctionProperties.v:2269`). -/
theorem erase_correct_firstorder : erase_correct_firstorder_statement.{w} := by
  intro P decls env view cfg e ê v p inl hacc hty hclean hcleanD hview hfrag hnopre hrun hmark
    hvals hev hfo
  have hsub := collectDeps_sub hacc hview hty hfrag hnopre
  have hG := coreEnv_of hacc hsub hnopre hfrag
  obtain ⟨hinj, -, -, hbn, har⟩ := collectDeps_spec hacc hview hty hfrag
  obtain ⟨lenv, tb, rfl, her, hdeps, hlc⟩ := erasePure_erases hacc hsub hnopre hfrag
    (eraseEntry_pure hfrag hrun) hvals hmark
  obtain ⟨vb, hvb, hlb⟩ := erases_correct (σ := evalEnvOf view cfg decls) hinj hbn har hG.ctors
    hG.natShaped hG.natCtors hG.recs hlc her hdeps hev
  obtain ⟨hT, hL⟩ := CertValue.firstOrder hfo (SrcEval.certValue hev)
  refine ⟨lenv, tb, rfl, ?_, hT, hL, srcEval_sound hacc hsub hty hclean hcleanD hmark hev⟩
  rw [← Erases.firstOrder hfo hvb]
  exact hlb

end EraseProof
