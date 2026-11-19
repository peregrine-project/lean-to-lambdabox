import EraseProof.Core.Steps
import EraseProof.Source.Value
import EraseProof.Oracle.Atom

/-!
# Steps of the shipping core's correctness: applications, constants, `visitMutual`

The steps of `visitExpr` on an application spine whose head is no constant with a rule of its own
(`visitExpr_app_step`, `visitExpr_const_step`): the head is erased by `visitExpr` or, for a
constant, by `visitConst`, which registers the constant through `visitMutual` if it is new, and the
arguments one at a time (`visitAppArgs_spec`); each relates the traversal's output to `Erases noCert`
of the marking (`MarkOf.app`, `MarkOf.constApp`) as `ExprSpec` states. The step of `visitMutual`
(`visitMutual_step`, the statement `MutualSpec`): a declaration without value or remapped is
registered as a λ□ axiom (`addAxiom_ok`); a value is erased in the empty context and registered with
its erasure (`StateOK.register`), its erasure being an erasure of every marking of the value
(`ErasesDecl`). `StepIH` collects `ExprSpec` and `MutualSpec` at the fuels up to a bound, the
induction hypothesis of every step; `CoreEnv` collects the facts about the closure the steps read.

The constant head of a spine the oracle keeps is no atom (`AtomBoxed`, the oracle's answer on atom
spines, proved in `atomBoxed`); the value `visitMutual` erases has a marking (`ValuesMarkedOf`,
every value of the closure has one), a premise of the step that reads it.

Reference: the `tApp` and `tConst` cases of `erases_erase` (`MR E/ErasureFunction.v:1228`), with
`erase_constant_body` (`MR E/ErasureFunction.v:1309`) and `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`); adapted from `ML-V Core/Steps.lean:42-118, 1319-1712,
1977-2051, 2410-2651` and `ML-V Core/Frame.lean:438-466`, whose typing premises are replaced by
the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas

/-! ## Application spines -/

/-- The arguments of an application spine. Copy of `ML-V Core/Steps.lean:45`. -/
def spineArgs : Expr → List Expr
  | .app f a => spineArgs f ++ [a]
  | _ => []

theorem spineArgs_foldl : ∀ (as : List Expr) (f : Expr),
    spineArgs (as.foldl .app f) = spineArgs f ++ as
  | [], _ => (List.append_nil _).symm
  | a :: as, f => by
    rw [List.foldl_cons, spineArgs_foldl as, spineArgs, List.append_assoc, List.singleton_append]

/-- Copy of `ML-V Core/Steps.lean:66`. -/
theorem drop_set {α : Type} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a).drop i = a :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_set_self]
  congr 1
  apply List.drop_set_of_lt
  omega

/-- Copy of `ML-V Core/Steps.lean:73`. -/
theorem withAppAux_toList : ∀ (e : Expr) (as : Array Expr) (i : Nat),
    (spineArgs e).length = i + 1 → i < as.size →
    (Expr.withAppAux (fun _ as => as) e as i).toList = spineArgs e ++ as.toList.drop (i + 1)
  | .app f a, as, i, hl, hi => by
    rw [Expr.withAppAux]
    simp only [spineArgs, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at hl
    cases f with
    | app g b =>
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp [spineArgs] at hl; omega⟩
      rw [show j + 1 - 1 = j from rfl,
        withAppAux_toList (.app g b) _ j hl (by simp [Array.size_setIfInBounds]; omega)]
      simp only [Array.set!, Array.toList_setIfInBounds, spineArgs, List.append_assoc,
        List.singleton_append]
      rw [drop_set (by simpa using hi)]
      simp
    | _ =>
      simp only [spineArgs, List.length_nil] at hl
      subst hl
      simp only [Expr.withAppAux, Array.set!, Array.toList_setIfInBounds, spineArgs,
        List.nil_append, List.singleton_append]
      obtain ⟨l⟩ := as
      cases l with
      | nil => simp at hi
      | cons y l => rfl

/-- Copy of `ML-V Core/Frame.lean:438`. -/
theorem withAppAux_eq {γ : Sort _} (k : Expr → Array Expr → γ) :
    ∀ (e : Expr) (as : Array Expr) (i : Nat),
      Expr.withAppAux k e as i = k e.getAppFn (Expr.withAppAux (fun _ as => as) e as i)
  | .app f a, as, i => by
    rw [Expr.withAppAux, Expr.withAppAux]
    exact withAppAux_eq k f _ _
  | .bvar _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit _, _, _ | .mdata .., _, _
  | .proj .., _, _ => rfl

/-- The head of a spine whose head is no application. -/
theorem getAppFn_mkAppN_of {f : Expr} (hf : f.isApp = false) (as : List Expr) :
    (mkAppN f as.toArray).getAppFn = f := by
  rw [mkAppN_toArray, getAppFn_foldl]
  cases f <;> first | rfl | cases hf

/-- `withApp` on a spine whose head is no application passes the head and the arguments. -/
theorem withApp_mkAppN {γ : Sort _} {f : Expr} (hf : f.isApp = false) (as : List Expr)
    (k : Expr → Array Expr → γ) : (mkAppN f as.toArray).withApp k = k f as.toArray := by
  have hsp : spineArgs (mkAppN f as.toArray) = as := by
    rw [mkAppN_toArray, spineArgs_foldl]
    cases f <;> first | rfl | cases hf
  have hn : (mkAppN f as.toArray).getAppNumArgs = as.length := by
    rw [mkAppN_toArray, getAppNumArgs_foldl]
    cases f <;> first | (cases hf; done) | exact Nat.zero_add _
  unfold Expr.withApp
  rw [withAppAux_eq, getAppFn_mkAppN_of hf]
  congr 1
  apply Array.toList_inj.1
  simp only [hn]
  rcases as with _ | ⟨a, as'⟩
  · cases f <;> first | rfl | cases hf
  · simp only [List.length_cons, Nat.add_sub_cancel]
    rw [withAppAux_toList _ _ as'.length (by rw [hsp]; rfl) (by simp), hsp]
    simp

/-- A property of applications that holds of both sides holds of a spine's head and arguments.
Copy of `ML-V Core/Steps.lean:1333`. -/
theorem foldl_pred {Q : Expr → Prop} (hQ : ∀ f a, Q (.app f a) → Q f ∧ Q a) :
    ∀ {f : Expr} {as : List Expr}, Q (as.foldl .app f) → Q f ∧ ∀ a ∈ as, Q a
  | _, [], h => ⟨h, by simp⟩
  | f, b :: as, h => by
    obtain ⟨h1, h2⟩ := foldl_pred hQ (f := .app f b) (as := as) h
    obtain ⟨hf, hb⟩ := hQ f b h1
    refine ⟨hf, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hb
    · exact h2 a ha

/-- The premises of `ExprSpec` on a spine hold of its head and of its arguments. -/
theorem spine_premises {S : FVarId → Prop} {Sc : Name → Prop} {cfg : ErasureConfig}
    {decls : List ConstantInfo} {f : Expr} {as : List Expr}
    (h : FVarsIn S (mkAppN f as.toArray) ∧ (∀ d, nameOccurs d (mkAppN f as.toArray) = true → Sc d) ∧
      NatPlain cfg (mkAppN f as.toArray) ∧ RecShaped cfg decls (mkAppN f as.toArray)) :
    (FVarsIn S f ∧ (∀ d, nameOccurs d f = true → Sc d) ∧ NatPlain cfg f ∧ RecShaped cfg decls f) ∧
      ∀ a ∈ as, FVarsIn S a ∧ (∀ d, nameOccurs d a = true → Sc d) ∧ NatPlain cfg a ∧
        RecShaped cfg decls a := by
  rw [mkAppN_toArray] at h
  exact foldl_pred (Q := fun x => FVarsIn S x ∧ (∀ d, nameOccurs d x = true → Sc d) ∧
    NatPlain cfg x ∧ RecShaped cfg decls x) (fun f a h => ⟨⟨h.1.1, fun d hd => h.2.1 d (by simp [nameOccurs, hd]),
    h.2.2.1.1, h.2.2.2.1⟩, ⟨h.1.2, fun d hd => h.2.1 d (by simp [nameOccurs, hd]),
    h.2.2.1.2, h.2.2.2.2⟩⟩) h

/-- A spine headed by an atom constant is an atom spine. Copy of `ML-V Core/Steps.lean:1350`. -/
theorem AtomSpine.of_getAppFn {σ : EvalEnv} {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    ∀ {e : Expr}, e.getAppFn = .const c us → AtomSpine σ e
  | .const .., h => by cases h; exact .const ha
  | .app f _, h => .app (AtomSpine.of_getAppFn ha (e := f) h)
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h
  | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => nomatch h

/-! ## Free variables of an erasure -/

section
variable {cert : BoxCert} {σ : EvalEnv}

/-- An element of a list pointwise erased from terms without free variables has none. -/
theorem noFVar_mem {as : List Expr} {bs : List LBTerm} {x : FVarId} {b : LBTerm}
    (hlen : as.length = bs.length)
    (ih : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b →
      FVarsIn (fun _ => False) a → ∀ x, hasFVar x b = true → False)
    (has : ∀ a ∈ as, FVarsIn (fun _ => False) a) (hb : b ∈ bs) (h : hasFVar x b = true) : False :=
  forall_mem_of_getElem hlen ih (Q := fun b => hasFVar x b = true → False)
    (fun a _ ha h' => h' (has a ha) x) b hb h

open TargetLift RecLam in
/-- The erasure of a term without free variables has none. Adapted from
`ML-V Core/Steps.lean:214 Erases.hasFVar_of` (no fix variables; the relation is on the marked term,
whose binders are loose indices). Reference: none (`LBTerm.fvar` has no MetaRocq counterpart,
DV-13). -/
theorem Erases.noFVar {Γ : List CtxBinder} {e : Expr} {tb : LBTerm} (h : Erases cert σ Γ e tb)
    (he : FVarsIn (fun _ => False) e) : ∀ x, hasFVar x tb = false := by
  have key : FVarsIn (fun _ => False) e → ∀ x, hasFVar x tb = true → False := by
    refine Erases.rec
      (motive_1 := fun _ e tb _ => FVarsIn (fun _ => False) e → ∀ x, hasFVar x tb = true → False)
      (motive_2 := fun _ _ e br _ => FVarsIn (fun _ => False) e → ∀ x, hasFVar x br.2 = true → False)
      ?bvar ?fvar ?lam ?etaLam ?letE ?app ?const ?ctor ?cases ?casesReduced ?proj ?litZero ?litSucc
      ?quotMk ?quotLift ?recLet ?recFix ?box ?done ?alam ?aeta h
    case bvar | const | box | litZero => intros; simp_all [hasFVar, hasFVarL]
    case fvar => intro _ _ hk _ _; exact hk
    case lam | etaLam => intro _ _ _ _ _ _ _ ih hk x hx; exact ih hk.2 x hx
    case letE =>
      intro _ _ _ _ _ _ _ _ _ _ ihv ihb hk x hx
      simp only [hasFVar, Bool.or_eq_true] at hx
      exact hx.elim (ihv hk.2.1 x) (ihb hk.2.2 x)
    case app =>
      intro _ _ _ _ _ _ _ _ ihf iha hk x hx
      simp only [hasFVar, Bool.or_eq_true] at hx
      exact hx.elim (ihf hk.1 x) (iha hk.2 x)
    case ctor =>
      intro _ _ _ _ _ as as' _ _ _ _ hlen _ ih hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · simp [hasFVar, hasFVarL] at h
      · exact noFVar_mem hlen ih hb.2 ha' h
    case cases =>
      intro _ iv _ _ maj _ _ pre alts extra brs _ _ _ _ hlalts _ hlbrs hcf _ hlex _ ihm iha ihe hk
        x hx
      have hb := fvarsIn_mkAppN.1 hk
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · simp only [hasFVar, Bool.or_eq_true] at h
        rcases h with h | h
        · exact ihm (hb.2 maj (by simp)) x h
        · have key : ∀ brs' : List (List BinderName × LBTerm), hasFVarB x brs' = true →
              ∃ br ∈ brs', hasFVar x br.2 = true := by
            intro brs' h'
            induction brs' with
            | nil => cases h'
            | cons br brs' ih =>
              obtain ⟨ns, b⟩ := br
              simp only [hasFVarB, Bool.or_eq_true] at h'
              rcases h' with h' | h'
              · exact ⟨_, .head _, h'⟩
              · obtain ⟨b', hb', h''⟩ := ih h'
                exact ⟨b', .tail _ hb', h''⟩
          obtain ⟨br, hbr, hbx⟩ := key brs h
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbr
          have hia : i < alts.length := hlbrs ▸ hi
          have hic : i < iv.ctors.length := hlalts ▸ hia
          obtain ⟨kf, hkf⟩ := Option.isSome_iff_exists.1 (hcf i _ (List.getElem?_eq_getElem hic))
          exact iha i _ _ _ kf (List.getElem?_eq_getElem hic) (List.getElem?_eq_getElem hia)
            (List.getElem?_eq_getElem hi) hkf (hb.2 _ (by simp [List.getElem_mem hia])) x hbx
      · exact noFVar_mem hlex ihe (fun a ha => hb.2 a (by simp [ha])) ha' h
    case casesReduced =>
      intro _ _ _ _ _ _ alt _ _ _ extra extra' _ _ _ _ _ _ _ hlex _ iha ihe hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · exact iha (hb.2 alt (by simp)) x h
      · rcases List.mem_append.1 ha' with ha' | ha'
        · rw [List.eq_of_mem_replicate ha'] at h; cases h
        · exact noFVar_mem hlex ihe (fun a ha => hb.2 a (by simp [ha])) ha' h
    case proj => intro _ _ _ _ _ _ _ _ _ _ _ ih hk x hx; exact ih hk x hx
    case litSucc =>
      intro _ _ _ _ _ _ ih _ x hx
      simp only [hasFVar, hasFVarL, Bool.false_or] at hx
      exact ih trivial x hx
    case quotMk =>
      intros; rename_i hlex _ iha ihe hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · exact iha (hb.2 _ (by simp)) x h
      · exact noFVar_mem hlex ihe (fun a ha => hb.2 a (by simp [ha])) ha' h
    case quotLift =>
      intros; rename_i hlex _ ihf ihq ihe hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · exact ihf (hb.2 _ (by simp)) x h
      · rcases List.mem_cons.1 ha' with rfl | ha'
        · exact ihq (hb.2 _ (by simp)) x h
        · exact noFVar_mem hlex ihe (fun a ha => hb.2 a (by simp [ha])) ha' h
    case recLet =>
      intro _ rv minors F _ maj maj' _ _ _ _ _ _ mins' is' _ _ hF _ _ _ _ hlm _ hli _ _ hle _
        ihmin ihis ihmaj ihext hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hFx⟩ := hF
      rcases hasFVar_recLetTerm (N := rv.numMinors) hFx hx with
        ⟨a', ha', h⟩ | ⟨a', ha', h⟩ | h | ⟨a', ha', h⟩
      · exact noFVar_mem hlm ihmin (fun a ha => hb.2 a (by simp [ha])) ha' h
      · exact noFVar_mem hli ihis (fun a ha => hb.2 a (by simp [ha])) ha' h
      · exact ihmaj (hb.2 maj (by simp)) x h
      · exact noFVar_mem hle ihext (fun a ha => hb.2 a (by simp [ha])) ha' h
    case recFix =>
      intro _ rv minors F _ maj _ _ _ _ _ _ _ ws _ _ _ hF _ _ hmins _ hlw _ hws hli _ _ hle _
        _ ihis ihmaj ihext hk x hx
      have hb := fvarsIn_mkAppN.1 hk
      obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hFc, hFx⟩ := hF
      have hG := substl_fix (ws := ws) (by rw [← hlw, hmins]; exact hFc) hFx
        fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
      rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
      · rw [hG.2 x] at h; cases h
      · rcases List.mem_append.1 ha' with ha' | ha'
        · rcases List.mem_append.1 ha' with ha' | ha'
          · exact noFVar_mem hli ihis (fun a ha => hb.2 a (by simp [ha])) ha' h
          · rw [List.mem_singleton.1 ha'] at h
            exact ihmaj (hb.2 maj (by simp)) x h
        · exact noFVar_mem hle ihext (fun a ha => hb.2 a (by simp [ha])) ha' h
    case done => intros; rename_i ih hk x hx; exact ih hk x hx
    case alam | aeta => intros; rename_i ih hk x hx; exact ih hk.2 x hx
  exact fun x => Bool.eq_false_iff.2 fun hx => key he x hx

end

/-! ## The closure, the statement of `visitMutual`, the induction hypothesis -/

/-- The facts about the closure `decls` that the steps read: its types and values have no free
variable, distinct kernames and block names, syntactic arities for its inductive types, no compiled
pre-definition for what the traversal erases by its value; what the traversal reads is `NatPlain`
and `RecShaped`; the quotient type has an arity and `Quot.ind` is named so; and every value
`visitMutual` erases (of a declaration that is neither a theorem nor a recognized `casesOn`) is of
a one-member block and has a scope without its own declaration, so that `visitMutual` erases it
as a non-recursive constant and cannot register the declaration while it erases the value.
Adapted from `ML-V Core/Steps.lean:794 CoreEnv`, whose typing facts have no counterpart; the scope
of a value replaces `ProgEnv.value_suffix` (`ML-V Core/Steps.lean:1741`). Reference: the hypotheses
of `erases_erase` (`MR E/ErasureFunction.v:1228`): `wf_ext Σ` and the abstract environment's
relation to `Σ`; `erase_global_deps_fresh` (`MR E/ErasureFunctionProperties.v:1206`). -/
structure CoreEnv (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) : Prop where
  closed : ClosedDecls decls = true
  inj : KernameInj decls
  bn : BlockNamesInj decls
  arity : ArityTypes decls
  nopre : NoPreDefs view cfg decls
  npd : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → NatPlain cfg x
  recShaped : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecShaped cfg decls x
  quotType : ∀ c q, findDecl decls c = some (.quotInfo q) → q.kind = .type →
    (arityShape q.type).isSome = true
  quotInd : ∀ c q, findDecl decls c = some (.quotInfo q) → q.kind = .ind → c = ``Quot.ind
  value : ∀ c ci v, findDecl decls c = some ci → ci.value? (allowOpaque := true) = some v →
    IsThm ci = false → casesInfo? decls c = none →
    ci.all.length = 1 ∧ ∃ Sc, ScopeOK decls Sc ∧ (∀ d, nameOccurs d v = true → Sc d) ∧ ¬ Sc c
  irr : ∀ iv, (∃ ci ∈ decls, ci = .inductInfo iv) → cfg.remove_irrel_constr_args = false
  phase : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci
  block : ∀ T iv, findDecl decls T = some (.inductInfo iv) → iv.all.Nodup ∧ iv.name ∈ iv.all ∧
    ∀ n ∈ iv.all, ∀ ivn, findDecl decls n = some (.inductInfo ivn) →
      ivn.all = iv.all ∧ ivn.numParams = iv.numParams
  ctors : CtorsListed decls
  /-- An inductive lists each constructor at the constructor's index, with the inductive's
  parameter count (`blockShapeOK`'s `cidx`, `numParams`), so its constructors are distinct. -/
  ctorIdx : ∀ T iv, findDecl decls T = some (.inductInfo iv) → ∀ (j : Nat) cn,
    iv.ctors[j]? = some cn → ∃ cv, findDecl decls cn = some (.ctorInfo cv) ∧ cv.cidx = j ∧
      cv.numParams = iv.numParams
  /-- The type of a constructor of `T` binds the parameters and the fields with `Π`s over an
  application of `T` (`blockShapeOK`). -/
  ctorShape : ∀ T iv, findDecl decls T = some (.inductInfo iv) → ∀ cn ∈ iv.ctors, ∀ cv,
    findDecl decls cn = some (.ctorInfo cv) → piLen cv.type = iv.numParams + cv.numFields ∧
      appHeadConst (piResult (iv.numParams + cv.numFields) cv.type) = some T
  /-- `Nat`, if declared, has Lean's shape, and ``Nat.zero``, ``Nat.succ`` are its constructors
  (con-leche's `natBasis`). -/
  natShaped : NatShaped (evalEnvOf view cfg decls)
  natCtors : NatCtors (evalEnvOf view cfg decls)
  /-- The recursor `T.rec` of a block of one type has one minor premise per constructor
  (`blockShapeOK`'s `numMinors`). -/
  recMinors : ∀ c rv T iv, findDecl decls c = some (.recInfo rv) → rv.all = [T] →
    rv.name = mkRecName T → findDecl decls T = some (.inductInfo iv) →
    rv.numMinors = iv.ctors.length
  /-- The recursors have Lean's shape (`RecsShaped`; `blockShapeOK`'s `recMotivesOK`). -/
  recs : RecsShaped decls

/-- On an application spine whose head is an atom (`EvalEnv.isAtom`), the shipping oracle answers
`true` or fails, never `false`, under every list of locals. Statement of
`ML-V Oracle/Atom.lean:480 Pure.isErasable_atom` at `evalEnvOf`. Reference: none; it plays the part
of `isErasable` on `tInd` (`MR E/Extract.v:106`); DV-11, DV-24. -/
def AtomBoxed (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) : Prop :=
  ∀ ls e b, AtomSpine (evalEnvOf view cfg decls) e →
    Pure.isErasable ⟨decls⟩ oracleFuel ls e = .ok b → b = true

/-- The oracle never answers `false` on an atom spine of the closure. Reference: as `AtomBoxed`. -/
theorem atomBoxed (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) :
    AtomBoxed view cfg decls :=
  fun _ _ _ hs h => EraseProof.Pure.isErasable_atom rfl hs h

/-- The correctness of `visitMutual fuel c` at the pure backend: on an unregistered constant of a
scope `Sc` that is a definition, an opaque or an axiom (`EmitsConst`, not a theorem), or
`Quot.ind`, and not a recognized `casesOn` constant, from a state with `StateOK`, a successful run
registers `c` and `Grows` within `Sc`. Adapted from `ML-V Core/Steps.lean:902`. Reference: the
`ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`), which erases a
declaration with `erase_constant_body` (`MR E/ErasureFunction.v:1309`). -/
def MutualSpec (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat)
    (c : Name) : Prop :=
  ∀ ⦃Sc : Name → Prop⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄
    ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
    ScopeOK decls Sc → Sc c → tc.config = cfg →
    (∃ ci, findDecl decls c = some ci ∧ IsThm ci = false ∧
      (EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind)) →
    casesInfo? decls c = none →
    StateOK noCert (evalEnvOf view cfg decls) st → st.constants[c]? = none →
    (visitMutual (m := PureM) fuel c).runPure st tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
    Grows (evalEnvOf view cfg decls) Sc st st' ps ps' ∧ ∃ kn, st'.constants[c]? = some kn

/-- The induction hypothesis of every step at fuel `fuel + 1`: `ExprSpec` and `MutualSpec` at
every fuel up to `fuel`. Copy of `ML-V Core/Steps.lean:918`. Reference: the induction of
`erases_erase` (`MR E/ErasureFunction.v:1228`), on the fuel of the shipping traversal. -/
structure StepIH (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat) :
    Prop where
  expr : ∀ m ≤ fuel, ∀ e, ExprSpec view cfg decls m e
  mutDecl : ∀ m ≤ fuel, ∀ c, MutualSpec view cfg decls m c

/-! ## Application spines and constants -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `visitAppArgs (j + 1) tf args`, from `visitExpr` at `j` (`ih`): applying an erasure of the head
to the erasures of the arguments' markings, one at a time, erases the marked spine
(`Erases.appS`). Adapted from `ML-V Core/Steps.lean:1381`. Reference: the `tApp` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tApp` (`MR E/Extract.v:101`). -/
theorem visitAppArgs_spec {j : Nat} (ih : ∀ e, ExprSpec view cfg decls j e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r tf : LBTerm} {F : Expr}
    {as âs : List Expr} (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc)
    (hR : RenOK ρ S ls tc.locals ps.next)
    (hargs : ∀ a ∈ as, FVarsIn S a ∧ (∀ d, nameOccurs d a = true → Sc d) ∧ NatPlain cfg a ∧
      RecShaped cfg decls a)
    (hlen : as.length = âs.length)
    (hm : ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hf : Erases noCert (evalEnvOf view cfg decls) [] F tf) (hc : closedn 0 tf = true)
    (hdf : ErasesDeps noCert (evalEnvOf view cfg decls) st.gdecls tf)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf (as.map (renFV ρ)).toArray).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (mkAppN F (âs.map (renFV ρ)).toArray) r ∧
      closedn 0 r = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction as generalizing âs F tf st ps with
  | nil =>
    cases âs with
    | nil => cases hrun; exact ⟨hf, hc, hdf, .refl hok⟩
    | cons => cases hlen
  | cons a l ihl =>
    cases âs with
    | nil => cases hlen
    | cons â âl =>
    rw [List.map_cons, List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := ok_of_bind hx
    cases hx
    obtain ⟨hfa, hoa, hna, hra⟩ := hargs a (.head _)
    have ⟨hera, hca, hdepsa, hgra⟩ := ih a hctx hR hfa hsc hoa hna hra hok (hm 0 a â rfl rfl) ha
    have ⟨her, hcr, hdeps, hgr⟩ := ihl (F := .app F (renFV ρ â)) (tf := .app tf ta)
      (hR.mono hgra.next) (fun b hb => hargs b (.tail _ hb)) (by simpa using hlen)
      (fun i b bM h1 h2 => hm (i + 1) b bM h1 h2) hgra.inv (Erases.appS hf hera)
      (by simp [closedn, hc, hca]) (.app (ErasesDeps.ext hgra.ext hdf) hdepsa) hrun
    refine ⟨?_, hcr, hdeps, hgra.trans hgr⟩
    rw [mkAppN_toArray] at her ⊢
    exact her

/-- `visitConst` at the pure backend, given `MutualSpec` at the fuels up to `j`, on a constant of
the scope that `MutualSpec` registers: a successful run returns the `tConst` of its kername, whose
λ□ dependencies are erased, and it `Grows` within the scope; no fix variable is bound (`CtxOK`).
Adapted from `ML-V Core/Steps.lean:1434`. Reference: the `tConst` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), and `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). -/
theorem visitConst_spec {j : Nat} (ihM : ∀ m ≤ j, ∀ c, MutualSpec view cfg decls m c)
    {Sc : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {us : List Level} (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc) (hS : Sc c)
    (hem : ∃ ci, findDecl decls c = some ci ∧ IsThm ci = false ∧
      (EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind))
    (hcs : casesInfo? decls c = none) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hrun : (visitConst (m := PureM) j (.const c us)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    r = .const (toKername c) ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  have hfx : (tc.fixvars.bind fun m => m[c]?) = none := by rw [hctx.fixvars]; rfl
  cases j with
  | zero => rw [visitConst] at hrun; cases hrun
  | succ i =>
  rw [visitConst] at hrun
  rw [runPure_read_bind] at hrun
  rw [hfx] at hrun
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨kn, st₁⟩, ps₁⟩, hk, hrun⟩ := ok_of_bind hrun
  cases hrun
  cases i with
  | zero => rw [get_constant_kername] at hk; cases hk
  | succ h =>
  obtain ⟨hcase, huniq⟩ := get_constant_kername_ok hk
  rcases hcase with ⟨hreg, rfl, rfl⟩ | ⟨hnew, hmut⟩
  · obtain ⟨rfl, hdeps⟩ := hok.kername hreg
    exact ⟨rfl, hdeps, .refl hok⟩
  · obtain ⟨hgr, kn', hkn'⟩ := ihM h (by omega) c hsc hS hctx.config hem hcs hok hnew hmut
    cases huniq kn' hkn'
    obtain ⟨rfl, hdeps⟩ := hgr.inv.kername hkn'
    exact ⟨rfl, hdeps, hgr⟩

/-- A constant without an arity of its own (`markArity?`) is no recognized `casesOn` and no
constructor, a quotient constant without an evaluation arity, and a recursor that stays a constant
whenever its block is read. -/
theorem markArity?_none {c : Name} (h : markArity? decls cfg c = none) :
    casesInfo? decls c = none ∧ ctorArity? decls c = none ∧
      (∀ qv, findDecl decls c = some (.quotInfo qv) → quotEvalArity qv.kind = none) ∧
      ∀ rv, findDecl decls c = some (.recInfo rv) → ∀ ivs cvs,
        recBlockOf? decls rv = some (ivs, cvs) → recStaysConstant cfg.nat rv ivs cvs = true := by
  unfold markArity? at h
  split at h
  · cases h
  rename_i hcs
  split at h
  · cases h
  rename_i hca
  refine ⟨hcs, hca, fun qv hq => ?_, fun rv hr ivs cvs hb => ?_⟩
  · rw [hq] at h; exact h
  · rw [hr] at h
    dsimp only at h
    rw [hb] at h
    cases hst : recStaysConstant cfg.nat rv ivs cvs
    · simp [hst] at h
    · rfl

/-- The head of a constant spine that the oracle keeps and that has no rule of its own: no atom
(`AtomBoxed`), no special arity, no recursor (`RecShaped`), and a declaration that `MutualSpec`
registers. -/
theorem constHead_ok (hG : CoreEnv view cfg decls)
    {Sc : Name → Prop} {ls : List Local} {c : Name} {us : List Level} {as : List Expr}
    (hsc : ScopeOK decls Sc) (hS : Sc c) (hma : markArity? decls cfg c = none)
    (hrc : ∀ rv, findDecl decls c = some (.recInfo rv) → RecInFragment cfg decls rv)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel ls (mkAppN (.const c us) as.toArray) = .ok false) :
    (evalEnvOf view cfg decls).isAtom c = false ∧ specialArity (evalEnvOf view cfg decls) c = none ∧
      (∀ rv, findDecl decls c ≠ some (.recInfo rv)) ∧ casesInfo? decls c = none ∧
      ∃ ci, findDecl decls c = some ci ∧ IsThm ci = false ∧
        (EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind) := by
  obtain ⟨hcs, hca, hcq, hcr⟩ := markArity?_none hma
  have hnr : ∀ rv, findDecl decls c ≠ some (.recInfo rv) := fun rv hrv => by
    obtain ⟨T, iv, cvs, -, -, hb, -, hst⟩ := hrc rv hrv
    rw [hcr rv hrv _ _ hb] at hst; cases hst
  have hat : (evalEnvOf view cfg decls).isAtom c = false := by
    cases ha : (evalEnvOf view cfg decls).isAtom c with
    | false => rfl
    | true => cases atomBoxed view cfg decls _ _ _ (AtomSpine.of_getAppFn ha (getAppFn_mkAppN_const c us _)) hor
  obtain ⟨ci, hci, -⟩ := hsc c hS
  have hci' : findDecl (evalEnvOf view cfg decls).decls c = some ci := hci
  have hco : (evalEnvOf view cfg decls).casesOn? c = none := by
    simp [EvalEnv.casesOn?, casesOnOf?, evalEnvOf, hcs]
  have hatom_of : (arityShape ci.type).isSome = true ∨ IsThm ci = true → OwnRules ci = false →
      (∀ d, ci ≠ .defnInfo d) → False := by
    intro hty hown hnd
    have : (evalEnvOf view cfg decls).isAtom c = true := by
      have hun : (evalEnvOf view cfg decls).unfold? c = none := by
        unfold EvalEnv.unfold?
        rw [hci']
        split
        · rename_i v hv; cases hv; exact absurd rfl (hnd v)
        · rfl
      simp only [EvalEnv.isAtom, hci', hun, hco, hown, Option.isNone_none, Bool.not_false,
        Bool.true_and]
      rcases hty with h | h <;> simp [h]
    rw [hat] at this; cases this
  refine ⟨hat, ?_, hnr, hcs, ci, hci, ?_⟩
  · unfold specialArity
    rw [hci']
    cases ci with
    | ctorInfo cv =>
      have : ctorArity? decls c = some (cv.numParams + cv.numFields) := by
        unfold ctorArity?; rw [show findConst decls c = findDecl decls c from rfl, hci]
      rw [hca] at this; cases this
    | quotInfo q => exact hcq q hci
    | recInfo rv => exact absurd hci (hnr rv)
    | _ => simp [hco]
  · cases ci with
    | defnInfo | opaqueInfo | axiomInfo => exact ⟨rfl, .inl rfl⟩
    | thmInfo v => exact (hatom_of (.inr rfl) rfl nofun).elim
    | inductInfo iv =>
      exact (hatom_of (.inl (hG.arity iv ⟨_, List.mem_of_find?_eq_some hci, rfl⟩)) rfl nofun).elim
    | ctorInfo cv =>
      have : ctorArity? decls c = some (cv.numParams + cv.numFields) := by
        unfold ctorArity?; rw [show findConst decls c = findDecl decls c from rfl, hci]
      rw [hca] at this; cases this
    | recInfo rv => exact absurd hci (hnr rv)
    | quotInfo q =>
      cases hk : q.kind with
      | type => exact (hatom_of (.inl (hG.quotType c q hci hk)) (by simp [OwnRules, hk]) nofun).elim
      | ctor => have := hcq q hci; rw [hk] at this; cases this
      | lift => have := hcq q hci; rw [hk] at this; cases this
      | ind => exact ⟨rfl, .inr ⟨q, rfl, hk⟩⟩

/-- `visitApp (k + 1)` at the pure backend, on a spine the oracle keeps whose head is no constant
with a rule of its own (`hplain`), from `visitExpr` and `visitMutual` at the fuels up to `k`
(`ih`): a marking `MarkOf.app` (the head no constant) is erased head first by `visitExpr`, a
marking `MarkOf.constApp` by `visitConst` on the head, which is no atom (`AtomBoxed`), no theorem
and no recursor, and registered by `visitMutual` if it is new; then the arguments
(`visitAppArgs_spec`). Adapted from `ML-V Core/Steps.lean:1487`. Reference: the `tApp` and
`tConst` cases of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitApp_spec (hG : CoreEnv view cfg decls) {k : Nat}
    (ih : StepIH view cfg decls k) {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local}
    {Sc : Name → Prop} {e ê : Expr} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r : LBTerm} (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e)
    (hsc : ScopeOK decls Sc) (hocc : ∀ d, nameOccurs d e = true → Sc d) (hnp : NatPlain cfg e)
    (hrs : RecShaped cfg decls e) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false)
    (hshape : e.isApp = true ∨ ∃ c us, e = .const c us)
    (hplain : ∀ c us, e.getAppFn = .const c us → markArity? decls cfg c = none)
    (hrun : (visitApp (m := PureM) (k + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  have hor' := oracle_agree hG.closed hR he hor
  cases hm with
  | erase h₁ => rw [h₁] at hor'; cases hor'
  | @app _ f fM as âs _ _ hfa hfc hf hlen hall =>
    obtain ⟨⟨hSf, hof, hnf, hrf⟩, hA⟩ := spine_premises ⟨he, hocc, hnp, hrs⟩
    have hfa' : (renFV ρ f).isApp = false := by cases f <;> first | rfl | cases hfa
    have hfc' : ∀ c us, renFV ρ f ≠ .const c us := by
      intro c us h
      cases f <;> simp only [renFV, reduceCtorEq] at h
      cases h
      exact hfc _ _ rfl
    rw [renFV_mkAppN, visitApp] at hrun
    split at hrun
    · rename_i c us hc
      rw [getAppFn_mkAppN_of hfa'] at hc
      exact absurd hc (hfc' c us)
    rw [withApp_mkAppN hfa', runPure_bind] at hrun
    obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, htf, hrun⟩ := ok_of_bind hrun
    have ⟨herf, hcf, hdf, hgf⟩ :=
      ih.expr k (Nat.le_refl _) f hctx hR hSf hsc hof hnf hrf hok hf htf
    cases k with
    | zero => rw [visitAppArgs] at hrun; cases hrun
    | succ i =>
    have ⟨her, hc0, hdeps, hgr⟩ := visitAppArgs_spec (fun e => ih.expr i (by omega) e) hctx hsc
      (hR.mono hgf.next) hA hlen hall hgf.inv herf hcf hdf hrun
    refine ⟨?_, hc0, hdeps, hgf.trans hgr⟩
    rw [renFV_mkAppN]; exact her
  | @constApp _ c us as âs _ hma hlen hall =>
    obtain ⟨⟨-, hoc, -, hrc⟩, hA⟩ := spine_premises (f := .const c us) ⟨he, hocc, hnp, hrs⟩
    have hS : Sc c := hoc c (by simp [nameOccurs])
    have hren : renFV ρ (mkAppN (.const c us) as.toArray) =
        mkAppN (.const c us) (as.map (renFV ρ)).toArray := renFV_mkAppN ρ _ as
    obtain ⟨hat, hspec, hnr, hcs, hem⟩ :=
      constHead_ok hG hsc hS hma hrc (by rw [← hren]; exact hor)
    obtain ⟨hcs', hca, hcq, -⟩ := markArity?_none hma
    rw [hren, visitApp] at hrun
    simp only [getAppFn_mkAppN_const] at hrun
    cases k with
    | zero => rw [visitConstApp] at hrun; cases hrun
    | succ j =>
    rw [visitConstApp, withApp_mkAppN rfl] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
        EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hcs], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
        EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
        EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((findConst decls c, st), ps) from rfl, ok_bind'] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i q _ _ _ heq
      cases hcq _ heq
    · rename_i q _ _ _ heq
      cases hcq _ heq
    · rename_i rv heq
      exact absurd heq (hnr rv)
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := ok_of_bind hrun
    cases j with
    | zero => rw [visitConst] at hf; cases hf
    | succ i =>
    obtain ⟨rfl, hdf, hgf⟩ := visitConst_spec (fun m hm c => ih.mutDecl m (by omega) c) hctx hsc
      hS hem hcs hok hf
    have ⟨her, hc0, hdeps, hgr⟩ := visitAppArgs_spec (F := .const c us)
      (fun e => ih.expr i (by omega) e) hctx hsc (hR.mono hgf.next) hA hlen hall hgf.inv
      (.const hat hspec hnr) rfl hdf hrun
    refine ⟨?_, hc0, hdeps, hgf.trans hgr⟩
    rw [renFV_mkAppN]; exact her
  | @special _ c us _ _ _ as _ hma =>
    rw [hplain c us (getAppFn_mkAppN_const c us as)] at hma; cases hma
  | fvar | mdata | lam | letE | proj | litZero | litSucc => simp [Expr.isApp] at hshape

/-- The `app` step, through `visitApp_spec`, on a spine whose head is no constant with a rule of
its own. Adapted from `ML-V Core/Steps.lean:1674`. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tApp` (`MR E/Extract.v:101`). -/
theorem visitExpr_app_step (hG : CoreEnv view cfg decls)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) {f a : Expr}
    (hplain : ∀ c us, (Expr.app f a).getAppFn = .const c us → markArity? decls cfg c = none) :
    ExprSpec view cfg decls (fuel + 1) (.app f a) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_spec hG ⟨fun m hm => ih.expr m (by omega),
    fun m hm => ih.mutDecl m (by omega)⟩ hctx hR he hsc hocc hnp hrs hok hm hor (.inl rfl) hplain hrun

/-- The `const` step: a constant without a rule of its own is erased as an application to no
argument (`visitApp_spec`). Adapted from `ML-V Core/Steps.lean:1694`. Reference: the `tConst` case
of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tConst` (`MR E/Extract.v:104`). -/
theorem visitExpr_const_step (hG : CoreEnv view cfg decls)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) {c : Name} {us : List Level}
    (hplain : markArity? decls cfg c = none) :
    ExprSpec view cfg decls (fuel + 1) (.const c us) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_spec hG ⟨fun m hm => ih.expr m (by omega),
    fun m hm => ih.mutDecl m (by omega)⟩ hctx hR he hsc hocc hnp hrs hok hm hor (.inr ⟨c, us, rfl⟩)
    (fun c' us' h => by cases h; exact hplain) hrun

end

/-! ## `visitMutual` -/

/-- At the pure backend, the traversal's `name_occurs` is `nameOccurs` (no `_unsafe_rec`
stripping). Copy of `ML-V Core/Steps.lean:1977`. -/
theorem name_occurs_eq : name_occurs (m := PureM) = nameOccurs := by
  funext n e
  induction e <;> simp [name_occurs, nameOccurs, remove_unsafe_rec, *]
  rfl

/-- A run of `x` at the pure backend that keeps the registered constants and inductive types, the
λ□ environment and the counter: the inlining bookkeeping of `visitMutual`. Copy of
`ML-V Core/Steps.lean:1984`. -/
def KeepsCG (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') →
    st'.constants = st.constants ∧ st'.inductives = st.inductives ∧ st'.gdecls = st.gdecls ∧
      ps' = ps

section
variable {pc : PureCtx}

theorem KeepsCG.pure {α : Type} (a : α) : KeepsCG pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.get : KeepsCG pc (MonadState.get : EraseT PureM ErasureState) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.modify {f : ErasureState → ErasureState}
    (hf : ∀ s, (f s).constants = s.constants ∧ (f s).inductives = s.inductives ∧
      (f s).gdecls = s.gdecls) :
    KeepsCG pc (_root_.modify f : EraseT PureM PUnit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨(hf st).1, (hf st).2.1, (hf st).2.2, rfl⟩

theorem KeepsCG.log (m : String) :
    KeepsCG pc (liftM (Backend.log (m := PureM) m) : EraseT PureM Unit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.isInstance (n : Name) :
    KeepsCG pc (liftM (Backend.isInstance (m := PureM) n) : EraseT PureM Bool) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.bind {α β : Type} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : KeepsCG pc x) (hk : ∀ a, KeepsCG pc (k a)) : KeepsCG pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := ok_of_bind h
  obtain ⟨c1, i1, g1, p1⟩ := hx _ _ _ _ _ _ h1
  obtain ⟨c2, i2, g2, p2⟩ := hk a _ _ _ _ _ _ h2
  exact ⟨c2.trans c1, i2.trans i1, g2.trans g1, p2.trans p1⟩

theorem KeepsCG.read_bind {α : Type} {k : TravCtx → EraseT PureM α}
    (hk : ∀ c, KeepsCG pc (k c)) : KeepsCG pc (read >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_read_bind] at h
  exact hk tc _ _ _ _ _ _ h

theorem KeepsCG.ite {α : Type} {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : c → KeepsCG pc a) (hb : ¬c → KeepsCG pc b) : KeepsCG pc (if c then a else b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

end

/-- `StateOK` reads only the registered constants and inductive types and the λ□ environment.
Copy of `ML-V Core/Steps.lean:2040`. -/
theorem StateOK.congr {cert : BoxCert} {σ : EvalEnv} {st st' : ErasureState}
    (h : StateOK cert σ st) (hc : st'.constants = st.constants) (hi : st'.inductives = st.inductives)
    (hg : st'.gdecls = st.gdecls) : StateOK cert σ st' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hc, hg]; exact h1, by rw [hi, hg]; exact h2, by rw [hc, hi, hg]; exact h3,
    by rw [hi]; exact h4, by rw [hg]; exact h5⟩

/-- `Quot.ind`'s kername is no λ□ block name: it is not a root kername. Adapted from
`ML-V Core/Steps.lean:2055`. -/
theorem knNotBlock_quotInd {σ : EvalEnv} : KnNotBlock σ ``Quot.ind := by
  intro iv _ h
  have := congrArg Kername.mp h
  simp [toKername, toModPath, blockKername, mutualBlockKername, rootKername] at this

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The declaration that `PureM.declInfo?` returns for a declaration `ci` of the closure: `ci`
itself when it has no compiled pre-definition, and otherwise a definition of the same block with a
value. -/
theorem declInfo_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {cfg' : ErasureConfig}
    {c : Name} {ci : ConstantInfo} (hci : findDecl decls c = some ci) :
    ∃ ci₀, (liftM (Backend.declInfo? (m := PureM) cfg' c) :
        EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((some ci₀, st), ps) ∧ ci₀.all = ci.all ∧
      ((preDef? view cfg' ci).isNone = true → ci₀ = ci) ∧
      (ci₀.value? (allowOpaque := true) = none → ci.value? (allowOpaque := true) = none) := by
  have hf : findConst decls c = some ci := hci
  refine ⟨(match (generalizing := false) ci, preDef? view cfg' ci with
    | .defnInfo d, some pre => .defnInfo { d with value := pre }
    | ci, _ => ci : ConstantInfo), ?_, ?_⟩
  · show Except.ok (((findConst decls c).map fun (ci : ConstantInfo) => match ci, preDef? view cfg' ci with
        | .defnInfo d, some pre => ConstantInfo.defnInfo { d with value := pre }
        | ci, _ => ci, st), ps) = _
    rw [hf]; rfl
  · rcases hpd : preDef? view cfg' ci with _ | p
    · cases ci <;> exact ⟨rfl, fun _ => rfl, id⟩
    · cases ci with
      | defnInfo d => exact ⟨rfl, fun h => by simp at h, fun h => by cases h⟩
      | _ => simp [preDef?] at hpd

/-- The `visitMutual` step: on a constant without value, or remapped (`axiomatized`), `addAxiom`
registers a λ□ axiom (`addAxiom_ok`); on a definition or an opaque, the value (no compiled
pre-definition, `NoPreDefs`; of a one-member block and without its own constant, `CoreEnv.value`,
so `visitMutual` takes its non-recursive branch) is erased in the empty context, which `RenOK`
relates to the caller's locals with no variable in scope, and registered with its erasure
(`StateOK.register`): an erasure of every marking of the value, of which there is one
(`ValuesMarkedOf`), closed and without free variables (`Erases.noFVar`); the traversal cannot
register the constant while it erases the value, whose scope does not hold it. The inlining
bookkeeping keeps the state invariant (`KeepsCG`). Adapted from `ML-V Core/Steps.lean:2418`,
without its fixpoint branch. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in
the `ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`);
`erase_global_deps_fresh` (`MR E/ErasureFunctionProperties.v:1206`). -/
theorem visitMutual_step (hG : CoreEnv view cfg decls) (hmk : ValuesMarkedOf decls cfg)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) {c : Name} :
    MutualSpec view cfg decls (fuel + 1) c := by
  intro Sc st tc ps st' ps' hsc hS hcfg hemc hcs hok hnew hrun
  obtain ⟨ci, hci, hthm, hem⟩ := hemc
  have hmem : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hname : ci.name = c := by simpa using List.find?_some hci
  have hnb : KnNotBlock (evalEnvOf view cfg decls) c := by
    rcases hem with hem | ⟨q, rfl, hk⟩
    · exact knNotBlock_of_emits hG.bn hci hem
    · rw [hG.quotInd c q hci hk]; exact knNotBlock_quotInd
  have hall : ci.all.length = 1 := by
    cases hv : ci.value? (allowOpaque := true) with
    | some v => exact (hG.value c ci v hci hv hthm hcs).1
    | none =>
      rcases hem with hem | ⟨q, rfl, -⟩
      · cases ci <;> simp_all [ConstantInfo.value?, EmitsConst, ConstantInfo.all]
      · rfl
  -- an axiom: `addAxiom` registers it
  have haxiom : ∀ {sd : ErasureState}, sd.constants = st.constants →
      sd.inductives = st.inductives → sd.gdecls = st.gdecls →
      (ci.value? (allowOpaque := true) = none ∨ axiomatized view cfg ci = true) →
      (addAxiom (m := PureM) c).runPure sd tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' ∧
        ∃ kn, st'.constants[c]? = some kn := by
    intro sd hcd hid hgd hax hrun
    obtain ⟨st'', hrun'', hc'', hok'', hext''⟩ :=
      addAxiom_ok (StateOK.congr hok hcd hid hgd) hG.inj hci hnb (by rw [hcd]; exact hnew) hax
    rw [hrun''] at hrun
    cases hrun
    refine ⟨⟨hok'', by rw [← hgd]; exact hext'', Nat.le_refl _, fun c' kn h0 h1 => ?_⟩,
      toKername c, by rw [hc'']; exact Std.HashMap.getElem?_insert_self⟩
    rw [hc'', Std.HashMap.getElem?_insert] at h1
    split at h1
    · rename_i hcc
      rw [← beq_iff_eq.1 hcc]
      exact hS
    · rw [hcd, h0] at h1
      cases h1
  obtain ⟨ci₀, hdi, h0all, h0eq, h0val⟩ :=
    declInfo_run (view := view) (tc := tc) (st := st) (ps := ps) (cfg' := tc.config) hci
  rw [hcfg] at h0eq
  have hall₀ : ci₀.all.length = 1 := by rw [h0all]; exact hall
  rw [visitMutual, runPure_read_bind, runPure_bind, hdi, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (getOrFail (m := PureM) (some ci₀)
    (toString "visitMutual: unknown constant " ++ toString c)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((ci₀, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  simp only [hall₀, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hrun
  generalize view.inlineAttr? c = ia at hrun
  rcases ia with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp only [↓reduceIte, Bool.false_eq_true] at hrun
  -- the `@[inline]` bookkeeping before the value touches only `inlinings`
  all_goals first
    | (rw [runPure_bind] at hrun
       replace hrun := ok_of_bind hrun
       obtain ⟨⟨⟨_, sa⟩, pa⟩, h1, hrun⟩ := hrun
       obtain ⟨ca, ia, ga, hpa⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pa
       try dsimp only at hrun
       rw [runPure_bind] at hrun
       replace hrun := ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pb⟩, h2, hrun⟩ := hrun
       obtain ⟨cb, ib, gb, hpb⟩ :=
         KeepsCG.modify (pc := ⟨decls, view⟩) (fun _ => ⟨rfl, rfl, rfl⟩) _ _ _ _ _ _ h2
       subst pb
       try dsimp only at hrun
       have hcb : sb.constants = st.constants := cb.trans ca
       have hib : sb.inductives = st.inductives := ib.trans ia
       have hgb : sb.gdecls = st.gdecls := gb.trans ga
       clear ca ia ga cb ib gb h1 h2)
    | (obtain ⟨sb, hsb⟩ : ∃ sb, sb = st := ⟨st, rfl⟩
       rw [← hsb] at hrun
       have hcb : sb.constants = st.constants := by rw [hsb]
       have hib : sb.inductives = st.inductives := by rw [hsb]
       have hgb : sb.gdecls = st.gdecls := by rw [hsb]
       clear hsb)
  all_goals
    rw [runPure_bind, show (liftM (Backend.isExtern (m := PureM) c) : EraseT PureM Bool).runPure sb
      tc ⟨decls, view⟩ ps = .ok ((view.isExtern c, sb), ps) from rfl, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_read_bind, hcfg] at hrun
  all_goals
    rcases hv : ci₀.value? (allowOpaque := true) with _ | v <;> cases hie : view.isExtern c <;>
      cases hext : cfg.1 <;> simp only [hv, hie, hext] at hrun
  all_goals first
    | (rw [runPure_bind] at hrun
       replace hrun := ok_of_bind hrun
       obtain ⟨⟨⟨_, sd⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, id, gd, hpd⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pd
       try dsimp only at hrun
       exact haxiom (cd.trans hcb) (id.trans hib) (gd.trans hgb)
         (by first
           | exact .inl (h0val hv)
           | exact .inr (by simp [axiomatized, hall, hname, hie, hext] <;> rfl)) hrun)
    | (rw [runPure_bind] at hrun
       replace hrun := ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, id, gd, hpd⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pd
       try dsimp only at hrun
       replace hcb := cd.trans hcb
       replace hib := id.trans hib
       replace hgb := gd.trans hgb
       clear cd id gd h1)
    | skip
  -- a definition or an opaque: its value is erased in the empty context, then registered
  all_goals
    have hax : axiomatized view cfg ci = false := by
      simp [axiomatized, hall, hname, hie, hext] <;> rfl
    have h0 : ci = ci₀ := (h0eq (hG.nopre ci hmem hax)).symm
    subst h0
    obtain ⟨-, Sc', hsc', hvS', hcS'⟩ := hG.value c ci v hci hv hthm hcs
    have hno : name_occurs (m := PureM) c v = false := by
      rw [name_occurs_eq]
      cases h : nameOccurs c v
      · rfl
      · exact absurd (hvS' c h) hcS'
    simp only [Option.getD_some, hno, Bool.not_false, ↓reduceIte] at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨e0, s0⟩, p0⟩, hg0, hrun⟩ := ok_of_bind hrun
    cases hg0
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨t, st₂⟩, ps₂⟩, hW, hrun⟩ := ok_of_bind hrun
    rw [runPure_withReader, runPure_read_bind, runPure_bind] at hW
    obtain ⟨⟨⟨v₁, s₁⟩, p₁⟩, hp, hW⟩ := ok_of_bind hW
    cases hp
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨_, st₃⟩, ps₃⟩, hm, hrun⟩ := ok_of_bind hrun
    cases hm
    obtain ⟨hc', hi', hg', hps⟩ := (by
      repeat' first
        | with_reducible_and_instances first
          | exact KeepsCG.pure _
          | exact KeepsCG.get
          | exact KeepsCG.log _
          | exact KeepsCG.isInstance _
          | refine KeepsCG.modify fun _ => ⟨rfl, rfl, rfl⟩
          | refine KeepsCG.read_bind fun _ => ?_
          | refine KeepsCG.bind ?_ fun _ => ?_
          | refine KeepsCG.ite (fun _ => ?_) (fun _ => ?_) : KeepsCG ⟨decls, view⟩ _) _ _ _ _ _ _ hrun
    dsimp only at hW
    have hread : ReadExpr decls ci v := by
      cases ci with
      | defnInfo dv =>
        cases hv
        refine .inr (.inl ⟨dv, rfl, rfl, ?_⟩)
        have hn' : dv.name = c := hname
        simp [casesOnOf?, hn', hcs]
      | opaqueInfo o => cases hv; exact .inr (.inr ⟨o, rfl, rfl⟩)
      | thmInfo _ => cases hthm
      | _ => cases hv
    have hvcl : FVarsIn (fun _ => False) v := (closed_find hG.closed hci).2 v hv
    have hctx0 : CtxOK cfg { lctx := tc.lctx, locals := tc.locals, config := tc.config, decl := c } :=
      ⟨hcfg, rfl⟩
    have hR0 : RenOK id (fun _ => False) [] tc.locals ps.next :=
      ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩
    have hW' : (visitExpr (m := PureM) fuel (renFV id v)).runPure sb
        { lctx := tc.lctx, locals := tc.locals, config := tc.config, decl := c } ⟨decls, view⟩ ps =
          .ok ((t, st₂), ps₂) := by rw [renFV_id]; exact hW
    have hoccS : ∀ d, nameOccurs d v = true → Sc d := by
      obtain ⟨ci₁, hci₁, hval₁⟩ := hsc c hS
      rw [hci] at hci₁
      cases hci₁
      exact hval₁ v hv hthm hcs
    have hokb := StateOK.congr hok hcb hib hgb
    obtain ⟨vM₀, hvM₀⟩ := hmk ci hmem v hv
    have hspec : ∀ (Sc₀ : Name → Prop), ScopeOK decls Sc₀ → (∀ d, nameOccurs d v = true → Sc₀ d) →
        ∀ {vM}, MarkOf decls cfg [] v vM → _ := fun Sc₀ hsc₀ hocc₀ vM hvM =>
      ih.expr fuel (Nat.le_refl _) v hctx0 hR0 hvcl hsc₀ hocc₀ (hG.npd ci hmem v hread)
        (hG.recShaped ci hmem v hread) hokb (ê := vM) hvM hW'
    obtain ⟨her₀, hc0, hdeps, hgr⟩ := hspec Sc hsc hoccS hvM₀
    obtain ⟨-, -, -, hgr'⟩ := hspec Sc' hsc' hvS' hvM₀
    have hnew₂ : st₂.constants[c]? = none := by
      cases h : st₂.constants[c]? with
      | none => rfl
      | some kn => exact (hcS' (hgr'.scope c kn (by rw [hcb]; exact hnew) h)).elim
    have hd : ErasesDecl noCert (evalEnvOf view cfg decls) ci ⟨some t⟩ := by
      unfold ErasesDecl
      rw [hv]
      refine .inr ⟨hax, ⟨vM₀, hvM₀⟩, t, rfl, fun vM hvM => ?_⟩
      have := (hspec Sc hsc hoccS hvM).1
      rwa [renFV_id] at this
    obtain ⟨hok₃, hext₃⟩ := hgr.inv.register hG.inj hci hnb hnew₂ hd fun b hb => by
      cases hb
      rw [renFV_id] at her₀
      exact ⟨hdeps, hc0, Erases.noFVar her₀
        (MarkOf.fvarsIn hG.closed hvM₀ (S := fun _ => False) (fun _ h => h.elim) hvcl)⟩
    refine ⟨⟨StateOK.congr hok₃ hc' hi' hg', ?_, hps ▸ hgr.next, ?_⟩, toKername c, ?_⟩
    · rw [hg', ← hgb]
      exact LenvExt.trans hgr.ext hext₃
    · intro c' kn h0 h1
      rw [hc'] at h1
      change (st₂.constants.insert c (toKername c))[c']? = some kn at h1
      rw [Std.HashMap.getElem?_insert] at h1
      split at h1
      · rename_i hcc
        rw [← beq_iff_eq.1 hcc]
        exact hS
      · exact hgr.scope c' kn (by rw [hcb]; exact h0) h1
    · rw [hc']
      exact Std.HashMap.getElem?_insert_self

end

end Steps

end EraseProof
