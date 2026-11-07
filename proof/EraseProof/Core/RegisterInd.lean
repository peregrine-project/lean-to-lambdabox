import EraseProof.Oracle.Sound
import EraseProof.Metatheory.NoConf
import EraseProof.Core.State
import EraseProof.Core.Frame

/-!
# The propositional flag of a registered inductive

`register_inductive` (`LeanToLambdaBox/Erasure.lean:463`) sets a λ□ inductive body's
`propositional` flag to `Pure.isPropFormerType` of the Lean inductive's declared type, a syntactic
test: the sort reached through Π-binders and metadata is `Sort 0` as written. `ErasesInd` asks the
flag to be `PropInductive`, a semantic fact: the Metalean block's level is `0` in Metalean's level
quotient (`ML Level/Quot/Basic.lean:16`). The two agree on the inductives of the fragment
(`Pure.isPropFormerType_iff`): Lean's kernel accepts an inductive at `Sort (max 0 0)`, which is
`PropInductive` while the test answers `false`, and the fragment test (`PhaseIDecl`, checked by
`Erasure.sortDecided`) excludes it, admitting only a sort written `Prop`, a never-zero sort, or a
sort that is not zero under some assignment.

The semantic half reads the block's level off `ConstTyped`: the inductive's η-term is typed at
`Π (params) (indices), Sort level` and at the translation of the declared type, a Π-telescope over
the translated sort, so the two sorts agree by Π and sort injectivity (`LShape.level_eq`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace RegisterInd

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ : Nat}

/-- A sort `l` under Π-binders, read from the outermost binder. -/
inductive LShape (l : Metalean.Level ℓ) : {n : Nat} → Metalean.Expr ζ ℓ n → Prop
  | sort {n : Nat} : LShape l (n := n) (.sort l)
  | forallE {n : Nat} {A : Metalean.Expr ζ ℓ n} {C : Metalean.Expr ζ ℓ (n + 1)} :
      LShape l C → LShape l (.forallE A C)

/-- Two equal Π-telescopes over sorts end in the same sort (Π and sort injectivity,
`MR pcuic/theories/PCUICConversion.v:326`). -/
theorem LShape.level_eq (hE : EnvWF E) {l₁ l₂ : Metalean.Level ℓ} {n : Nat}
    {X Y : Metalean.Expr ζ ℓ n} (h₁ : LShape l₁ X) :
    ∀ {Γ : Metalean.Ctx ζ ℓ 0 n}, E[Γ] ⊢ ok → LShape l₂ Y → E[Γ] ⊢ X ≡ Y typ → l₁ = l₂ := by
  induction h₁ with
  | sort =>
    intro Γ hΓ h₂ h
    cases h₂ with
    | sort => exact TypeEq.sort_inj hE hΓ h
    | forallE _ => exact absurd h (TypeEq.sort_ne_forallE hE hΓ)
  | @forallE m A C _ ih =>
    intro Γ hΓ h₂ h
    cases h₂ with
    | sort => exact absurd h.symm (TypeEq.sort_ne_forallE hE hΓ)
    | forallE h₂ =>
      obtain ⟨-, hC⟩ := TypeEq.forallE_inj hE hΓ h
      obtain ⟨_, hX⟩ := TypeEq.sort_uniq hE hΓ h
      obtain ⟨hA, -⟩ := hX.left.forallE_inv
      exact ih (.snoc hΓ hA) h₂ hC

/-- A Π-telescope over a shape is a shape. -/
theorem LShape.pi {l : Metalean.Level ℓ} :
    ∀ {k : Nat} (Θ : Metalean.Ctx ζ ℓ 0 k) {T : Metalean.Expr ζ ℓ k}, LShape l T →
      LShape l (Θ.pi T)
  | 0, .nil, _, h => h
  | _ + 1, .snoc Θ _, _, h => LShape.pi Θ (.forallE h)

/-- A λ-telescope over a typed body is typed at the Π-telescope over the body's type. -/
theorem lam_typed : ∀ {k : Nat} (Θ : Metalean.Ctx ζ ℓ 0 k) {body T : Metalean.Expr ζ ℓ k},
    E[Θ] ⊢ ok → E[Θ] ⊢ body : T → E[.nil] ⊢ Θ.lam body : Θ.pi T
  | 0, .nil, _, _, _, hb => hb
  | _ + 1, .snoc Θ A, _, _, hΘ, hb => by
    obtain ⟨_, hA⟩ := Tele.Forall.last hΘ
    obtain ⟨_, hT⟩ := hb.regular
    exact lam_typed Θ (Tele.Forall.init hΘ) (.lamDF hA hT hT hb hb)

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- The translation of a syntactic arity `Π x̄, Sort u` is a Π-telescope over the translated
sort. -/
theorem trM_arity : ∀ {A : Expr} {k : Nat} {u : Level} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {T : Metalean.Expr ζ lps.length n}, arityShape A = some (k, u) → TrM E B lps Γ Δ A T →
    ∃ l, TrLevel lps u = some l ∧ RegisterInd.LShape l T
  | .sort v, k, u, n, Γ, Δ, T, ha, h => by
    simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    generalize hx : Expr.sort v = x at h
    cases h with
    | sort hl => cases hx; exact ⟨_, hl, .sort⟩
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | .forallE x A b bi, k, u, n, Γ, Δ, T, ha, h => by
    simp only [arityShape, Option.map_eq_some_iff] at ha
    obtain ⟨⟨k', u'⟩, hb, he⟩ := ha
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    generalize hx : Expr.forallE x A b bi = X at h
    cases h with
    | forallE _ hB =>
      cases hx
      obtain ⟨l, hl, hs⟩ := trM_arity hb hB
      exact ⟨l, hl, .forallE hs⟩
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | .mdata d e, k, u, n, Γ, Δ, T, ha, h => by
    simp only [arityShape] at ha
    generalize hx : Expr.mdata d e = X at h
    cases h with
    | mdata h => cases hx; exact trM_arity ha h
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | .bvar _, _, _, _, _, _, _, ha, _ | .fvar _, _, _, _, _, _, _, ha, _
  | .mvar _, _, _, _, _, _, _, ha, _ | .const .., _, _, _, _, _, _, ha, _
  | .app .., _, _, _, _, _, _, ha, _ | .lam .., _, _, _, _, _, _, ha, _
  | .letE .., _, _, _, _, _, _, ha, _ | .lit _, _, _, _, _, _, _, ha, _
  | .proj .., _, _, _, _, _, _, ha, _ => by simp [arityShape] at ha

/-- The η-term (or node) of an inductive type at levels `ls`, translated from the bare constant,
is typed at a Π-telescope over the block's sort at `ls`. -/
theorem satTr_ind_shape (hE : EnvWF E) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {us : List Level}
    {t₀ T : Metalean.Expr ζ lps.length 0} (hsat : SatTr E lps (.ind η s) us [] t₀)
    (ht : E[.nil] ⊢ t₀ : T) :
    ∃ ls T₀, TrLevels lps us ι.nlevels = some ls ∧ E[.nil] ⊢ T ≡ T₀ typ ∧
      RegisterInd.LShape ((E.get η).block.level{ls}) T₀ := by
  generalize hargs : ([] : List (Metalean.Expr ζ lps.length 0)) = args at hsat
  cases hsat with
  | indSat ps is rest hls =>
    have hr : rest = [] := by
      have := congrArg List.length hargs
      simp only [List.length_nil, List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    obtain ⟨-, -, -, -, hT⟩ := ht.ind_inv
    exact ⟨_, _, hls, hT, .sort⟩
  | indEta hls hlt =>
    rename_i ls
    subst hargs
    have hB := (hE.entryWF η).block
    have hP : E[(E.get η).block.params{ls}] ⊢ ok := hB.paramClosedWF ls
    have hvars (p : Fin ι.nparams) : E[(E.get η).block.params{ls}] ⊢ Metalean.Expr.var p :
        (E.get η).block.paramType ls Metalean.Expr.var p := by
      simpa using hP.var p
    have hm := hB.motiveTele (s := s) hP hvars
    obtain ⟨u, _, hbody⟩ := Tele.Forall.last hm
    have hidx : Metalean.TeleWF E (fun _ => True) _ _ := Tele.Forall.init hm
    have hΘ : E[(E.get η).block.params{ls} ++ (E.get η).block.indexTele ls s Metalean.Subst.id] ⊢ ok :=
      hidx.appendCtxWF hP
    have hb' : E[(E.get η).block.params{ls} ++ (E.get η).block.indexTele ls s Metalean.Subst.id] ⊢
        (.ind η s ls (fun p => .var ⟨p.val, by omega⟩)
          fun i => .var ⟨ι.nparams + i.val, by omega⟩ :
            Metalean.Expr ζ lps.length (ι.nparams + ι.nindices s)) :
        .sort u := by
      convert hbody using 2
      all_goals first
        | rfl
        | funext p; simp [Metalean.Expr.wkN_eq_rename]; rfl
    obtain ⟨-, -, -, -, hu⟩ := hb'.ind_inv
    have hlam := lam_typed _ hΘ (hu.conv hb')
    have ht' : E[.nil] ⊢ Metalean.Frontend.indTerm (E.get η).block η s ls : T := ht
    simp only [Metalean.Frontend.indTerm, SatTyped.argTele_eq] at ht'
    exact ⟨ls, _, hls, Defeq.uniqTy hE SrcDefeq.nil_ok ht' hlam, LShape.pi _ .sort⟩

/-- The translation of a bare constant bound to an inductive type is its η-term (or node). -/
theorem satTr_of_const_ind {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {c : Name} {us : List Level} {t : Metalean.Expr ζ lps.length n}
    {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    (h : TrM E B lps Γ Δ (.const c us) t) (hb : B c = some (.ind η s)) :
    SatTr E lps (.ind η s) us [] t := by
  generalize he : Expr.const c us = e at h
  cases h with
  | const hb' _ => cases he; rw [hb] at hb'; cases hb'
  | special hb' _ hlen _ hsat =>
    obtain ⟨rfl, rfl, rfl⟩ := SrcDefeq.spine_const he.symm
    rw [hb] at hb'
    cases hb'
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    exact hsat
  | _ => cases he

/-- An inductive type of the program is bound to its Metalean sort, and the translation of the
sort `u` of its declared arity is the block's level at the inductive's own universe parameters. -/
theorem ProgEnv.ind_level {P : List ConstantInfo} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    {c : Name} {iv : InductiveVal} (hc : findDecl P c = some (.inductInfo iv)) {k : Nat}
    {u : Level} (ha : arityShape iv.type = some (k, u)) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (ls : Fin ι.nlevels → Metalean.Level iv.levelParams.length),
      B c = some (.ind η s) ∧
      TrLevels iv.levelParams (iv.levelParams.map .param) ι.nlevels = some ls ∧
      TrLevel iv.levelParams u = some ((E.get η).block.level{ls}) := by
  obtain ⟨ι, η, s, hb, -⟩ := henv.lookup_ind hc
  obtain ⟨-, -, T, t₀, hT, ht₀, hty⟩ := henv.lookup hE hc
  have hn : iv.name = c := (findDecl_eq_some hc).2
  obtain ⟨l, hl, hsT⟩ := trM_arity ha hT
  have hsat := satTr_of_const_ind ht₀ (hn ▸ hb)
  obtain ⟨ls, T₀, hls, hTT₀, hs₀⟩ := satTr_ind_shape hE hsat hty
  obtain rfl := hsT.level_eq hE SrcDefeq.nil_ok hs₀ hTT₀
  exact ⟨ι, η, s, ls, hb, hls, hl⟩

/-- At a declaration's own distinct universe parameters, a level is zero exactly when its
instance is. -/
theorem inst_params_zero {lps' : List Name} (hnd : lps'.Nodup) {k : Nat}
    {ls : Fin k → Metalean.Level lps'.length} (hls : TrLevels lps' (lps'.map .param) k = some ls)
    (L : Metalean.Level k) : L{ls} = .zero ↔ L = .zero := by
  obtain ⟨hk, hget⟩ := SrcDefeq.trLevels_params_nodup hnd hls
  refine ⟨fun h => Metalean.Level.ext fun ν => ?_, fun h => by rw [h]; rfl⟩
  have := congrArg (Metalean.Level.eval (fun p => ν (p.cast hk.symm))) h
  rw [Metalean.Level.eval_inst] at this
  simp only [Metalean.Level.eval_zero] at this ⊢
  rw [← this]
  congr 1
  funext i
  simp [hget]

/-- The universe parameters of a declaration, all at level `1`, translate as closed levels. -/
theorem trLevels_ones (xs : List Name) :
    ∃ ls, TrLevels [] (xs.map fun _ => Level.succ .zero) xs.length = some ls := by
  have h : ∀ m, (List.replicate m (Level.succ .zero)).mapM (TrLevel []) =
      some (List.replicate m (Metalean.Level.succ .zero : Metalean.Level 0)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, List.mapM_cons, TrLevel, ih]
  simp [TrLevels, h]

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}

/-- On a program inductive whose arity's sort `u` is written `Prop`, never zero, or not zero under
some assignment (the fragment's sorts), `PropInductive` is `u = Prop` as written. -/
theorem propInductive_iff {P : List ConstantInfo} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    {c : Name} {iv : InductiveVal} (hc : findDecl P c = some (.inductInfo iv)) {k : Nat}
    {u : Level} (ha : arityShape iv.type = some (k, u))
    (hu : u = .zero ∨ u.isNeverZero = true ∨ mayBeNonZero iv.levelParams u = true) :
    PropInductive E B c ↔ u = .zero := by
  obtain ⟨ι, η, s, ls, hb, hls, hl⟩ := ProgEnv.ind_level henv hE hc ha
  have hnd : iv.levelParams.Nodup := henv.levelParams_nodup (findDecl_eq_some hc).1
  have key : PropInductive E B c ↔ (E.get η).block.level = .zero := by
    constructor
    · rintro ⟨ι', η', s', hb', hz⟩
      rw [hb] at hb'
      cases hb'
      exact hz
    · exact fun h => ⟨ι, η, s, hb, h⟩
  rw [key, ← inst_params_zero hnd hls]
  constructor
  · intro hz
    rw [hz] at hl
    rcases hu with h | h | h
    · exact h
    · exact absurd rfl ((TrLevel.isNeverZero_iff hl).1 h (fun _ => 0))
    · obtain ⟨ones, hones⟩ := trLevels_ones iv.levelParams
      have h1 := TrLevel_instLevel hones hl
      exact absurd rfl ((TrLevel.isNeverZero_iff h1).1 h (fun _ => 0))
  · rintro rfl
    simp only [TrLevel, Option.some.injEq] at hl
    exact hl.symm

end

/-- On a syntactic arity, `whnf` only strips metadata. -/
theorem whnf_arity {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f : Nat} {T W : Expr} {k : Nat} {u : Level}, arityShape T = some (k, u) →
      Pure.whnf cx f ls T = .ok W → arityShape W = some (k, u) ∧ ∀ d e, W ≠ .mdata d e
  | 0, _, _, _, _, _, h => by simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, .sort v, W, k, u, ha, h => by
    simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨ha, fun _ _ h => by cases h⟩
  | f + 1, .forallE x A C bi, W, k, u, ha, h => by
    simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨ha, fun _ _ h => by cases h⟩
  | f + 1, .mdata d e, W, k, u, ha, h => by
    simp only [Pure.whnf] at h
    simp only [arityShape] at ha
    exact whnf_arity ha h
  | _ + 1, .bvar _, _, _, _, ha, _ | _ + 1, .fvar _, _, _, _, ha, _
  | _ + 1, .mvar _, _, _, _, ha, _ | _ + 1, .const .., _, _, _, ha, _
  | _ + 1, .app .., _, _, _, ha, _ | _ + 1, .lam .., _, _, _, ha, _
  | _ + 1, .letE .., _, _, _, ha, _ | _ + 1, .lit _, _, _, _, ha, _
  | _ + 1, .proj .., _, _, _, ha, _ => by simp [arityShape] at ha

/-- On a syntactic arity `Π x̄, Sort u`, `isPropFormerType` answers whether `u` is written
`Prop`. -/
theorem isPropFormerType_arity {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f : Nat} {T : Expr} {k : Nat} {u : Level} {b : Bool}, arityShape T = some (k, u) →
      Pure.isPropFormerType cx f ls T = .ok b → (b = true ↔ u = .zero)
  | 0, _, _, _, _, _, h => by
    simp [Pure.isPropFormerType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, T, k, u, b, ha, h => by
    simp only [Pure.isPropFormerType] at h
    obtain ⟨W, hW, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨haW, hnm⟩ := whnf_arity ha hW
    cases W with
    | sort v =>
      simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at haW
      obtain ⟨-, rfl⟩ := haW
      cases v <;> simp_all [pure, Except.pure]
    | forallE x A C bi =>
      simp only [arityShape, Option.map_eq_some_iff] at haW
      obtain ⟨⟨k', u'⟩, hC, he⟩ := haW
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact isPropFormerType_arity hC h
    | mdata d e => exact absurd rfl (hnm d e)
    | _ => simp [arityShape] at haW

end RegisterInd

open RegisterInd in
/-- The propositional flag that `register_inductive` computes is `PropInductive`, on every
inductive that passes the fragment test (`PhaseIDecl`, `Erasure.sortDecided`): the test is
syntactic (`Sort 0` as written), `PropInductive` is semantic (Metalean's block level is `0`), and
the fragment admits only sorts written `Prop`, never zero, or not zero under some assignment, on
which the two agree. Without the fragment test the equivalence fails: Lean's kernel accepts an
inductive at `Sort (max 0 0)`, a `PropInductive` on which the test answers `false`. Reference:
`Sort.is_propositional` of the inductive's sort in `MR E/ErasureFunction.v:1325
erase_one_inductive_body`, `isPropositional` (`MR P/PCUICFirstorder.v:109`). -/
theorem Pure.isPropFormerType_iff {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}
    {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {c : Name} {iv : InductiveVal} {b : Bool}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hc : findDecl P c = some (.inductInfo iv))
    (hph : PhaseIDecl view cfg decls (.inductInfo iv))
    (h : Pure.isPropFormerType cx fuel ls iv.type = .ok b) : b = true ↔ PropInductive E B c := by
  obtain ⟨-, -, ⟨k, u, ha, hu⟩, -⟩ := hph
  rw [isPropFormerType_arity ha h, propInductive_iff henv hE hc ha]
  rcases hu with h | h | ⟨h, -⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)


namespace RegisterInd

/-! ## Runs of the pure traversal -/

section
variable {α β : Type} {tc : TravCtx} {pc : PureCtx}

/-- Every successful run of `x` from a state satisfying `I` ends with a result and a state
satisfying `Q`. -/
def HT (tc : TravCtx) (pc : PureCtx) (I : ErasureState → Prop) (x : EraseT PureM α)
    (Q : α → ErasureState → Prop) : Prop :=
  ∀ st ps a st' ps', I st → x.runPure st tc pc ps = .ok ((a, st'), ps') → Q a st'

theorem HT.pure {I : ErasureState → Prop} {Q : α → ErasureState → Prop} {a : α}
    (h : ∀ s, I s → Q a s) : HT tc pc I (Pure.pure a) Q := by
  intro st ps a' st' ps' hI hr
  cases hr
  exact h _ hI

theorem HT.bind {I : ErasureState → Prop} {R : α → ErasureState → Prop}
    {Q : β → ErasureState → Prop} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : HT tc pc I x R) (hk : ∀ a, HT tc pc (R a) (k a) Q) : HT tc pc I (x >>= k) Q := by
  intro st ps b st' ps' hI hr
  rw [TravFrame.runPure_bind] at hr
  rcases hx' : x.runPure st tc pc ps with _ | ⟨⟨a, s₁⟩, ps₁⟩
  · rw [hx'] at hr; cases hr
  · rw [hx'] at hr
    exact hk a s₁ ps₁ b st' ps' (hx st ps a s₁ ps₁ hI hx') hr

theorem HT.mono {I I' : ErasureState → Prop} {Q Q' : α → ErasureState → Prop}
    {x : EraseT PureM α} (h : HT tc pc I x Q) (hI : ∀ s, I' s → I s)
    (hQ : ∀ a s, Q a s → Q' a s) : HT tc pc I' x Q' :=
  fun st ps a st' ps' h' hr => hQ _ _ (h st ps a st' ps' (hI _ h') hr)

theorem HT.get {I : ErasureState → Prop} :
    HT tc pc I (MonadState.get : EraseT PureM ErasureState) (fun a s => I s ∧ a = s) := by
  intro st ps a st' ps' hI hr
  cases hr
  exact ⟨hI, rfl⟩

theorem HT.modify {I : ErasureState → Prop} (f : ErasureState → ErasureState) :
    HT tc pc I (_root_.modify f : EraseT PureM PUnit) (fun _ s => ∃ s₀, I s₀ ∧ s = f s₀) := by
  intro st ps a st' ps' hI hr
  cases hr
  exact ⟨st, hI, rfl⟩

theorem HT.read_bind {I : ErasureState → Prop} {Q : α → ErasureState → Prop}
    {k : TravCtx → EraseT PureM α} (h : HT tc pc I (k tc) Q) : HT tc pc I (read >>= k) Q :=
  fun st ps a st' ps' hI hr => h st ps a st' ps' hI (by rwa [TravFrame.runPure_read_bind] at hr)

theorem HT.liftM {I : ErasureState → Prop} (x : PureM α) :
    HT tc pc I (_root_.liftM x : EraseT PureM α)
      (fun a s => I s ∧ ∃ ps ps', (x.run pc).run ps = .ok (a, ps')) := by
  intro st ps a st' ps' hI hr
  rw [TravFrame.runPure_liftM] at hr
  rcases hx : (x.run pc).run ps with _ | ⟨b, ps₁⟩
  · rw [hx] at hr; cases hr
  · rw [hx] at hr
    cases hr
    exact ⟨hI, ps, ps₁, hx⟩

theorem HT.throwM {I : ErasureState → Prop} {Q : α → ErasureState → Prop} (err : EraseError) :
    HT tc pc I (_root_.liftM (throw err : PureM α) : EraseT PureM α) Q :=
  fun _ _ _ _ _ _ hr => nomatch hr

theorem HT.getConst {I : ErasureState → Prop} (n : Name) :
    HT tc pc I (getConst (m := PureM) n) (fun ci s => I s ∧ findConst pc.decls n = some ci) := by
  unfold Erasure.getConst
  refine HT.bind (R := fun r s => I s ∧ r = findConst pc.decls n) ?_ fun r => ?_
  · intro st ps a st' ps' hI hr
    cases hr
    exact ⟨hI, rfl⟩
  · split
    · next ci => exact HT.pure fun s hs => ⟨hs.1, hs.2.symm⟩
    · exact HT.throwM _

theorem HT.getOrFail {γ : Type} [Inhabited γ] {I : ErasureState → Prop} (o : Option γ)
    (msg : String) : HT tc pc I (getOrFail (m := PureM) o msg) (fun a s => I s ∧ o = some a) := by
  cases o with
  | some a => exact HT.pure fun s hs => ⟨hs, rfl⟩
  | none => exact HT.throwM _

/-- `List.mapM` with an invariant indexed by the processed prefix of the list `L`. -/
theorem HT.mapM {f : α → EraseT PureM β} {P : α → β → Prop}
    {I : List α → ErasureState → Prop} {L : List α}
    (hf : ∀ pre a rest, pre ++ a :: rest = L →
      HT tc pc (I pre) (f a) (fun b s => I (pre ++ [a]) s ∧ P a b)) :
    ∀ (l pre : List α), pre ++ l = L →
      HT tc pc (I pre) (l.mapM f) (fun bs s => I L s ∧ List.Forall₂ P l bs)
  | [], pre, h => by
    rw [List.mapM_nil]
    exact HT.pure fun s hs => ⟨by rw [List.append_nil] at h; exact h ▸ hs, .nil⟩
  | a :: l, pre, h => by
    rw [List.mapM_cons]
    refine HT.bind (hf pre a l h) fun b => ?_
    intro st ps bs st' ps' ⟨hI, hP⟩ hr
    rw [TravFrame.runPure_bind] at hr
    rcases hl : (l.mapM f).runPure st tc pc ps with _ | ⟨⟨bs', s₁⟩, ps₁⟩
    · rw [hl] at hr; cases hr
    · rw [hl] at hr
      cases hr
      obtain ⟨hI', hF⟩ := HT.mapM hf l (pre ++ [a]) (by simpa using h) st ps bs' s₁ ps₁ hI hl
      exact ⟨hI', .cons hP hF⟩

theorem HT.of_fact {I : ErasureState → Prop} {Q : α → ErasureState → Prop} {p : Prop}
    {x : EraseT PureM α} (h : p → HT tc pc I x Q) : HT tc pc (fun s => I s ∧ p) x Q :=
  fun st ps a st' ps' ⟨hI, hp⟩ hr => h hp st ps a st' ps' hI hr

theorem HT.any {I : ErasureState → Prop} {x : EraseT PureM α} :
    HT tc pc I x (fun _ _ => True) :=
  fun _ _ _ _ _ _ _ => trivial

theorem HT.pure_eq {I : ErasureState → Prop} {a : α} :
    HT tc pc I (Pure.pure a) (fun b s => I s ∧ b = a) :=
  HT.pure fun _ h => ⟨h, rfl⟩

theorem isExtern_run {n : Name} {ps ps' : PureState} {a : Bool}
    (h : ((Backend.isExtern (m := PureM) n).run pc).run ps = .ok (a, ps')) :
    a = pc.view.isExtern n := by
  cases h
  rfl

theorem pureM_isPropFormerType_run (e : Expr) (ps : PureState) :
    ((PureM.isPropFormerType e).run pc).run ps =
      (Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e).map (·, ps) := by
  unfold PureM.isPropFormerType
  have hr : ReaderT.run (read : PureM PureCtx) pc = Pure.pure pc := rfl
  simp only [ReaderT.run_bind, hr, pure_bind]
  rcases Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e with err | b
  · rfl
  · rfl

theorem isPropFormerType_run (e : Expr) (ps : PureState) :
    ((Backend.isPropFormerType (m := PureM) e).run pc).run ps =
      (Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e).map (·, ps) :=
  pureM_isPropFormerType_run e ps

end

/-! ## The run of `register_inductive` -/

/-- The λ□ body that `register_inductive` builds for the type `p.1` at position `p.2` of its
block: one constructor per Lean constructor, each with all its fields, and the flag of
`Pure.isPropFormerType` on the type's declared type. -/
def BodyOK (σ : EvalEnv) (p : Name × Nat) (ob : OneInductiveBody) : Prop :=
  ∃ ivn, findDecl σ.decls p.1 = some (.inductInfo ivn) ∧ ob.ctors.length = ivn.ctors.length ∧
    (∀ (k : Nat) cn, ivn.ctors[k]? = some cn → ∃ (cv : ConstructorVal) (cb : ConstructorBody),
      findDecl σ.decls cn = some (.ctorInfo cv) ∧ ob.ctors[k]? = some cb ∧
      cb.nargs = cv.numFields) ∧
    Pure.isPropFormerType ⟨σ.decls⟩ oracleFuel [] ivn.type = .ok ob.propositional

/-- What `register_inductive` builds for the constructor `cn`: its λ□ body with all its fields and
the mask that keeps every field. -/
def CtorOK (pc : PureCtx) (cn : Name) (out : ConstructorBody × ConstructorArgMask) : Prop :=
  ∃ cv, findConst pc.decls cn = some (.ctorInfo cv) ∧ out.1.nargs = cv.numFields ∧
    out.2 = Array.replicate cv.numFields .keep

/-- The state after `register_inductive` has registered the types `pre` of a block named `bk`,
from the state `st₀`: constants and λ□ environment unchanged, every type of `pre` registered at
its position with masks that keep every field, the other entries unchanged. -/
def Registered (σ : EvalEnv) (st₀ : ErasureState) (bk : Kername) (pre : List (Name × Nat))
    (s : ErasureState) : Prop :=
  s.constants = st₀.constants ∧ s.gdecls = st₀.gdecls ∧
    (∀ T, (∀ p ∈ pre, p.1 ≠ T) → s.inductives[T]? = st₀.inductives[T]?) ∧
    ∀ p ∈ pre, ∃ ivn masks, findDecl σ.decls p.1 = some (.inductInfo ivn) ∧
      s.inductives[p.1]? = some (⟨bk, p.2⟩, masks) ∧ KeepMasks σ ivn masks

/-- The element at a position of the first list of `Forall₂` has a partner at that position. -/
theorem forall₂_get {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ {k : Nat} {a : α}, l[k]? = some a →
      ∃ b, l'[k]? = some b ∧ R a b := by
  induction h with
  | nil => intro k a h; simp at h
  | cons hab _ ih =>
    intro k a h
    cases k with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ k => simpa using ih (by simpa using h)

/-- In a list of distinct names with their positions, a name differs from every name before
it. -/
theorem zipIdx_prefix_ne {l : List Name} (hnd : l.Nodup) {pre rest : List (Name × Nat)}
    {n : Name} {j : Nat} (h : pre ++ (n, j) :: rest = l.zipIdx) : ∀ p ∈ pre, p.1 ≠ n := by
  have h2 := congrArg (List.map Prod.fst) h
  rw [List.zipIdx_map_fst] at h2
  rw [← h2, List.map_append, List.map_cons] at hnd
  intro p hp heq
  exact (List.nodup_append.1 hnd).2.2 p.1 (List.mem_map_of_mem hp) n List.mem_cons_self heq

section
variable {tc : TravCtx} {pc : PureCtx}

/-- A run of `register_inductive` at the pure backend: either the type is registered and the
state is unchanged, or the whole block is registered at once (`Registered`), each type with a body
that `BodyOK` describes, and the block is consed to the λ□ environment. -/
theorem register_inductive_run {σ : EvalEnv} {iv : InductiveVal} (hdecls : pc.decls = σ.decls)
    (hirr : tc.config.remove_irrel_constr_args = false)
    (hext : ∀ cn cv, findDecl σ.decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → pc.view.isExtern cn = false)
    (hnd : iv.all.Nodup) (st₀ : ErasureState) :
    HT tc pc (· = st₀) (register_inductive (m := PureM) iv) (fun r s =>
      (st₀.inductives[iv.name]? = some r ∧ s = st₀) ∨
      (st₀.inductives[iv.name]? = none ∧ ∃ s₁ bodies,
        Registered σ st₀ (mutualBlockKername iv.all) iv.all.zipIdx s₁ ∧
        List.Forall₂ (BodyOK σ) iv.all.zipIdx bodies ∧ s₁.inductives[iv.name]? = some r ∧
        s = { s₁ with gdecls := s₁.gdecls.cons (mutualBlockKername iv.all,
          .inductiveDecl { npars := iv.numParams, bodies }) })) := by
  rw [Erasure.register_inductive]
  refine HT.bind HT.get fun s => ?_
  split
  · next iid hiid =>
    refine HT.pure fun s' ⟨h1, h2⟩ => .inl ⟨?_, ?_⟩
    · subst h1 h2; rwa [Std.HashMap.get?_eq_getElem?] at hiid
    · exact h1
  · next hnone =>
    refine HT.bind (R := fun bodies s' => s = st₀ ∧
      Registered σ st₀ (mutualBlockKername iv.all) iv.all.zipIdx s' ∧
      List.Forall₂ (BodyOK σ) iv.all.zipIdx bodies) ?_ fun bodies => ?_
    · refine HT.mono (HT.mapM (I := fun pre s' => s = st₀ ∧
          Registered σ st₀ (mutualBlockKername iv.all) pre s') (P := BodyOK σ)
          (L := iv.all.zipIdx) (fun pre p rest hpre => ?_) _ [] rfl) ?_ ?_
      rotate_left
      · rintro s' ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => nomatch h⟩
      · rintro bodies' s' ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
      obtain ⟨n, j⟩ := p
      dsimp only
      refine HT.bind (HT.getConst _) fun ci => ?_
      split
      · next inf =>
        refine HT.of_fact fun hinf => ?_
        refine HT.bind (HT.mapM (I := fun _ s' => s = st₀ ∧
            Registered σ st₀ (mutualBlockKername iv.all) pre s') (P := CtorOK pc)
            (L := inf.ctors) (fun pre' cn rest' _ => ?_) _ [] rfl) fun outs => ?_
        · refine HT.bind (HT.liftM _) fun a => HT.of_fact fun ha => ?_
          obtain ⟨_, _, ha⟩ := ha
          have ha' := isExtern_run ha
          refine HT.read_bind ?_
          split
          · next hc =>
            refine HT.bind (HT.liftM _) fun _ => HT.bind HT.any fun _ => ?_
            refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              exfalso
              rw [Bool.and_eq_true, ha'] at hc
              have hx : tc.config.1 = .preferAxiom := by
                obtain ⟨-, h2⟩ := hc
                revert h2
                cases tc.config.1 <;> first | (intro; rfl) | (intro h; cases h)
              have := hext cn cv (hdecls ▸ hcv) hx
              rw [this] at hc
              exact Bool.false_ne_true hc.1
            · exact HT.throwM _
          · next hc =>
            refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              refine HT.read_bind ?_
              split
              · next hrm => exact absurd hrm (by simp [hirr])
              · refine HT.bind HT.pure_eq fun am => HT.of_fact fun ham => ?_
                subst ham
                refine HT.pure fun s' hs' => ⟨hs', cv, hcv, ?_, rfl⟩
                show Array.count ConstructorArgRelevance.keep
                  (Array.replicate cv.numFields ConstructorArgRelevance.keep) = cv.numFields
                generalize cv.numFields = m
                induction m with
                | zero => rfl
                | succ m ih => rw [Array.replicate_succ, Array.count_push, ih]; rfl
            · exact HT.throwM _
        · refine HT.of_fact fun hF => ?_
          have hne := zipIdx_prefix_ne hnd hpre
          have hinf' : findDecl σ.decls n = some (.inductInfo inf) := hdecls ▸ hinf
          have hcv : ∀ (k : Nat) cn, inf.ctors[k]? = some cn → ∃ cv out,
              findDecl σ.decls cn = some (.ctorInfo cv) ∧ outs[k]? = some out ∧
              out.1.nargs = cv.numFields ∧ out.2 = Array.replicate cv.numFields .keep := by
            intro k cn hk
            obtain ⟨out, hout, cv, hc, h1, h2⟩ := forall₂_get hF hk
            exact ⟨cv, out, hdecls ▸ hc, hout, h1, h2⟩
          have hlen := hF.length_eq
          have tail : ∀ projs : List ProjectionBody, HT tc pc
              (fun s₁ => s = st₀ ∧ Registered σ st₀ (mutualBlockKername iv.all) pre s₁)
              (_root_.modify (fun s : ErasureState => { s with
                  inductives := (s.inductives.insert n
                    ({ mutualBlockName := mutualBlockKername iv.all, idx := j }, outs.unzip.2)) }) >>=
                fun _ => (_root_.liftM (Backend.isPropFormerType (m := PureM) inf.type) :
                  EraseT PureM Bool) >>= fun propositional =>
                (Pure.pure { name := toString n, propositional, ctors := outs.unzip.1, projs } :
                  EraseT PureM OneInductiveBody))
              (fun b s₁ => (s = st₀ ∧
                Registered σ st₀ (mutualBlockKername iv.all) (pre ++ [(n, j)]) s₁) ∧
                BodyOK σ (n, j) b) := by
            intro projs
            refine HT.bind (HT.modify _) fun _ => HT.bind (HT.liftM _) fun b => HT.pure ?_
            rintro s₂ ⟨⟨s₁, ⟨rfl, hreg⟩, rfl⟩, _, _, hb⟩
            rw [isPropFormerType_run] at hb
            have hb' : Pure.isPropFormerType ⟨σ.decls⟩ oracleFuel [] inf.type = .ok b := by
              rw [← hdecls]
              rcases h : Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] inf.type with _ | b' <;>
                rw [h] at hb <;> cases hb
              rfl
            obtain ⟨hc₁, hg₁, hold, hnew⟩ := hreg
            have hmask : KeepMasks σ inf outs.unzip.2 := by
              refine ⟨by simp [hlen], fun k cn cv hk hc => ?_⟩
              obtain ⟨cv', out, hc', hout, -, h2⟩ := hcv k cn hk
              rw [hc] at hc'
              cases hc'
              simp [List.unzip_snd, hout, h2]
            refine ⟨⟨rfl, hc₁, hg₁, fun T hT => ?_, fun p hp => ?_⟩, ?_⟩
            · have hTn : n ≠ T := hT (n, j) (by simp)
              rw [Std.HashMap.getElem?_insert, ite_eq_right_of_eq_false _ _ (by simpa using hTn)]
              exact hold T fun p hp => hT p (by simp [hp])
            · rcases List.mem_append.1 hp with hp | hp
              · have hpn := hne p hp
                obtain ⟨ivn, masks, h1, h2, h3⟩ := hnew p hp
                refine ⟨ivn, masks, h1, ?_, h3⟩
                rw [Std.HashMap.getElem?_insert, ite_eq_right_of_eq_false _ _ (by simpa using Ne.symm hpn)]
                exact h2
              · simp only [List.mem_singleton] at hp
                subst hp
                exact ⟨inf, _, hinf', Std.HashMap.getElem?_insert_self, hmask⟩
            · refine ⟨inf, hinf', by simp [hlen], fun k cn hk => ?_, hb'⟩
              obtain ⟨cv, out, hc, hout, h1, -⟩ := hcv k cn hk
              exact ⟨cv, out.1, hc, by simp [List.unzip_fst, hout], h1⟩
          split
          · exact HT.bind (HT.getOrFail _ _) fun _ => HT.bind HT.pure_eq fun projs =>
              HT.mono (tail projs) (fun _ h => h.1.1) fun _ _ h => h
          · exact HT.bind HT.pure_eq fun projs => HT.mono (tail projs) (fun _ h => h.1) fun _ _ h => h
      · exact HT.throwM _
    · refine HT.bind (HT.modify _) fun _ => HT.bind HT.get fun s₂ => ?_
      refine HT.mono (HT.getOrFail _ _) (fun _ h => h) fun r s₃ ⟨⟨h₃, h₄⟩, h₅⟩ => ?_
      obtain ⟨s₀, ⟨rfl, hreg, hF⟩, rfl⟩ := h₃
      subst h₄
      refine .inr ⟨?_, s₀, bodies, hreg, hF, h₅, rfl⟩
      cases h : s.inductives[iv.name]? with
      | none => rfl
      | some iid => exact (hnone iid (by rwa [Std.HashMap.get?_eq_getElem?])).elim

end


/-! ## The registration lemma -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}

/-- The block of a program inductive: its names are distinct and contain it, and each names a
program inductive with the same block and parameter count (`IndBlock.ind`). -/
theorem ProgEnv.ind_all {P : List ConstantInfo} (henv : ProgEnv P ζ E B) {c : Name}
    {iv : InductiveVal} (hc : findDecl P c = some (.inductInfo iv)) :
    iv.all.Nodup ∧ c ∈ iv.all ∧ ∀ n ∈ iv.all, ∃ iv', findDecl P n = some (.inductInfo iv') ∧
      iv'.all = iv.all ∧ iv'.numParams = iv.numParams := by
  obtain ⟨ι, η, s, hb, -⟩ := henv.lookup_ind hc
  obtain ⟨lps, Is, Cs, Rs, orders, ⟨_, _, _, _, hblk⟩, hnd, hfind, _, hind, _⟩ := CasesWhred.ProgEnv.block henv η
  have hcs : c = (Is s).name := hind c s hb
  have hIs : ∀ t, findDecl P (Is t).name = some (.inductInfo (Is t)) := fun t =>
    hfind (.inductInfo (Is t)) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨t, rfl⟩))
  have hiv : iv = Is s := by
    rw [hcs, hIs s] at hc
    cases hc
    rfl
  subst hiv hcs
  have hall : ∀ t, (Is t).all = List.ofFn (fun t => (Is t).name) := fun t => (hblk.ind t).2.2.1
  have hpar : ∀ t, (Is t).numParams = ι.nparams := fun t => (hblk.ind t).2.2.2.1
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [hall s]
    have hsub : (List.ofFn fun t => (Is t).name).Sublist ((IndBlock.decls Is Cs Rs).map (·.name)) := by
      have e : (List.ofFn fun t => ConstantInfo.inductInfo (Is t)).map (·.name) =
          List.ofFn fun t => (Is t).name := by
        rw [List.map_ofFn]; rfl
      rw [← e]
      exact (List.sublist_append_right _ _).map _
    exact hnd.sublist hsub
  · rw [hall s]
    exact List.mem_ofFn.mpr ⟨s, rfl⟩
  · rw [hall s] at hn
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hn
    exact ⟨Is t, hIs t, by rw [hall t, hall s], by rw [hpar t, hpar s]⟩

end

/-- The λ□ inductive of a type at position `j` of its block. -/
theorem indIdOf_member {σ : EvalEnv} {T : Name} {ivT : InductiveVal} {j : Nat}
    (hT : findDecl σ.decls T = some (.inductInfo ivT)) (hnd : ivT.all.Nodup)
    (hj : ivT.all[j]? = some T) : IndIdOf σ T = some ⟨blockKername ivT, j⟩ := by
  unfold IndIdOf
  rw [hT]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  have : ivT.all.idxOf? T = some j := List.idxOf?_eq_some_iff.mpr ⟨hlt, hget, fun i hi h => by
    have := (List.Nodup.getElem_inj_iff hnd).mp (h.trans hget.symm)
    omega⟩
  simp [this]

/-- The newest block of a λ□ environment, at its kername. -/
theorem lookupInd_cons_self {bk : Kername} {mib : MutualInductiveBody} {l : GlobalDeclarations}
    {j : Nat} : lookupInd ((bk, .inductiveDecl mib) :: l) ⟨bk, j⟩ = (mib.bodies[j]?).map (mib, ·) := by
  simp [lookupInd, List.find?, StateLemmas.kername_beq_self]

end RegisterInd

open RegisterInd StateLemmas in
/-- `register_inductive` at the pure backend keeps the state invariant: on a registered type it
returns the registered λ□ inductive and masks; otherwise it registers the type's whole block, each
type at its position with masks that keep every field, and conses one λ□ block whose bodies erase
the block's types (`ErasesInd`: parameters, constructors with their field counts, and the
propositional flag, which is `PropInductive` by `Pure.isPropFormerType_iff`), under a fresh block
name. The constants are not touched. The premises are the fragment's: the type's declaration in
the closure (a closure inductive), constructor fields kept, and the facts the fragment test checks
(`PhaseIDecl`: no `@[extern]` constructor under `preferAxiom`, the inductives' sorts;
`BlockNamesInj`). Reference: `erase_mutual_inductive_body` (`MR E/ErasureFunction.v:1325`), the
`InductiveDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_inductive_ok {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {σ : EvalEnv} {st st' : ErasureState} {tc : TravCtx} {pc : PureCtx}
    {ps ps' : PureState} {iv : InductiveVal} {r : InductiveId × InductiveArgMasks}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hok : StateOK E B σ st) (hdecls : pc.decls = σ.decls)
    (hirr : tc.config.remove_irrel_constr_args = false)
    (hph : ∀ ci ∈ σ.decls, PhaseIDecl pc.view tc.config σ.decls ci)
    (hbn : BlockNamesInj σ.decls)
    (hiv : findDecl σ.decls iv.name = some (.inductInfo iv))
    (h : (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st'), ps')) :
    StateOK E B σ st' ∧ LenvExt st.gdecls st'.gdecls ∧ st'.constants = st.constants ∧
      IndIdOf σ iv.name = some r.1 ∧ KeepMasks σ iv r.2 := by
  obtain ⟨hnd, hmem, hco⟩ := ProgEnv.ind_all henv (SrcDefeq.findDecl_sub hsub hiv)
  -- a type of the block, in the closure, has the block's names and parameter count
  have hcoσ : ∀ n ∈ iv.all, ∀ ivn, findDecl σ.decls n = some (.inductInfo ivn) →
      ivn.all = iv.all ∧ ivn.numParams = iv.numParams := by
    intro n hn ivn hf
    obtain ⟨iv', hP, h1, h2⟩ := hco n hn
    rw [SrcDefeq.findDecl_sub hsub hf] at hP
    cases hP
    exact ⟨h1, h2⟩
  have hext : ∀ cn cv, findDecl σ.decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → pc.view.isExtern cn = false := by
    intro cn cv hc hx
    obtain ⟨hm, hn⟩ := findDecl_eq_some hc
    have := (hph _ hm).2 hx
    rwa [show cv.name = cn from hn] at this
  rcases register_inductive_run hdecls hirr hext hnd st st ps r st' ps' rfl h with
    ⟨hr, rfl⟩ | ⟨hnone, s₁, bodies, ⟨hc₁, hg₁, hold, hnew⟩, hF, hr, rfl⟩
  · -- the type is registered
    obtain ⟨h1, -, ivT, hT, hk⟩ := hok.inductives iv.name r hr
    rw [hiv] at hT
    cases hT
    exact ⟨hok, ⟨[], rfl, by simp⟩, rfl, h1, hk⟩
  · -- the block is registered
    have hbk : blockKername iv = mutualBlockKername iv.all := rfl
    generalize mutualBlockKername iv.all = bk at hbk hnew hr ⊢
    generalize hmib : ({ npars := iv.numParams, bodies } : MutualInductiveBody) = mib
    have hpos : ∀ n ∈ iv.all, ∃ j, iv.all[j]? = some n := fun n hn => List.mem_iff_getElem?.mp hn
    have hfst : ∀ p ∈ iv.all.zipIdx, p.1 ∈ iv.all := fun p hp => by
      rw [← List.zipIdx_map_fst 0 iv.all]
      exact List.mem_map_of_mem hp
    -- what the run registered for the type at position `j`
    have hmemb : ∀ j n, iv.all[j]? = some n → ∃ ivn masks ob,
        findDecl σ.decls n = some (.inductInfo ivn) ∧ s₁.inductives[n]? = some (⟨bk, j⟩, masks) ∧
        KeepMasks σ ivn masks ∧ bodies[j]? = some ob ∧ BodyOK σ (n, j) ob := by
      intro j n hj
      have hz : iv.all.zipIdx[j]? = some (n, j) := by simp [hj]
      obtain ⟨ivn, masks, hf, hs, hk⟩ := hnew (n, j) (List.mem_of_getElem? hz)
      obtain ⟨ob, hob, hbody⟩ := forall₂_get hF hz
      exact ⟨ivn, masks, ob, hf, hs, hk, hob, hbody⟩
    -- no type of the block was registered before
    have hfree : ∀ n ∈ iv.all, st.inductives[n]? = none := by
      intro n hn
      cases hs : st.inductives[n]? with
      | none => rfl
      | some r' =>
        obtain ⟨-, -, ivn, hf, -⟩ := hok.inductives n r' hs
        obtain ⟨r'', h''⟩ := hok.whole n r' hs ivn hf iv.name ((hcoσ n hn ivn hf).1 ▸ hmem)
        rw [hnone] at h''
        cases h''
    have hold' : ∀ T, T ∉ iv.all → s₁.inductives[T]? = st.inductives[T]? :=
      fun T hT => hold T fun p hp heq => hT (heq ▸ hfst p hp)
    -- the block name is fresh
    have hfresh : st.gdecls.find? (·.1 == bk) = none := by
      rw [List.find?_eq_none]
      intro d hd hdk
      have hdk' := kername_eq_of_beq hdk
      have hivm : ∃ ci ∈ σ.decls, ci = .inductInfo iv := ⟨_, (findDecl_eq_some hiv).1, rfl⟩
      rcases hok.entries d hd with ⟨c, hc⟩ | ⟨T, r', hT, hname⟩
      · obtain ⟨hk, -, -, -, hnb, -⟩ := hok.registered c d.1 hc
        exact hnb iv hivm (by rw [← hk, hdk', ← hbk])
      · obtain ⟨hid, -, ivT, hT', -⟩ := hok.inductives T r' hT
        unfold IndIdOf at hid
        rw [hT'] at hid
        obtain ⟨j, hj, hj'⟩ := Option.map_eq_some_iff.1 hid
        have hb : blockKername ivT = blockKername iv := by
          rw [hbk, ← hdk', ← hname, ← hj']
        have hall := (hbn ivT iv ⟨_, (findDecl_eq_some hT').1, rfl⟩ hivm).1 hb
        have hTm : T ∈ iv.all := hall ▸ List.isSome_idxOf?.mp (by rw [hj]; rfl)
        rw [hfree T hTm] at hT
        cases hT
    have hx : LenvExt st.gdecls ((bk, .inductiveDecl mib) :: st.gdecls) :=
      ⟨[(bk, .inductiveDecl mib)], rfl, by simpa using hfresh⟩
    -- the new block erases every type of the block
    have herase : ∀ n ∈ iv.all, ErasesInd E B σ ((bk, .inductiveDecl mib) :: st.gdecls) n := by
      intro n hn
      obtain ⟨j, hj⟩ := hpos n hn
      obtain ⟨ivn, -, -, hf, -⟩ := hmemb j n hj
      obtain ⟨hall, hpar⟩ := hcoσ n hn ivn hf
      refine ⟨ivn, hf, fun j' n' hj' => ?_⟩
      rw [hall] at hj'
      obtain ⟨ivn', -, ob, hf', -, -, hob, ivb, hfb, hlen, hctors, hprop⟩ := hmemb j' n' hj'
      rw [hf'] at hfb
      cases hfb
      refine ⟨ivn', mib, ob, hf', ?_, by rw [← hmib, hpar], hlen, hctors,
        Pure.isPropFormerType_iff henv hE (SrcDefeq.findDecl_sub hsub hf')
          (hph _ (findDecl_eq_some hf').1) hprop⟩
      have hb : blockKername ivn = bk := by
        show mutualBlockKername ivn.all = bk
        rw [hall]
        exact hbk
      rw [hb, lookupInd_cons_self, ← hmib]
      simp [hob]
    obtain ⟨j₀, hj₀⟩ := hpos iv.name hmem
    obtain ⟨iv₀, masks₀, -, hf₀, hs₀, hk₀, -⟩ := hmemb j₀ iv.name hj₀
    rw [hiv] at hf₀
    cases hf₀
    rw [hs₀] at hr
    cases hr
    have hx' : LenvExt st.gdecls ((bk, .inductiveDecl mib) :: s₁.gdecls) := by rw [hg₁]; exact hx
    refine ⟨⟨fun c kn hc => ?_, fun T r' hT => ?_, fun d hd => ?_, fun T r' hT ivT hfT n hn => ?_,
      fun kn cb b hl hb => ?_⟩, hx', hc₁, ?_, hk₀⟩
    · rw [show s₁.constants = st.constants from hc₁] at hc
      obtain ⟨hk, ci, cb, hf, hem, hl, hd, hb⟩ := hok.registered c kn hc
      exact ⟨hk, ci, cb, hf, hem, lookupConst_ext hx' hl, hd, fun b h => (hb b h).ext hx'⟩
    · by_cases hTm : T ∈ iv.all
      · obtain ⟨j, hj⟩ := hpos T hTm
        obtain ⟨ivn, masks, -, hf, hs, hk, -⟩ := hmemb j T hj
        change s₁.inductives[T]? = some r' at hT
        rw [hs] at hT
        cases hT
        obtain ⟨hall, -⟩ := hcoσ T hTm ivn hf
        refine ⟨?_, by rw [hg₁]; exact herase T hTm, ivn, hf, hk⟩
        have hb : blockKername ivn = bk := by
          show mutualBlockKername ivn.all = bk
          rw [hall]
          exact hbk
        rw [indIdOf_member hf (hall ▸ hnd) (hall ▸ hj), hb]
      · change s₁.inductives[T]? = some r' at hT
        rw [hold' T hTm] at hT
        obtain ⟨h1, h2, h3⟩ := hok.inductives T r' hT
        exact ⟨h1, StateLemmas.ErasesInd.ext hx' h2, h3⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact .inr ⟨iv.name, _, hs₀, rfl⟩
      · rw [hg₁] at hd
        rcases hok.entries d hd with ⟨c, hc⟩ | ⟨T, r', hT, hn⟩
        · exact .inl ⟨c, by rw [show s₁.constants = st.constants from hc₁]; exact hc⟩
        · have hTm : T ∉ iv.all := fun hTm => by rw [hfree T hTm] at hT; cases hT
          exact .inr ⟨T, r', by rw [← hold' T hTm] at hT; exact hT, hn⟩
    · have hsome : ∀ m : Name, (∃ r'' : InductiveId × InductiveArgMasks, st.inductives[m]? = some r'') →
          ∃ r'' : InductiveId × InductiveArgMasks, s₁.inductives[m]? = some r'' := by
        intro m ⟨r'', hm⟩
        by_cases hmm : m ∈ iv.all
        · obtain ⟨j, hj⟩ := hpos m hmm
          obtain ⟨_, masks, -, -, hs, -⟩ := hmemb j m hj
          exact ⟨_, hs⟩
        · exact ⟨r'', by rw [hold' m hmm]; exact hm⟩
      change s₁.inductives[T]? = some r' at hT
      by_cases hTm : T ∈ iv.all
      · obtain ⟨hall, -⟩ := hcoσ T hTm ivT hfT
        rw [hall] at hn
        obtain ⟨j, hj⟩ := hpos n hn
        obtain ⟨_, masks, -, -, hs, -⟩ := hmemb j n hj
        exact ⟨_, hs⟩
      · rw [hold' T hTm] at hT
        exact hsome n (hok.whole T r' hT ivT hfT n hn)
    · rcases lookupConst_cons hl with ⟨-, hcd⟩ | ⟨-, hl'⟩
      · cases hcd
      · rw [hg₁] at hl'
        exact hok.closed kn cb b hl' hb
    · rw [indIdOf_member hiv hnd hj₀, hbk]

end EraseProof
