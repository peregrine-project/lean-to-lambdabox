import EraseProof.Source.Defeq
import EraseProof.Metatheory.NoConf

/-!
# The proof-irrelevant ι of the source semantics, and subject reduction

`SrcProof.proofSound` discharges `SrcDefeq.ProofSound`: a saturated recognized `casesOn` of a
`Prop` inductive with one field-less constructor, on a major that evaluates to a neutral proof,
is definitionally equal to its alternative. Metalean has no ι on a neutral major; the step is
proof irrelevance at the major's type followed by ι on the constructor. The major's type is a
proposition because the `casesOn` unfolds to the recursor (`SrcProof.casesOn_recr`), whose major
has the inductive's type at the `casesOn`'s levels, whose sort is that of the Lean declaration
(`SrcProof.ind_level`). The constructor applied to the parameters of the major's statement
translates, since the statement has the shape `I ps idx` that the constructor's Lean type gives it
(`IndBlock.ctorType`, `SrcProof.ctor_statement`), and it has the statement's type
(`SrcProof.ctorTerm_apps_typed`). With it, `SrcEval.defeq` (subject reduction) and
`ErasableS.eval` hold. The shape of constructor types also makes the type of a constructor of a
`Prop` inductive an evident proposition (`SrcProof.ctor_evidentProp`). Reference:
`eval_iota_sing` (`MR E/EWcbvEval.v:162`); `proofIrrel` (`ML Typing/Defs.lean:158`); DV-24.
-/

open Lean Erasure
open Metalean (Defeq EnvWF WHRed WHRedS TypeEq)

namespace EraseProof

namespace SrcProof

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ}

/-! ## Telescopes -/

section
variable {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n}

/-- A Π over a telescope respects equality of the body's types. -/
theorem pi_congr {m : Nat} (Δ : Metalean.Ctx ζ ℓ n m) :
    ∀ {U₁ U₂ : Metalean.Expr ζ ℓ m}, E[Γ ++ Δ] ⊢ ok → E[Γ ++ Δ] ⊢ U₁ ≡ U₂ typ →
      E[Γ] ⊢ Δ.pi U₁ ≡ Δ.pi U₂ typ := by
  induction Δ with
  | nil => intro _ _ _ h; exact h
  | snoc Δ t ih =>
    intro _ _ hok h
    have .snoc hΓΔ ⟨_, ht⟩ := hok
    exact ih hΓΔ (TypeEq.forallE_congr ht h)

/-- A typed λ over a telescope: its body is typed in the extended context, and its type is the
Π over the telescope of the body's type. -/
theorem lam_tele_inv (hΓ : E[Γ] ⊢ ok) {m : Nat} (Δ : Metalean.Ctx ζ ℓ n m) :
    ∀ {e : Metalean.Expr ζ ℓ m} {T : Metalean.Expr ζ ℓ n}, E[Γ] ⊢ Δ.lam e : T →
      ∃ U, E[Γ ++ Δ] ⊢ ok ∧ E[Γ ++ Δ] ⊢ e : U ∧ E[Γ] ⊢ T ≡ Δ.pi U typ := by
  induction Δ with
  | nil =>
    intro e T h
    obtain ⟨_, hr⟩ := h.regular
    exact ⟨T, hΓ, h, Metalean.IsType.typeEq ⟨_, hr⟩⟩
  | snoc Δ t ih =>
    intro e T h
    obtain ⟨U', hok, hl, hT⟩ := ih h
    obtain ⟨U, he, hU⟩ := hl.lam_inv hok
    obtain ⟨_, hr⟩ := hU.right
    obtain ⟨l₁, -, ht, -, -⟩ := hr.forallE_ty_inv
    exact ⟨U, .snoc hok ⟨l₁, ht⟩, he, hT.trans (pi_congr Δ hok hU)⟩

end

/-- A Π-telescope of `k` binders over a sort. -/
inductive PiSort {ℓ : Nat} : {n : Nat} → Metalean.Expr ζ ℓ n → Nat → Metalean.Level ℓ → Prop
  | sort {n : Nat} {u : Metalean.Level ℓ} : PiSort (n := n) (.sort u) 0 u
  | forallE {n k : Nat} {A : Metalean.Expr ζ ℓ n} {B : Metalean.Expr ζ ℓ (n + 1)}
      {u : Metalean.Level ℓ} : PiSort B k u → PiSort (.forallE A B) (k + 1) u

/-- A Π over a telescope of a Π-telescope over a sort. -/
theorem PiSort.pi {ℓ n m : Nat} {u : Metalean.Level ℓ} (Δ : Metalean.Ctx ζ ℓ n m) :
    ∀ {e : Metalean.Expr ζ ℓ m} {k : Nat}, PiSort e k u → PiSort (Δ.pi e) (k + (m - n)) u := by
  induction Δ with
  | nil => intro _ _ h; simpa using h
  | @snoc b Δ t ih =>
    intro _ k h
    have hle := Δ.le
    have h2 := ih (.forallE (A := t) h)
    rwa [show k + 1 + (b - n) = k + (b + 1 - n) by omega] at h2

/-- Equal Π-telescopes over sorts have the same number of binders and the same sort. -/
theorem PiSort.inj (hE : EnvWF E) {ℓ n : Nat} {X : Metalean.Expr ζ ℓ n} {k : Nat}
    {a : Metalean.Level ℓ} (hX : PiSort X k a) :
    ∀ {Γ : Metalean.Ctx ζ ℓ 0 n} {Y : Metalean.Expr ζ ℓ n} {k' : Nat} {b : Metalean.Level ℓ},
      PiSort Y k' b → E[Γ] ⊢ ok → E[Γ] ⊢ X ≡ Y typ → a = b ∧ k = k' := by
  induction hX with
  | sort =>
    intro Γ Y k' b hY hΓ h
    cases hY with
    | sort => exact ⟨TypeEq.sort_inj hE hΓ h, rfl⟩
    | forallE => exact absurd h (EraseProof.TypeEq.sort_ne_forallE hE hΓ)
  | forallE _ ih =>
    intro Γ Y k' b hY hΓ h
    cases hY with
    | sort => exact absurd h.symm (EraseProof.TypeEq.sort_ne_forallE hE hΓ)
    | forallE hB =>
      obtain ⟨_, hl⟩ := h.left
      obtain ⟨l₁, -, hA, -, -⟩ := hl.forallE_ty_inv
      obtain ⟨h1, h2⟩ := ih hB (.snoc hΓ ⟨l₁, hA⟩) (TypeEq.forallE_inj hE hΓ h).2
      exact ⟨h1, by rw [h2]⟩

/-- The translation of a Lean arity `Π xs, Sort u` is a Π-telescope over the translated sort. -/
theorem trM_arity {B : Binds ζ} {lps : List Name} :
    ∀ {ty : Expr} {k : Nat} {u : Level} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
      {Δ : MLCtx ζ lps.length n} {Y : Metalean.Expr ζ lps.length n},
      arityShape ty = some (k, u) → TrM E B lps Γ Δ ty Y →
      ∃ a, TrLevel lps u = some a ∧ PiSort Y k a
  | .sort v, k, u, n, Γ, Δ, Y, hs, h => by
    simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    generalize hx : Expr.sort v = e at h
    cases h with
    | sort hl => cases hx; exact ⟨_, hl, .sort⟩
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const (e := .sort v) fun _ _ h => by cases h)
    | _ => cases hx
  | .forallE x A b bi, k, u, n, Γ, Δ, Y, hs, h => by
    simp only [arityShape, Option.map_eq_some_iff] at hs
    obtain ⟨⟨k', u'⟩, hs', he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨A', b', rfl, -, hb⟩ := SrcDefeq.trM_forallE_inv h
    obtain ⟨a, ha, hp⟩ := trM_arity hs' hb
    exact ⟨a, ha, .forallE hp⟩
  | .mdata d e, k, u, n, Γ, Δ, Y, hs, h => by
    simp only [arityShape] at hs
    generalize hx : Expr.mdata d e = e' at h
    cases h with
    | mdata he => cases hx; exact trM_arity hs he
    | special =>
      exact absurd hx (CasesWhred.ne_mkAppN_const (e := .mdata d e) fun _ _ h => by cases h)
    | _ => cases hx
  | .bvar _, _, _, _, _, _, _, hs, _ | .fvar _, _, _, _, _, _, _, hs, _
  | .mvar _, _, _, _, _, _, _, hs, _ | .const .., _, _, _, _, _, _, hs, _
  | .app .., _, _, _, _, _, _, hs, _ | .lam .., _, _, _, _, _, _, hs, _
  | .letE .., _, _, _, _, _, _, hs, _ | .lit _, _, _, _, _, _, _, hs, _
  | .proj .., _, _, _, _, _, _, hs, _ => by simp [arityShape] at hs

/-! ## The sort of an inductive -/

section
variable {B : Binds ζ} {P : List ConstantInfo}

/-- The type of the translation of an inductive type former of the program, at its own levels,
is a Π-telescope over the block's sort at those levels. -/
theorem indConst_piSort {iv : InductiveVal} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} (hB : B iv.name = some (.ind η s))
    {ls₀ : Fin ι.nlevels → Metalean.Level iv.levelParams.length}
    (hls : TrLevels iv.levelParams (iv.levelParams.map .param) ι.nlevels = some ls₀)
    {t₀ T : Metalean.Expr ζ iv.levelParams.length 0}
    (ht₀ : TrM E B iv.levelParams .nil [] (.const iv.name (iv.levelParams.map .param)) t₀)
    (ht : E[.nil] ⊢ t₀ : T) :
    ∃ Y, PiSort Y (ι.nparams + ι.nindices s) ((E.get η).block.level{ls₀}) ∧
      E[.nil] ⊢ T ≡ Y typ := by
  have ht₀' : TrM E B iv.levelParams .nil [] (mkAppN (.const iv.name
      (iv.levelParams.map .param)) ([] : List Expr).toArray) t₀ := ht₀
  obtain ⟨as₁, hlen₁, -, hsat⟩ := TrM.special_inv hB rfl ht₀'
  cases hsat with
  | indSat ps is rest hls' =>
    obtain rfl := (Option.some.inj (hls.symm.trans hls'))
    have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hlen₁; omega)
    subst hrest
    obtain ⟨-, -, -, -, hT⟩ := ht.ind_inv
    have h0 : ι.nparams + ι.nindices s = 0 := by simp at hlen₁; omega
    exact ⟨_, by rw [h0]; exact .sort, hT⟩
  | indEta hls' _ =>
    obtain rfl := (Option.some.inj (hls.symm.trans hls'))
    obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
    have ht' : E[.nil] ⊢ ((E.get η).block.argTele s){ls₀}.lam
        (.ind η s ls₀ (fun p => .var ⟨p.val, by omega⟩)
          fun i => .var ⟨ι.nparams + i.val, by omega⟩) : T := ht
    obtain ⟨U, hok, hbody, hT⟩ := lam_tele_inv SrcDefeq.nil_ok _ ht'
    obtain ⟨-, -, -, -, hU⟩ := hbody.ind_inv
    have hp := PiSort.pi (((E.get η).block.argTele s){ls₀})
      (PiSort.sort (n := ι.nparams + ι.nindices s) (u := (E.get η).block.level{ls₀}))
    rw [Nat.zero_add] at hp
    exact ⟨_, hp, hT.trans (pi_congr _ hok hU)⟩

/-- The sort of an inductive of the program: the Metalean block's level at any levels is the
translation of the sort of the Lean type, at the corresponding universe parameters. Reference:
`declared_inductive` (MC §3.6). -/
theorem ind_level (henv : ProgEnv P ζ E B) (hE : EnvWF E) {iv : InductiveVal}
    (hiv : findDecl P iv.name = some (.inductInfo iv)) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} (hB : B iv.name = some (.ind η s))
    {k : Nat} {u : Level} (har : arityShape iv.type = some (k, u)) :
    ∃ (a : Metalean.Level iv.levelParams.length) (hk : ι.nlevels = iv.levelParams.length),
      TrLevel iv.levelParams u = some a ∧ k = ι.nparams + ι.nindices s ∧
      ∀ {ℓ' : Nat} (L : Fin ι.nlevels → Metalean.Level ℓ'),
        (E.get η).block.level{L} = a{fun i : Fin iv.levelParams.length => L (i.cast hk.symm)} := by
  obtain ⟨b, hb, T, t₀, hT, ht₀, ht⟩ := henv.lookup hE hiv
  have hnd : iv.levelParams.Nodup :=
    henv.levelParams_nodup (findDecl_eq_some hiv).1
  have ht₀' : TrM E B iv.levelParams .nil [] (mkAppN (.const iv.name
      (iv.levelParams.map .param)) ([] : List Expr).toArray) t₀ := ht₀
  obtain ⟨_, -, -, hsat⟩ := TrM.special_inv hB rfl ht₀'
  obtain ⟨ls₀, hls⟩ : ∃ ls₀, TrLevels iv.levelParams (iv.levelParams.map .param) ι.nlevels =
      some ls₀ := by
    cases hsat with
    | indSat _ _ _ h => exact ⟨_, h⟩
    | indEta h _ => exact ⟨_, h⟩
  obtain ⟨hk, hls₀⟩ := SrcDefeq.trLevels_params_nodup hnd hls
  obtain ⟨a, ha, hPa⟩ := trM_arity har hT
  obtain ⟨Y, hY, hTY⟩ := indConst_piSort hB hls ht₀ ht
  obtain ⟨heq, hdepth⟩ := PiSort.inj hE hPa hY SrcDefeq.nil_ok hTY
  refine ⟨a, hk, ha, hdepth, fun L => ?_⟩
  rw [heq, Metalean.Level.inst_inst]
  congr 1
  funext i
  rw [hls₀ i]
  rfl

end

/-- Translated levels, level by level. -/
theorem trLevels_of_get {lps : List Name} {vs : List Level} {k : Nat}
    {ls : Fin k → Metalean.Level lps.length} (hk : vs.length = k)
    (h : ∀ i : Fin k, TrLevel lps (vs[i.val]'(by omega)) = some (ls i)) :
    TrLevels lps vs k = some ls := by
  subst hk
  have hmap : ∀ (vs : List Level) (ls : Fin vs.length → Metalean.Level lps.length),
      (∀ i : Fin vs.length, TrLevel lps vs[i.val] = some (ls i)) →
      vs.mapM (TrLevel lps) = some (List.ofFn ls) := by
    intro vs
    induction vs with
    | nil => intro ls _; rfl
    | cons v vs ih =>
      intro ls h
      have h0 := h ⟨0, by simp⟩
      simp only [List.getElem_cons_zero] at h0
      rw [List.mapM_cons, h0, ih (fun i => ls i.succ) fun i => by simpa using h i.succ]
      simp [List.ofFn_succ]
  simp only [TrLevels, hmap vs ls h, List.length_ofFn, bind, Option.bind_some, ↓reduceDIte,
    List.getElem_ofFn]

/-- The recursor's levels in a `casesOn` value with level parameters `pre ++ lps₀` (the motive's
level, if any, then the inductive's), instantiated at a spine's levels `us`, are the translations
of the last `|lps₀|` levels of `us`. -/
theorem recr_levels {lps dl pre lps₀ : List Name} {us : List Level} {k : Nat}
    (hdl : dl = pre ++ lps₀) (hnd : dl.Nodup) (hk : k = lps₀.length)
    {lsc : Fin dl.length → Metalean.Level lps.length} (hlsc : TrLevels lps us dl.length = some lsc)
    {lsR : Fin k → Metalean.Level dl.length} (hlsR : TrLevels dl (lps₀.map .param) k = some lsR) :
    TrLevels lps (us.drop (us.length - lps₀.length)) lps₀.length =
      some (fun i => (lsR (i.cast hk.symm)){lsc}) := by
  subst hdl hk
  obtain ⟨hus, hget⟩ := TrLevels_get hlsc
  obtain ⟨_, hgetR⟩ := TrLevels_get hlsR
  simp only [List.length_append] at hus
  refine trLevels_of_get (by simp; omega) fun i => ?_
  have hi : pre.length + i.val < (pre ++ lps₀).length := by simp
  have hfi : (pre ++ lps₀).finIdxOf? lps₀[i.val] = some ⟨pre.length + i.val, hi⟩ :=
    List.finIdxOf?_eq_some_iff.mpr ⟨by simp, fun j hj heq => by
      have h1 : (pre ++ lps₀)[pre.length + i.val] = lps₀[i.val] := by
        simp [List.getElem_append_right]
      have := (List.Nodup.getElem_inj hnd).mp (heq.trans h1.symm)
      rw [Fin.lt_def] at hj; simp at hj this; omega⟩
  have hR := hgetR i
  simp only [List.getElem_map, TrLevel, hfi, Option.map_some, Option.some.injEq] at hR
  rw [Fin.cast_eq_self, ← hR, Metalean.Level.inst_param]
  have := hget ⟨pre.length + i.val, hi⟩
  simp only [List.getElem_drop]
  convert this using 3
  simp; omega

/-! ## A `casesOn` spine reduces to the recursor on its major -/

section
variable {B : Binds ζ} {P : List ConstantInfo} {lps : List Name}

open CasesWhred in
/-- A saturated recognized `casesOn` spine reduces (δ, β) to the Metalean recursor node of the
inductive on a translation of its major, at the levels of the recursor in the `casesOn`'s value
instantiated by the spine's, in any context. The `casesOn` has as many universe parameters as its
inductive exactly when the block does not eliminate into every sort, and the motive's level is
then `0`. Reference: `WHRed.delta` (`ML Syntax/Reduction.lean`). -/
theorem casesOn_recr {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n}
    {c : Name} {iv : InductiveVal} {as : List Expr} {m : Expr} {us : List Level}
    {t : Metalean.Expr ζ lps.length n} (hcs : σ.casesOn? c = some iv)
    (hlen : as.length = casesArity iv) (hm : as[casesMajor iv]? = some m)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (L : Fin ι.nlevels → Metalean.Level lps.length) (l : Metalean.Level lps.length)
      (ps : Fin ι.nparams → Metalean.Expr ζ lps.length n)
      (ms : Fin ι.nsorts → Metalean.Expr ζ lps.length n)
      (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Metalean.Expr ζ lps.length n)
      (is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n) (m' : Metalean.Expr ζ lps.length n),
      B iv.name = some (.ind η s) ∧ TrM E B lps Γ Δ m m' ∧
      E ⊢ t ⤳* .recr η s L l ps ms mins is m' ∧
      (∀ l₀, casesSortLevel iv us = some l₀ → TrLevel lps l₀ = some ((E.get η).block.level{L})) ∧
      (∀ d, findDecl σ.decls c = some (.defnInfo d) →
        (d.levelParams.length = iv.levelParams.length ↔ ¬ (E.get η).block.LargeElim)) ∧
      (¬ (E.get η).block.LargeElim → l = .zero) := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨d, R, j, before, alts, body, rargs, -, hd, hiv, hR, -, -, hlp, -, -, hbe, -, hbody,
    hbdy, hrlen, -, -, -, -, hmaj⟩ := casesOn_shape hcs
  obtain ⟨ι, η, s, hBT, -, -, -⟩ := ProgEnv.lookup_ind henv (hP hiv)
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨_, E₀, _, η₀, hIB⟩, hnd, hfd, hrec, hindB, -⟩ :=
    ProgEnv.block henv η
  have hT : iv.name = (Is s).name := hindB _ _ hBT
  have hmemI : ∀ t, ConstantInfo.inductInfo (Is t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hmemR : ∀ t, ConstantInfo.recInfo (Rs t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hfdI : ∀ t, findDecl P (Is t).name = some (.inductInfo (Is t)) := fun t => hfd _ (hmemI t)
  have hfdR : ∀ t, findDecl P (Rs t).name = some (.recInfo (Rs t)) := fun t => hfd _ (hmemR t)
  have hivs : iv = Is s := by
    have h1 := hP hiv
    rw [hT, hfdI s] at h1
    cases h1; rfl
  subst hivs
  have hRs : R = Rs s := by
    have h1 := hP hR
    rw [← (hIB.recr s).1, hfdR s] at h1
    cases h1; rfl
  subst hRs
  obtain ⟨-, hlpI, -, hInp, hIni, hIctors, -, -⟩ := hIB.ind s
  obtain ⟨-, -, hLE1, hLE2, -, -, hRnp, hRnm, hRmin, hRni⟩ := hIB.recr s
  subst hlpI
  have hrecrEnd : rargs.length = ι.recrEnd s := by
    rw [hrlen, hRnp, hRnm, hRmin, hRni]
    show _ = ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1
    rw [fin_sum_eq]
  obtain ⟨ηc, hBc, htrv⟩ := ProgEnv.lookup_def henv (hP hd)
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us'', b, h1, h2, h3⟩
    cases h1; rw [hBc] at h2; cases h2; cases h3
  obtain ⟨h', xs, hh', hxs, rfl⟩ := trM_spine_inv hns as he
  obtain ⟨lsc, rfl, hlsc⟩ := SrcDefeq.trM_const_inv' hBc hh'
  have hxslen : xs.length = casesArity (Is s) := by rw [← hxs.length_eq, hlen]
  obtain ⟨Θ, b, Γ', hdef, hb⟩ := trM_peel _ hbody htrv
  rw [hbdy] at hb
  obtain ⟨lsR, lR, mo, A, mins, hA, -, -, hbeq, us', hRL, hlsR⟩ := trM_recr_inv (hrec s) hrecrEnd hb
  let g : Fin (casesArity (Is s)) → Metalean.Expr ζ lps.length n := fun j => xs[j.val]'(by omega)
  let σ₀ : Metalean.Subst ζ lps.length 0 n := Fin.elim0
  have hδβ : E ⊢ (Metalean.Expr.const ηc lsc).appList xs ⤳* b{lsc}.subst (Fin.append σ₀ g) := by
    refine (appList_whredS (E := E) (Relation.ReflTransGen.single
      (WHRed.delta (η := ηc) (ls := lsc))) xs).trans ?_
    rw [hdef, ← Metalean.Expr.subst_closed _ σ₀,
      appList_eq_apps _ g hxslen (fun j => by simp [g])]
    exact lams_beta (E := E) Θ _ lsc σ₀ g
  obtain ⟨m', hxm, hm'⟩ := CasesWhred.forall₂_getElem? hxs hm
  obtain ⟨a₀, ha₀, htr₀⟩ := hA (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve
  have hpos : ((Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve).val =
      (Is s).numParams + (Rs s).numMotives + (Rs s).numMinors + (Is s).numIndices := by
    simp only [Metalean.IndSig.RecrBinder.resolve, Fin.val_last, hInp, hRnm, hRmin, hIni,
      Metalean.IndSig.casesEnd, Metalean.IndSig.motivesEnd, fin_sum_eq]
  rw [hpos, hmaj] at ha₀
  cases ha₀
  have hfb := trM_bvar_inv htr₀
  rw [findB_pushLams_lt _ _ _ (by unfold casesArity; omega)] at hfb
  have hAmaj : ((A (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve){lsc}).subst
      (Fin.append σ₀ g) = m' := by
    rw [← Option.some.inj hfb]
    show Fin.append σ₀ g _ = _
    rw [append_elim0]
    simp only [g]
    have : casesArity (Is s) - 1 - (casesArity (Is s) - 1 - casesMajor (Is s)) =
        casesMajor (Is s) := by unfold casesArity; omega
    simp only [Nat.zero_add, this]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hxm)
  -- the levels
  have hlev := hIB.levels
  obtain ⟨hlsRlen, _⟩ := TrLevels_get hlsR
  have hdl : ∃ pre, d.levelParams = pre ++ (Is s).levelParams ∧
      us' = (Is s).levelParams.map .param := by
    rw [hlp]
    have hRlps : (∃ x, (Rs s).levelParams = x :: (Is s).levelParams) ∨
        (Rs s).levelParams = (Is s).levelParams := by
      by_cases hL : (E₀.get η₀).block.LargeElim
      · exact .inl (hLE1 hL)
      · exact .inr (hLE2 hL)
    rcases hRL with ⟨-, u', hcons, -⟩ | ⟨-, hus', -⟩
    · rcases hRlps with ⟨x, hx⟩ | hx <;> rw [hx] at hcons ⊢
      · simp only [List.map_cons, List.cons.injEq] at hcons
        exact ⟨[x], rfl, hcons.2.symm⟩
      · have := congrArg List.length hcons
        simp at this hlsRlen; omega
    · rcases hRlps with ⟨x, hx⟩ | hx <;> rw [hx] at hus' ⊢
      · subst hus'
        simp only [List.length_map, List.length_cons] at hlsRlen
        omega
      · exact ⟨[], rfl, hus'⟩
  obtain ⟨pre, hpre, rfl⟩ := hdl
  have hdrop := recr_levels hpre (henv.levelParams_nodup (findDecl_eq_some (hP hd)).1)
    hlev.symm hlsc hlsR
  have hlevel : ∀ l₀, casesSortLevel (Is s) us = some l₀ →
      TrLevel lps l₀ = some ((E.get η).block.level{fun i => (lsR i){lsc}}) := by
    intro l₀ hl₀
    simp only [casesSortLevel, Option.map_eq_some_iff] at hl₀
    obtain ⟨⟨k₀, u⟩, har, rfl⟩ := hl₀
    obtain ⟨a, hk, ha, -, hlv⟩ := ind_level henv hE (hfdI s) hBT har
    rw [hlv, TrLevel_instLevel hdrop ha]
  have hLE : (d.levelParams.length = (Is s).levelParams.length ↔ ¬ (E.get η).block.LargeElim) ∧
      (¬ (E.get η).block.LargeElim → lR = .zero) := by
    rcases hRL with ⟨hL, u', hcons, -⟩ | ⟨hL, hus', hl0⟩
    · have := congrArg List.length hcons
      simp only [List.length_map, List.length_cons] at this
      exact ⟨⟨fun h => by rw [hlp] at h; omega, fun h => absurd hL h⟩, fun h => absurd hL h⟩
    · have := congrArg List.length hus'
      simp only [List.length_map] at this
      exact ⟨⟨fun _ => hL, fun _ => by rw [hlp]; exact this.symm⟩, fun _ => hl0⟩
  rw [hbeq] at hδβ
  refine ⟨ι, η, s, _, _, _, _, _, _, _, hBT, ?_, hδβ, hlevel, fun d' hd' => ?_, fun h => ?_⟩
  · erw [hAmaj]
    exact hm'
  · rw [hd] at hd'
    cases hd'
    exact hLE.1
  · rw [hLE.2 h]
    rfl

end

/-! ## Constructor types are evident propositions -/

section
variable {B : Binds ζ} {P : List ConstantInfo}

/-- Every constructor of the program belongs to an inductive block whose type is in the
program. -/
theorem ctor_mem_block (henv : ProgEnv P ζ E B) {cv : ConstructorVal}
    (hm : ConstantInfo.ctorInfo cv ∈ P) :
    ∃ (ι : Metalean.IndSig) (ζ₀ : Metalean.Sigs) (E₀ : Metalean.Env ζ₀) (B₀ : Binds ζ₀)
      (η₀ : Metalean.Head ζ₀ (.inductive ι)) (lps₀ : List Name) (Is : Fin ι.nsorts → InductiveVal)
      (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal)
      (Rs : Fin ι.nsorts → RecursorVal) (orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat)
      (s : Fin ι.nsorts) (k : Fin (ι.nctors s)),
      IndBlock E₀ B₀ η₀ lps₀ Is Cs Rs orders ∧ cv = Cs s k ∧ .inductInfo (Is s) ∈ P := by
  induction henv with
  | nil => cases hm
  | «axiom» _ _ _ _ _ ih | defn _ _ _ _ _ _ _ ih | thm _ _ _ _ _ _ _ ih
  | «opaque» _ _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
    · obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hb, rfl, hI⟩ := ih h
      exact ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hb, rfl, .tail _ hI⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs orders _ _ _ _ _ hblk _ ih =>
    rcases List.mem_append.mp hm with h | h
    · rcases IndBlock.mem_decls h with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
      refine ⟨ι, _, _, _, _, _, Is, Cs, Rs, orders, s, k, hblk, rfl, List.mem_append_left _ ?_⟩
      simp [IndBlock.decls, List.mem_ofFn]
    · obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is', Cs', Rs', orders', s, k, hb, rfl, hI⟩ := ih h
      exact ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is', Cs', Rs', orders', s, k, hb, rfl,
        List.mem_append_right _ hI⟩
  | quot _ _ _ _ _ _ _ ih =>
    rcases List.mem_append.mp hm with h | h
    · simp at h
    · obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hb, rfl, hI⟩ := ih h
      exact ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hb, rfl,
        List.mem_append_right _ hI⟩

/-- Peeling `Π`s does not change whether a type is an evident proposition. -/
theorem evidentProp_peel (decls : List ConstantInfo) :
    ∀ (k : Nat) {ty body : Expr}, peelForalls k ty = some body →
      EvidentProp decls ty = EvidentProp decls body
  | 0, ty, body, h => by
    simp only [peelForalls, Function.iterate_zero, id, Option.some.injEq] at h
    rw [h]
  | k + 1, ty, body, h => by
    simp only [peelForalls, Function.iterate_succ, Function.comp_apply, Option.bind_some] at h
    cases ty with
    | forallE x A b bi =>
      simp only [Expr.isForall, ↓reduceIte, Expr.bindingBody!] at h
      rw [EvidentProp]
      exact evidentProp_peel decls k h
    | _ =>
      simp only [Expr.isForall, Bool.false_eq_true, ↓reduceIte] at h
      rw [Function.iterate_fixed (by rfl)] at h
      cases h

/-- An evident proposition on a constant spine: the head is `DeltaFree`, its declared arity
takes exactly the arguments, at an evidently zero sort. -/
theorem evidentProp_spine (decls : List ConstantInfo) (h : Name) (vs : List Level)
    (args : List Expr) :
    EvidentProp decls (mkAppN (.const h vs) args.toArray) =
      match findDecl decls h with
      | some ci => DeltaFree ci && match arityShape ci.type with
        | some (n, u) => n == args.length && EvidentZero (Pure.instLevel ci.levelParams vs u)
        | none => false
      | none => false := by
  rcases List.eq_nil_or_concat args with rfl | ⟨L, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, SrcDefeq.mkAppN_snoc, EvidentProp,
      ← SrcDefeq.mkAppN_snoc, SrcDefeq.getAppFn_mkAppN_const, SrcDefeq.getAppNumArgs_mkAppN_const]
    · rfl
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h

/-- The Lean type of a constructor of an inductive that is evidently in `Prop` is an evident
proposition: `Π (params) (fields), I.{lps} params indices` (`IndBlock.ctorType`), `I` an
inductive type whose declared arity has one binder per parameter and index (`SrcProof.ind_level`)
and whose sort is evidently zero. Reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`). -/
theorem ctor_evidentProp {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {c : Name} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) (hp : σ.propInd cv.induct = true) :
    EvidentProp σ.decls cv.type = true := by
  obtain ⟨iv, k', u, hiv, har, hz⟩ : ∃ iv k' u, findDecl σ.decls cv.induct = some (.inductInfo iv) ∧
      arityShape iv.type = some (k', u) ∧ EvidentZero u = true := by
    unfold EvalEnv.propInd at hp
    split at hp
    · rename_i iv hiv
      split at hp
      · rename_i k' u har
        exact ⟨iv, k', u, hiv, har, hp⟩
      · cases hp
    · cases hp
  obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hIB, rfl, hI⟩ :=
    ctor_mem_block henv (findDecl_eq_some (SrcDefeq.findDecl_sub hsub hc)).1
  obtain ⟨-, hlp, hind, -, -, -, -, -⟩ := hIB.ctor s k
  obtain ⟨-, hlpI, -, hInp, hIni, -, -, -⟩ := hIB.ind s
  have hfdI : findDecl P (Is s).name = some (.inductInfo (Is s)) :=
    CasesWhred.findDecl_of_nodup henv.fresh hI
  have hivs : iv = Is s := by
    have h1 := SrcDefeq.findDecl_sub hsub hiv
    rw [hind, hfdI] at h1
    cases h1; rfl
  subst hivs
  obtain ⟨ι', η', s', hB', hnp', hni', -⟩ := ProgEnv.lookup_ind henv hfdI
  obtain ⟨-, -, -, hdepth, -⟩ := ind_level henv hE hfdI hB' har
  obtain ⟨body, idx, hpeel, hidx, rfl⟩ := hIB.ctorType s k
  rw [evidentProp_peel _ _ hpeel, evidentProp_spine, ← hind, hiv]
  have har' : arityShape (ConstantInfo.inductInfo (Is s)).type = some (k', u) := har
  have hlp' : (ConstantInfo.inductInfo (Is s)).levelParams = lps₀ := hlpI
  simp only [DeltaFree, Bool.true_and, har', hlp', instLevel_self, hz, Bool.and_true, beq_iff_eq,
    List.length_append, List.length_map, List.length_reverse, List.length_range, hidx]
  omega

end

/-! ## The statement of a constructor spine -/

/-- An evidently zero level translates to zero. -/
theorem evidentZero_tr {lps : List Name} :
    ∀ {l : Level} {a : Metalean.Level lps.length}, EvidentZero l = true →
      TrLevel lps l = some a → a = .zero
  | .zero, a, _, h => by cases h; rfl
  | .max x y, a, hz, h => by
    simp only [EvidentZero, Bool.and_eq_true] at hz
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x', hx, y', hy, rfl⟩ := h
    rw [evidentZero_tr hz.1 hx, evidentZero_tr hz.2 hy]
    ext ν
    simp [Metalean.Level.eval_max]
  | .imax x y, a, hz, h => by
    simp only [EvidentZero] at hz
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x', -, y', hy, rfl⟩ := h
    rw [evidentZero_tr hz hy, Metalean.Level.imax_zero]
  | .succ _, _, hz, _ | .param _, _, hz, _ | .mvar _, _, hz, _ => by simp [EvidentZero] at hz

/-- Peeling a `Π`. -/
theorem peelForalls_succ_forallE (k : Nat) (x : Name) (A b : Expr) (bi : BinderInfo) :
    peelForalls (k + 1) (.forallE x A b bi) = peelForalls k b := by
  simp only [peelForalls, Function.iterate_succ, Function.comp_apply, Option.bind_some,
    Expr.isForall, ↓reduceIte, Expr.bindingBody!]

/-- Peeling a `Π` off a term that is not one. -/
theorem peelForalls_succ_none {e : Expr} (h : e.isForall = false) (k : Nat) :
    peelForalls (k + 1) e = none := by
  simp only [peelForalls, Function.iterate_succ, Function.comp_apply, Option.bind_some, h,
    Bool.false_eq_true, ↓reduceIte]
  exact Function.iterate_fixed rfl k

/-- Universe instantiation commutes with peeling `Π`s. -/
theorem peelForalls_instLevels (ps : List Name) (us : List Level) :
    ∀ (k : Nat) {ty body : Expr}, peelForalls k ty = some body →
      peelForalls k (Pure.instLevels ps us ty) = some (Pure.instLevels ps us body)
  | 0, ty, body, h => by
    simp only [peelForalls, Function.iterate_zero, id, Option.some.injEq] at h ⊢
    rw [h]
  | k + 1, ty, body, h => by
    cases ty with
    | forallE x A b bi =>
      rw [peelForalls_succ_forallE] at h
      simp only [Pure.instLevels]
      rw [peelForalls_succ_forallE]
      exact peelForalls_instLevels ps us k h
    | _ => rw [peelForalls_succ_none rfl] at h; cases h

/-- Instantiating a loose variable commutes with peeling `Π`s, under the peeled binders. -/
theorem peelForalls_inst (a : Expr) :
    ∀ (k : Nat) {ty body : Expr} (d : Nat), peelForalls k ty = some body →
      peelForalls k (ty.instantiate1' a d) = some (body.instantiate1' a (d + k))
  | 0, ty, body, d, h => by
    simp only [peelForalls, Function.iterate_zero, id, Option.some.injEq] at h ⊢
    rw [h]; rfl
  | k + 1, ty, body, d, h => by
    cases ty with
    | forallE x A b bi =>
      rw [peelForalls_succ_forallE] at h
      simp only [Expr.instantiate1']
      rw [peelForalls_succ_forallE, peelForalls_inst a k (d + 1) h]
      congr 2
      omega
    | _ => rw [peelForalls_succ_none rfl] at h; cases h

/-- Instantiate the loose variables `|as| - 1, …, 0` of `e` by `as`, in order: the body of a type
under `|as|` binders after `piInst as`. -/
def instSeq : List Expr → Expr → Expr
  | [], e => e
  | a :: as, e => instSeq as (e.instantiate1' a as.length)

/-- `piInst` on a type with at least as many leading `Π`s as arguments. -/
theorem piInst_peel : ∀ (as : List Expr) {ty body : Expr},
    peelForalls as.length ty = some body → piInst as ty = some (instSeq as body)
  | [], ty, body, h => by
    simp only [List.length_nil, peelForalls, Function.iterate_zero, id, Option.some.injEq] at h
    simp [piInst, instSeq, h]
  | a :: as, ty, body, h => by
    cases ty with
    | forallE x A b bi =>
      rw [List.length_cons, peelForalls_succ_forallE] at h
      have h' := peelForalls_inst a as.length 0 h
      rw [Nat.zero_add] at h'
      simp only [piInst, instSeq]
      exact piInst_peel as h'
    | _ => rw [List.length_cons, peelForalls_succ_none rfl] at h; cases h

/-- Instantiating a variable at depth `s + m` of a term lifted by `m + 1` at `s`. -/
theorem inst_lift (x : Expr) (m : Nat) : ∀ (e : Expr) (s : Nat),
    (e.liftLooseBVars' s (m + 1)).instantiate1' x (s + m) = e.liftLooseBVars' s m
  | .bvar i, s => by
    simp only [Expr.liftLooseBVars', Expr.instantiate1']
    by_cases h : i < s
    · simp [h, show i < s + m by omega]
    · simp only [h, ↓reduceIte, show ¬ i + (m + 1) < s + m by omega,
        show ¬ i + (m + 1) = s + m by omega]
      congr 1
  | .app f a, s => by
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m f s, inst_lift x m a s]
  | .lam n t b bi, s => by
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m t s]
    rw [show s + m + 1 = (s + 1) + m by omega, inst_lift x m b (s + 1)]
  | .forallE n t b bi, s => by
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m t s]
    rw [show s + m + 1 = (s + 1) + m by omega, inst_lift x m b (s + 1)]
  | .letE n t v b nd, s => by
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m t s, inst_lift x m v s]
    rw [show s + m + 1 = (s + 1) + m by omega, inst_lift x m b (s + 1)]
  | .mdata d e, s => by simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m e s]
  | .proj S i e, s => by simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift x m e s]
  | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl

/-- `instSeq` undoes a lift by the number of its arguments. -/
theorem instSeq_lift : ∀ (as : List Expr) (e : Expr), instSeq as (e.liftLooseBVars' 0 as.length) = e
  | [], e => by simp [instSeq, liftLooseBVars'_zero]
  | a :: as, e => by
    have h := inst_lift a as.length e 0
    rw [Nat.zero_add] at h
    simp only [instSeq, List.length_cons, h, instSeq_lift as e]

/-- `instSeq` on the variable of the `i`-th binder. -/
theorem instSeq_bvar : ∀ (as : List Expr) (i : Nat) (hi : i < as.length),
    instSeq as (.bvar (as.length - 1 - i)) = as[i]
  | [], _, hi => absurd hi (by simp)
  | a :: as, 0, _ => by
    simp only [instSeq, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, Expr.instantiate1',
      Nat.lt_irrefl, ↓reduceIte, List.getElem_cons_zero]
    exact instSeq_lift as a
  | a :: as, i + 1, hi => by
    simp only [List.length_cons] at hi
    simp only [instSeq, List.length_cons, Expr.instantiate1',
      show as.length + 1 - 1 - (i + 1) < as.length by omega, ↓reduceIte, List.getElem_cons_succ]
    rw [show as.length + 1 - 1 - (i + 1) = as.length - 1 - i by omega]
    exact instSeq_bvar as i (by omega)

/-- `instSeq` on a constant spine. -/
theorem instSeq_spine (c : Name) (us : List Level) : ∀ (as args : List Expr),
    instSeq as (mkAppN (.const c us) args.toArray) =
      mkAppN (.const c us) (args.map (instSeq as)).toArray
  | [], args => by simp [instSeq]
  | a :: as, args => by
    simp only [instSeq]
    rw [mkAppN_eq_foldl, instantiate1'_foldl, ← mkAppN_eq_foldl]
    simp only [Expr.instantiate1']
    rw [instSeq_spine c us as, List.map_map]
    rfl

/-- The statement `piInst ps (cv.type)` of a field-less constructor at its parameters is its
inductive applied to `ps` and to indices, by the shape of constructor types (`IndBlock.ctorType`). -/
theorem ctor_statement {lps₀ : List Name} {I : Name} {np ni : Nat} {cvty body : Expr}
    {idx ps : List Expr} {vs : List Level}
    (hpeel : peelForalls np cvty = some body) (hidx : idx.length = ni) (hps : ps.length = np)
    (hbody : body = mkAppN (.const I (lps₀.map .param))
      ((List.range np).reverse.map (fun i => Expr.bvar (i + 0)) ++ idx).toArray)
    {st : Expr} (hpi : piInst ps (Pure.instLevels lps₀ vs cvty) = some st) :
    ∃ idx', idx'.length = ni ∧
      st = mkAppN (.const I ((lps₀.map .param).map (Pure.instLevel lps₀ vs))) (ps ++ idx').toArray := by
  have hp := peelForalls_instLevels lps₀ vs np hpeel
  rw [← hps] at hp
  rw [piInst_peel ps hp, Option.some.injEq] at hpi
  subst hpi hbody
  rw [mkAppN_eq_foldl, instLevels_foldl, ← mkAppN_eq_foldl,
    show Pure.instLevels lps₀ vs (Expr.const I (lps₀.map .param)) =
      .const I ((lps₀.map .param).map (Pure.instLevel lps₀ vs)) from rfl, instSeq_spine]
  refine ⟨(idx.map (Pure.instLevels lps₀ vs)).map (instSeq ps), by simp [hidx], ?_⟩
  have hbv : (List.range np).reverse.map
      (instSeq ps ∘ Pure.instLevels lps₀ vs ∘ fun i => Expr.bvar (i + 0)) = ps := by
    apply List.ext_getElem (by simp [hps])
    intro i h₁ h₂
    simp only [List.length_map, List.length_reverse, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, Function.comp_apply,
      Nat.add_zero, List.length_range]
    have := instSeq_bvar ps i (by omega)
    rw [hps] at this
    exact this
  simp only [List.map_append, List.map_map, hbv]

/-- An accumulator that writes the arguments of a spine from the right, as `Expr.getAppArgs`'s
does, fills the first positions of its array with the arguments of a constant spine. -/
theorem argsAux_spine (g : Expr → Array Expr → Nat → Array Expr)
    (happ : ∀ f a as i, g (.app f a) as i = g f (as.set! i a) (i - 1))
    (hconst : ∀ c us as i, g (.const c us) as i = as) (c : Name) (us : List Level) :
    ∀ (args : List Expr) (as : Array Expr), args.length ≤ as.size →
      (g (mkAppN (.const c us) args.toArray) as (args.length - 1)).toList =
        args ++ as.toList.drop args.length := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
    intro as _
    show (g (.const c us) as (0 - 1)).toList = [] ++ as.toList.drop 0
    rw [hconst]; simp
  | append_singleton init a ih =>
    intro as hle
    simp only [List.length_append, List.length_singleton] at hle
    have key : ∀ (l : List Expr) (i : Nat), i < l.length → (l.set i a).drop i = a :: l.drop (i + 1) := by
      intro l
      induction l with
      | nil => intro i hi; simp at hi
      | cons x l ih' =>
        intro i hi
        cases i with
        | zero => simp
        | succ i => simp [ih' i (by simpa using hi)]
    rw [SrcDefeq.mkAppN_snoc, happ, List.length_append, List.length_singleton,
      Nat.add_sub_cancel, ih _ (by simp; omega)]
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, Array.size_setIfInBounds,
      List.append_assoc, List.singleton_append]
    rw [key _ _ (by simp only [Array.length_toList]; omega)]

/-- The arguments of a constant spine. -/
theorem getAppArgs_mkAppN_const (c : Name) (us : List Level) (args : List Expr) :
    (mkAppN (.const c us) args.toArray).getAppArgs = args.toArray := by
  unfold Expr.getAppArgs
  simp only [SrcDefeq.getAppNumArgs_mkAppN_const]
  apply Array.toList_inj.mp
  rw [argsAux_spine _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c us args _ (by simp)]
  simp

/-- An atom spine is a constant spine with an atom head. -/
theorem atomSpine_spine {σ : EvalEnv} {e : Expr} (h : AtomSpine σ e) :
    ∃ c us args, e = mkAppN (.const c us) (args : List Expr).toArray ∧ σ.isAtom c = true := by
  induction h with
  | @const c us ha => exact ⟨c, us, [], rfl, ha⟩
  | @app f a _ ih =>
    obtain ⟨c, us, args, rfl, ha⟩ := ih
    exact ⟨c, us, args ++ [a], (SrcDefeq.mkAppN_snoc c us args a).symm, ha⟩

section
variable {B : Binds ζ} {P : List ConstantInfo} {lps : List Name}

/-- The statement of a typed atom spine translates to a type of the spine's translation, when
that type is an inductive type. -/
theorem spine_type_tr {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {mv st : Expr} (hsp : AtomSpine σ mv)
    (hst : σ.spineType? mv = some st) {mv' A : Metalean.Expr ζ lps.length 0}
    (htr : TrM E B lps .nil [] mv mv') (hA : E[.nil] ⊢ mv' : A) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {L : Fin ι.nlevels → Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length 0} {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length 0}
    (hAind : E[.nil] ⊢ A ≡ .ind η s L ps is typ) :
    ∃ Y, TrM E B lps .nil [] st Y ∧ E[.nil] ⊢ A ≡ Y typ := by
  obtain ⟨c, us, args, rfl, hat⟩ := atomSpine_spine hsp
  obtain ⟨ci, hci⟩ : ∃ ci, findDecl σ.decls c = some ci := by
    unfold EvalEnv.isAtom at hat
    split at hat
    · exact ⟨_, ‹_›⟩
    · cases hat
  simp only [EvalEnv.spineType?, SrcDefeq.getAppFn_mkAppN_const, getAppArgs_mkAppN_const,
    List.toList_toArray, hci, Option.bind_some] at hst
  have hcP := SrcDefeq.findDecl_sub hsub hci
  have hnd := henv.levelParams_nodup (findDecl_eq_some hcP).1
  have hname : ci.name = c := (findDecl_eq_some hcP).2
  obtain ⟨b, hb, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
  rw [hname] at htc
  by_cases hs : b.isSpecial
  · -- an inductive type former or `Quot` (the other saturating heads have their own rules)
    have hown : OwnRules ci = false := by
      simp only [EvalEnv.isAtom, hci, Bool.and_eq_true, Bool.not_eq_true'] at hat
      exact hat.1.2
    by_cases hq : ∃ qv, ci = .quotInfo qv
    · obtain ⟨qv, rfl⟩ := hq
      have hk : qv.kind = .type := by cases hk : qv.kind <;> simp [OwnRules, hk] at hown ⊢
      obtain ⟨η', hBq⟩ := henv.lookup_quot hcP
      rw [hk] at hBq
      obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hBq rfl htr
      cases hsat with
      | @quotType _ α r rest _ u hu =>
        exfalso
        rcases rest with _ | ⟨x, rest⟩
        · exact EraseProof.TypeEq.sort_ne_ind hE SrcDefeq.nil_ok (hA.quot_inv.symm.trans hAind)
        · obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv (as := rest) hA
          obtain ⟨A₁, B₁, hf, -, -⟩ := hF.app_inv
          exact EraseProof.TypeEq.sort_ne_forallE hE SrcDefeq.nil_ok hf.quot_inv.symm
      | quotEta hu hlt h₀ =>
        obtain ⟨ls', Tq, t₁, hus, hTq, htqT, rfl⟩ := SrcDefeq.quotTerm_typed henv hE hcP hBq hu h₀
        have htqT' := Metalean.Defeq.instLevel (ℓ := qv.levelParams.length) ls' htqT
        obtain ⟨_, hreg⟩ := htqT'.regular
        exact SrcDefeq.piInst_tr hE henv.metaOrderOK args (TrM.instLevels hus hTq) htqT'
          (Metalean.IsType.typeEq ⟨_, hreg⟩) (CasesWhred.forall₂_of_getElem? hlen hargs) hA hst
    obtain ⟨v, rfl⟩ : ∃ v, ci = .inductInfo v := by
      rcases SrcDefeq.special_kind henv hb hs hcP with h | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨v, rfl⟩
      · exact h
      · simp [OwnRules] at hown
      · simp [OwnRules] at hown
      · exact absurd ⟨v, rfl⟩ hq
    obtain ⟨ι', η', s', hBi, -⟩ := ProgEnv.lookup_ind henv (hname ▸ hcP)
    rw [← hname, hBi] at hb
    cases hb
    obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv (hname ▸ hBi) rfl htr
    cases hsat with
    | indSat ps' is' rest hls =>
      exfalso
      rcases rest with _ | ⟨r, rest⟩
      · obtain ⟨-, -, -, -, hT⟩ := hA.ind_inv
        exact EraseProof.TypeEq.sort_ne_ind hE SrcDefeq.nil_ok (hT.symm.trans hAind)
      · obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv (as := rest) hA
        obtain ⟨A₁, B₁, hf, -, -⟩ := hF.app_inv
        obtain ⟨-, -, -, -, hT⟩ := hf.ind_inv
        exact EraseProof.TypeEq.sort_ne_forallE hE SrcDefeq.nil_ok hT.symm
    | @indEta _ _ _ _ _ lsm hls hlt =>
      have htc' : TrM E B v.levelParams .nil [] (mkAppN (.const c (v.levelParams.map .param))
          ([] : List Expr).toArray) tc := htc
      have hTc₀ : TrM E B v.levelParams .nil [] v.type Tc := hTc
      have htcT₀ : E[.nil] ⊢ (tc : Metalean.Expr ζ v.levelParams.length 0) : Tc := htcT
      obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv (hname ▸ hBi) rfl htc'
      cases hsat₁ with
      | indSat ps₀ is₀ rest₀ hls₀ => simp at hlen₁; omega
      | @indEta _ _ _ _ _ ls₀ hls₀ _ =>
        obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
        have hnd' : v.levelParams.Nodup := hnd
        obtain ⟨hk, hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd' hls₀
        obtain ⟨ls', hus, hls'⟩ := SrcDefeq.trLevels_cast hls hk
        have htcT' := Metalean.Defeq.instLevel (ℓ := v.levelParams.length) ls' htcT₀
        have hf : E[.nil] ⊢ (Metalean.Frontend.indTerm (E.get η').block η' s' lsm).wkClosed :
            Metalean.Expr.instL ls' Tc := by
          have hit := indTerm_instL (E.get η').block η' s' ls₀ ls'
          have hlseq : ls₀{ls'} = lsm := by
            funext i
            show (ls₀ i){ls'} = lsm i
            rw [hls₀' i]
            show ls' (Fin.cast hk i) = lsm i
            rw [hls']
            rfl
          rw [hlseq] at hit
          show E[.nil] ⊢ Metalean.Frontend.indTerm (E.get η').block η' s' lsm : _
          rw [← hit]
          exact htcT'
        obtain ⟨_, hreg⟩ := hf.regular
        exact SrcDefeq.piInst_tr hE henv.metaOrderOK args (TrM.instLevels hus hTc₀) hf
          (Metalean.IsType.typeEq ⟨_, hreg⟩) (CasesWhred.forall₂_of_getElem? hlen hargs) hA hst
  · -- a constant: its spines are applications
    have hns : ¬ SpecialHead B (.const c us) := by
      rintro ⟨c', us', b', hfn, hb', hs'⟩
      cases hfn; rw [hb] at hb'; cases hb'; exact hs hs'
    obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns args htr
    cases b with
    | const η' =>
      obtain ⟨ls, rfl, hls⟩ := SrcDefeq.trM_const_inv' hb hh
      obtain ⟨ls₀, rfl, hls₀⟩ := SrcDefeq.trM_const_inv' hb htc
      obtain ⟨hk, hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd hls₀
      obtain ⟨ls', hus, hls'⟩ := SrcDefeq.trLevels_cast hls hk
      have hTc' := TrM.instLevels hus hTc
      have htcT' := Metalean.Defeq.instLevel (ℓ := ci.levelParams.length) ls' htcT
      have hlseq : ls₀{ls'} = ls := by
        funext i
        show (ls₀ i){ls'} = ls i
        rw [hls₀' i]
        show ls' (Fin.cast hk i) = ls i
        rw [hls']
        rfl
      have hf : E[.nil] ⊢ Metalean.Expr.const η' ls : Tc{ls'} := by
        rw [← hlseq]; exact htcT'
      obtain ⟨_, hreg⟩ := htcT'.regular
      exact SrcDefeq.piInst_tr hE henv.metaOrderOK args hTc' hf
        (Metalean.IsType.typeEq ⟨_, hreg⟩) has hA hst
    | _ => exact absurd rfl hs

end

/-! ## A field-less constructor's η-term applied to its parameters -/

/-- A term typed by a Π over a closed telescope, applied to arguments of the telescope's types,
is typed by the body under the arguments. -/
theorem apps_pi {ℓ : Nat} {m : Nat} (Δ : Metalean.Ctx ζ ℓ 0 m) :
    ∀ {f : Metalean.Expr ζ ℓ 0} {T : Metalean.Expr ζ ℓ m} (xs : Fin m → Metalean.Expr ζ ℓ 0),
      E[.nil] ⊢ f : Δ.pi T →
      (∀ p : Fin m, E[.nil] ⊢ xs p :
        (Δ.entry (Nat.zero_le p.val) p.isLt).subst fun previous : Fin p.val =>
          xs (previous.castLE (by omega))) →
      E[.nil] ⊢ f.apps xs : T.subst xs := by
  induction Δ with
  | nil =>
    intro f T xs hf _
    rw [Metalean.Expr.apps_zero, Metalean.Expr.subst_closed]
    exact hf
  | @snoc b Δ t ih =>
    intro f T xs hf hxs
    let xs₀ : Fin b → Metalean.Expr ζ ℓ 0 := fun p => xs p.castSucc
    have h₀ := ih (T := .forallE t T) xs₀ hf fun p => by
      have := hxs p.castSucc
      rw [Metalean.Ctx.entry_snoc_of_lt _ _ _ _ (by simp)] at this
      exact this
    have hlast : E[.nil] ⊢ xs (Fin.last b) : t.subst xs₀ := by
      have := hxs (Fin.last b)
      simp only [Fin.val_last, Metalean.Ctx.entry_snoc_self] at this
      exact this
    obtain ⟨_, hr⟩ := h₀.regular
    obtain ⟨l₁, l₂, hA, hB, -⟩ := hr.forallE_ty_inv
    have happ := Metalean.Defeq.appDF hA hB h₀ hlast (hB.inst_congr hlast)
    rw [Metalean.Expr.apps_last]
    have hx : Metalean.Subst.extend xs₀ (xs (Fin.last b)) = xs := Fin.snoc_init_self xs
    rw [Metalean.Expr.inst_subst_lift, hx] at happ
    exact happ

/-- The η-term of a field-less constructor (`Metalean.Frontend.ctorTerm`), typed, applied to
parameters of the parameter types, is typed. -/
theorem ctorTerm_apps_typed {ℓ : Nat} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ls : Fin ι.nlevels → Metalean.Level ℓ} {order : List Nat} {t₀ T₀ : Metalean.Expr ζ ℓ 0}
    (ht : Metalean.Frontend.ctorTerm (E.get η).block η s c ls order = .ok t₀)
    (htyped : E[.nil] ⊢ t₀ : T₀)
    (hf : (ι.ctors s c).nfields = 0) (hr : (ι.ctors s c).nrecFields = 0)
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ 0)
    (hps : ∀ p, E[.nil] ⊢ ps p : (E.get η).block.paramType ls ps p) :
    ∃ T, E[.nil] ⊢ t₀.wkClosed.appList (List.ofFn ps) : T := by
  unfold Metalean.Frontend.ctorTerm at ht
  dsimp only at ht
  rcases hπ : Metalean.Frontend.orderMaps? order
        ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with _ | ⟨π, πinv⟩
  · rw [hπ] at ht; cases ht
  rw [hπ] at ht
  dsimp only at ht
  obtain ⟨x, hx⟩ : ∃ x, Metalean.Ctx.permute? (k := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
      (by simp [Nat.add_assoc]) π πinv (((E.get η).block.ctors s c).fieldTele η ls
        (fun p => .var p)) = x := ⟨_, rfl⟩
  rw [hx] at ht
  rcases x with _ | fields'
  · cases ht
  dsimp only at ht
  obtain ⟨y, hy⟩ : ∃ y, Fin.mapM (m := Option) (fun f : Fin (ι.ctors s c).nfields =>
      (do let j ← πinv (Fin.castAdd (ι.ctors s c).nrecFields f)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, Fin.mapM (m := Option) (fun r : Fin (ι.ctors s c).nrecFields =>
      (do let j ← πinv (Fin.natAdd (ι.ctors s c).nfields r)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = z := ⟨_, rfl⟩
  rw [hy, hz] at ht
  rcases y with _ | fds
  · cases ht
  rcases z with _ | recFds
  · cases ht
  dsimp only at ht
  cases ht
  obtain ⟨U, -, -, hTU⟩ := lam_tele_inv .nil _ htyped
  have hpi := hTU.conv htyped
  let xs : Fin (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) →
      Metalean.Expr ζ ℓ 0 := Fin.append ps fun j => absurd j.isLt (by omega)
  have hxs_left : ∀ (j : Nat) (h : j < ι.nparams) (h' : j < ι.nparams +
      ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)), xs ⟨j, h'⟩ = ps ⟨j, h⟩ :=
    fun j h h' => CasesWhred.append_val_left _ _ h h'
  rw [appList_eq_apps _ xs (by simp; omega) fun j => by
    have hj : j.val < ι.nparams := by omega
    simp [List.getElem?_ofFn, hj, hxs_left j.val hj j.isLt]]
  refine ⟨_, apps_pi _ xs hpi fun p => ?_⟩
  have hp : p.val < ι.nparams := by omega
  rw [Metalean.Ctx.entry_append_left _ _ _ hp, ← Metalean.Ctx.entry_instL, hxs_left _ hp]
  have := hps ⟨p.val, hp⟩
  unfold Metalean.Inductive.paramType at this
  convert this using 2
  funext previous
  exact hxs_left _ (by omega) _

/-! ## The proof-irrelevant ι -/

/-- Instantiating at the instances of the parameters is instantiating directly. -/
theorem instLevel_params_comp (ps : List Name) (vs : List Level) : ∀ u : Level,
    Pure.instLevel ps ((ps.map .param).map (Pure.instLevel ps vs)) u = Pure.instLevel ps vs u
  | .zero => rfl
  | .succ u => by simp only [Pure.instLevel, instLevel_params_comp ps vs u]
  | .max a b => by
    simp only [Pure.instLevel, instLevel_params_comp ps vs a, instLevel_params_comp ps vs b]
  | .imax a b => by
    simp only [Pure.instLevel, instLevel_params_comp ps vs a, instLevel_params_comp ps vs b]
  | .mvar _ => rfl
  | .param n => by
    have key : ∀ (l : List Name), (l.zip ((l.map Level.param).map (Pure.instLevel ps vs))).find?
        (·.1 == n) = if n ∈ l then some (n, Pure.instLevel ps vs (.param n)) else none := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih =>
        simp only [List.map_cons, List.zip_cons_cons, List.find?_cons, List.mem_cons, ih]
        by_cases hx : x = n
        · subst hx; simp
        · have : (x == n) = false := by simpa using hx
          simp [this, Ne.symm hx]
    simp only [Pure.instLevel]
    rw [key]
    by_cases hn : n ∈ ps
    · simp only [hn, ↓reduceIte]; rfl
    · have hnone : (ps.zip vs).find? (·.1 == n) = none :=
        List.find?_eq_none.mpr fun q hq h => hn (by
          simp only [beq_iff_eq] at h
          exact h ▸ (List.of_mem_zip hq).1)
      simp only [hn, ↓reduceIte, hnone]

/-- `instLevel_params_comp` on terms. -/
theorem instLevels_params_comp (ps : List Name) (vs : List Level) : ∀ e : Expr,
    Pure.instLevels ps ((ps.map .param).map (Pure.instLevel ps vs)) e = Pure.instLevels ps vs e
  | .sort u => by simp only [Pure.instLevels, instLevel_params_comp]
  | .const c ls => by
    simp only [Pure.instLevels]
    congr 1
    exact List.map_congr_left fun u _ => instLevel_params_comp ps vs u
  | .app f a => by
    simp only [Pure.instLevels, instLevels_params_comp ps vs f, instLevels_params_comp ps vs a]
  | .lam _ t b _ => by
    simp only [Pure.instLevels, instLevels_params_comp ps vs t, instLevels_params_comp ps vs b]
  | .forallE _ t b _ => by
    simp only [Pure.instLevels, instLevels_params_comp ps vs t, instLevels_params_comp ps vs b]
  | .letE _ t v b _ => by
    simp only [Pure.instLevels, instLevels_params_comp ps vs t, instLevels_params_comp ps vs v,
      instLevels_params_comp ps vs b]
  | .mdata _ e => by simp only [Pure.instLevels, instLevels_params_comp ps vs e]
  | .proj _ _ e => by simp only [Pure.instLevels, instLevels_params_comp ps vs e]
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => rfl

section
variable {B : Binds ζ} {P : List ConstantInfo} {lps : List Name}

/-- Two typed translations of the same type are equal types. -/
theorem trM_typeEq (hE : EnvWF E) {e : Expr} {Y₁ Y₂ : Metalean.Expr ζ lps.length 0}
    (h₁ : TrM E B lps .nil [] e Y₁) (h₂ : TrM E B lps .nil [] e Y₂) (hY₁ : E[.nil] ⊢ Y₁ typ)
    (hY₂ : E[.nil] ⊢ Y₂ typ) : E[.nil] ⊢ Y₁ ≡ Y₂ typ := by
  obtain ⟨u₁, hu₁⟩ := hY₁
  obtain ⟨u₂, hu₂⟩ := hY₂
  exact TypeEq.ofDefEq (DCong.defeq₂ hE (h₁.dcong h₂ (LocCong.refl [])) SrcDefeq.nil_ok
    SrcDefeq.nil_ok (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hu₂⟩ hu₁)

/-- `SrcEval.casesProof` preserves typed translations up to definitional equality: the major's
value, a neutral proof, has a proposition as type (the recursor's major type, at the inductive's
sort, `SrcProof.casesOn_recr`); the field-less constructor applied to the parameters of the
major's statement translates to a proof of the same proposition (`SrcProof.ctor_statement`,
`SrcProof.ctorTerm_apps_typed`); proof irrelevance identifies them, and ι on the constructor
(`SrcDefeq.case_casesIota`) continues with the alternative. Reference: `eval_iota_sing`
(`MR E/EWcbvEval.v:162`); `proofIrrel` (`ML Typing/Defs.lean:158`); DV-24. -/
theorem proofSound {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) : SrcDefeq.ProofSound σ E B lps := by
  intro c us vs iv as ps m mv st alt v l cn cv hcs hlen hm hsp hl hz hcn hcv hnf hst hps hpi halt
    ihm ihb t T he ht
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h =>
    SrcDefeq.findDecl_sub hsub h
  obtain ⟨d, R, -, -, -, -, -, -, -, hiv, -⟩ := casesOn_shape hcs
  obtain ⟨ι, η, s, hBT, -, -, -⟩ := ProgEnv.lookup_ind henv (hP hiv)
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨_, _, _, _, hIB⟩, -, hfd, -, hindB, -⟩ :=
    CasesWhred.ProgEnv.block henv η
  have hmemI : ConstantInfo.inductInfo (Is s) ∈ IndBlock.decls Is Cs Rs := by
    simp [IndBlock.decls, List.mem_ofFn]
  have hmemC : ∀ k, ConstantInfo.ctorInfo (Cs s k) ∈ IndBlock.decls Is Cs Rs := fun k => by
    simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
    exact .inl (.inr ⟨_, ⟨s, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩)
  have hivs : iv = Is s := by
    have h1 := hP hiv
    have hfdI : findDecl P (Is s).name = some (.inductInfo (Is s)) := hfd _ hmemI
    rw [hindB _ _ hBT, hfdI] at h1
    cases h1; rfl
  subst hivs
  obtain ⟨-, hlpI, -, hInp, hIni, hIctors, -, -⟩ := hIB.ind s
  have hn1 : ι.nctors s = 1 := by
    have := congrArg List.length (hIctors.symm.trans hcn); simpa using this
  obtain ⟨k0, hk0⟩ : ∃ k0 : Fin (ι.nctors s), k0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hcn0 : (Cs s k0).name = cn := by
    have h := congrArg (fun l => l[0]?) (hIctors.symm.trans hcn)
    simp only [List.getElem?_ofFn, List.getElem?_cons_zero] at h
    obtain ⟨_, h⟩ := by simpa using h
    rw [show k0 = ⟨0, by omega⟩ from Fin.ext hk0]
    exact h
  have hcvs : cv = Cs s k0 := by
    have h1 := hP hcv
    have hfdC : findDecl P (Cs s k0).name = some (.ctorInfo (Cs s k0)) := hfd _ (hmemC k0)
    rw [← hcn0, hfdC] at h1
    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at h1
    exact h1.symm
  subst hcvs
  obtain ⟨-, hlpC, hindC, hcidx, hnpC, hnfC, -, -⟩ := hIB.ctor s k0
  have hnf0 : (ι.ctors s k0).nfields = 0 := by omega
  have hnr0 : (ι.ctors s k0).nrecFields = 0 := by omega
  -- the major's value is a proof of the recursor's major type, a proposition
  have hjlt : casesMajor (Is s) < as.length := (List.getElem?_eq_some_iff.mp hm).1
  obtain ⟨t₂, ht₂, hd2⟩ := SrcDefeq.major_congr henv hE hsub hcs hm ihm he ht
  obtain ⟨ι₂, η₂, s₂, L, l', ps₀, ms, mins, is₀, mv'', hBT₂, hmv, hred, hlev, -, -⟩ :=
    casesOn_recr henv hE hsub hcs (by simp [hlen]) (List.getElem?_set_self hjlt) ht₂
  rw [hBT] at hBT₂
  cases hBT₂
  have hR := (WHRedS.defeq hE SrcDefeq.nil_ok hred hd2.right).right
  obtain ⟨-, hps₀, -, -, his₀, hmaj⟩ := Metalean.Defeq.recr_typed hE SrcDefeq.nil_ok hR
  have hind := Metalean.Defeq.indDF hps₀ his₀
  rw [evidentZero_tr hz (hlev l hl)] at hind
  -- the major's statement: the inductive applied to the parameters `ps`
  obtain ⟨Y, hY, hPY⟩ := spine_type_tr henv hE hsub hsp hst hmv hmaj
    (Metalean.IsType.typeEq ⟨_, hind⟩)
  obtain ⟨body, idx, hpeel, hidx, hbody⟩ := hIB.ctorType s k0
  rw [hnf, Nat.add_zero] at hpeel
  rw [hnf] at hbody
  subst hlpC
  obtain ⟨idx', hidx', rfl⟩ := ctor_statement hpeel hidx (hps.trans hnpC) hbody hpi
  obtain ⟨args', hlenA, hargsA, hsatY⟩ := TrM.special_inv hBT rfl hY
  cases hsatY with
  | indEta _ hlt => exfalso; simp at hlenA; omega
  | @indSat _ _ _ _ Ly ps' is' rest hlsY =>
  have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hlenA; omega)
  subst hrest
  have hpsTr : List.Forall₂ (TrM E B lps .nil []) ps (List.ofFn ps') := by
    refine CasesWhred.forall₂_of_getElem? (by simp; omega) fun j x y h1 h2 => ?_
    have hj : j < ps.length := (List.getElem?_eq_some_iff.mp h1).1
    refine hargsA j x y ?_ ?_
    · rw [List.getElem?_append_left hj]; exact h1
    · rw [List.append_nil, List.getElem?_append_left (by simp; omega)]; exact h2
  obtain ⟨_, hYs⟩ := hPY.right
  have hYs' : E[.nil] ⊢ Metalean.Expr.ind η s _ ps' is' : _ := hYs
  have hps' := (Metalean.Defeq.ind_typed hE hYs').1
  -- the constructor applied to the parameters translates to a proof of the same proposition
  obtain ⟨ι', η', s', k', order, hBcn, hcidx', -, -, -, hBind⟩ :=
    ProgEnv.lookup_ctor henv (hP hcv)
  rw [hindC, hBT] at hBind
  cases hBind
  obtain rfl : k0 = k' := Fin.ext (by omega)
  have hnd : (Cs s k0).levelParams.Nodup := henv.levelParams_nodup (findDecl_eq_some (hP hcv)).1
  have hk : ι.nlevels = (Cs s k0).levelParams.length := hIB.levels.symm
  obtain ⟨ls', hus, hls'⟩ := SrcDefeq.trLevels_cast hlsY hk
  obtain ⟨Tc, tc, hTc₀, htc₀, htcT₀⟩ : ∃ Tc tc : Metalean.Expr ζ (Cs s k0).levelParams.length 0,
      TrM E B (Cs s k0).levelParams .nil [] (Cs s k0).type Tc ∧
      TrM E B (Cs s k0).levelParams .nil []
        (mkAppN (.const cn ((Cs s k0).levelParams.map .param)) ([] : List Expr).toArray) tc ∧
      E[.nil] ⊢ tc : Tc := by
    obtain ⟨_, _, Tc, tc, h1, h2, h3⟩ := henv.lookup hE (hP hcv)
    exact ⟨Tc, tc, h1, by rw [← hcn0]; exact h2, h3⟩
  have hhead : TrM E B lps .nil [] (.const cn (((Cs s k0).levelParams.map .param).map
      (Pure.instLevel (Cs s k0).levelParams vs))) (Metalean.Expr.instL ls' tc) := by
    have h : TrM E B lps .nil [] (Pure.instLevels (Cs s k0).levelParams
        (((Cs s k0).levelParams.map .param).map (Pure.instLevel (Cs s k0).levelParams vs))
        (.const cn ((Cs s k0).levelParams.map .param))) (Metalean.Expr.instL ls' tc) :=
      TrM.instLevels hus htc₀
    simp only [Pure.instLevels] at h
    rwa [params_instLevel hnd (by simp)] at h
  obtain ⟨c', hc'tr, hc'red⟩ := TrM.apps hhead hpsTr
  have htcT' := Metalean.Defeq.instLevel (ℓ := (Cs s k0).levelParams.length) ls' htcT₀
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, E[.nil] ⊢ (Metalean.Expr.instL ls' tc).appList (List.ofFn ps') : T₁ := by
    obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv hBcn rfl htc₀
    cases hsat₁ with
    | ctorSat ps₀' fs rest₀ fds recFds hls₀ hfs _ _ =>
      have hnp0 : ι.nparams = 0 := by simp at hlen₁; omega
      have hofn : List.ofFn ps' = [] := by simp [hnp0]
      rw [hofn]
      exact ⟨_, htcT'⟩
    | @ctorEta _ _ _ _ _ _ _ ls₀ t₀ hls₀ _ hct =>
      obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
      obtain ⟨hk₀, hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd hls₀
      have hct' := ctorTerm_instL _ _ _ _ _ _ ls' hct
      have hlseq : ls₀{ls'} = Ly := by
        funext i
        show (ls₀ i){ls'} = Ly i
        rw [hls₀' i]
        show ls' (Fin.cast _ i) = Ly i
        rw [hls']
        rfl
      rw [hlseq] at hct'
      exact ctorTerm_apps_typed hct' htcT' hnf0 hnr0 ps' hps'
  have hpi' := hpi
  rw [← instLevels_params_comp] at hpi'
  obtain ⟨_, hreg⟩ := htcT'.regular
  obtain ⟨Y'', hY'', hTY''⟩ := SrcDefeq.piInst_tr hE henv.metaOrderOK ps
    (TrM.instLevels hus hTc₀) htcT' (Metalean.IsType.typeEq ⟨_, hreg⟩) hpsTr hT₁ hpi'
  have hc'T : E[.nil] ⊢ c' : T₁ := (WHRedS.defeq hE SrcDefeq.nil_ok hc'red hT₁).right
  have hYY : E[.nil] ⊢ Y'' ≡ _ typ := trM_typeEq hE hY'' hY hTY''.right hPY.right
  have hc'P := ((hTY''.trans hYY).trans hPY.symm).conv hc'T
  -- proof irrelevance at the major's type, then ι on the constructor
  have hSound : SrcDefeq.Sound E B lps m (mkAppN (.const cn (((Cs s k0).levelParams.map .param).map
      (Pure.instLevel (Cs s k0).levelParams vs))) ps.toArray) := by
    intro x X hx hxX
    obtain ⟨y, hy, hxy⟩ := ihm hx hxX
    have hymv : E[.nil] ⊢ y ≡ mv'' : X := DCong.defeq₂ hE (hy.dcong hmv (LocCong.refl []))
      SrcDefeq.nil_ok SrcDefeq.nil_ok (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hmaj⟩ hxy.right
    have hXP := Defeq.uniqTy hE SrcDefeq.nil_ok hymv.right hmaj
    have hirr := Metalean.Defeq.proofIrrel hind hmaj hc'P
    exact ⟨c', hc'tr, hxy.trans (hymv.trans (hXP.symm.conv hirr))⟩
  have hcvv : CtorValue σ (Is s).name (mkAppN (.const cn (((Cs s k0).levelParams.map .param).map
      (Pure.instLevel (Cs s k0).levelParams vs))) ps.toArray) 0 [] :=
    ⟨cn, _, Cs s k0, ps, hcv, hindC, by rw [hcidx, hk0], hps, by simp [hnf],
      by rw [List.append_nil]⟩
  exact (SrcDefeq.case_casesIota henv hE hsub hcs hlen hm hcvv (by simpa using halt) hSound ihb).1
    he ht

end

end SrcProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name}

/-- Subject reduction: a typed translation of a term that evaluates is definitionally equal, at
its type, to a translation of the value. Reference: `subject_reduction_eval`
(`MR P/PCUICWcbvEval.v`), per rule `WHRed.*_defeq` (`ML Metatheory/SubjectReduction.lean`). -/
theorem SrcEval.defeq {e v : Expr} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {t T : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] e t) (ht : E[.nil] ⊢ t : T) (hev : SrcEval σ e v) :
    ∃ t', TrM E B lps .nil [] v t' ∧ E[.nil] ⊢ t ≡ t' : T :=
  (SrcDefeq.sound_of henv hE hsub (SrcProof.proofSound henv hE hsub) hev).1 he ht

/-- Erasability is preserved by evaluation: the erasable translation of the term is definitionally
equal, at its type, to a translation of the value, which therefore has the same type. Reference:
`Is_type_eval` (`MR E/ErasureCorrectness.v`). -/
theorem ErasableS.eval {e v : Expr} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {t T : Metalean.Expr ζ lps.length 0}
    (_he : TrM E B lps .nil [] e t) (_ht : E[.nil] ⊢ t : T) (hev : SrcEval σ e v)
    (h : ErasableS E B lps .nil [] e) : ErasableS E B lps .nil [] v := by
  obtain ⟨t₀, htr, T₀, ht₀, hT₀⟩ := h
  obtain ⟨t', htr', hd⟩ := SrcEval.defeq henv hE hsub htr ht₀ hev
  exact ⟨t', htr', T₀, hd.right, hT₀⟩

end

end EraseProof
