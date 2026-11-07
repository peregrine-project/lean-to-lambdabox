import EraseProof.Simulation.Quot
import EraseProof.Simulation.Rec
import EraseProof.Statements

/-!
# The relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`), by induction on the source evaluation `e ⇓ v`,
with the motive strengthened to every head-β-reduct `X` of `e` (`SimIota.HeadBeta`): `X ⇓ v`, and
every erasure of a typed translation of `X` evaluates in λ□ to an erasure of `v`. For `X = e` each
rule is its case lemma (`Simulation/Cases.lean`, `Simulation/Ind.lean`, `Simulation/Iota.lean`,
`Simulation/Quot.lean`);
the ι cases use the motive at the head-β-reducts of the alternative applied to the fields. A
proper head-β-reduct exists only for an application whose head reduces to a λ: then `e` evaluates
by `beta` or `appCong`, and the reduct evaluates by the same rule from the reduct of the head, or
is the reduct of the β-redex the rule evaluates.
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

namespace SimMain

open SimIota

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- A spine with an argument appended. -/
theorem app_mkAppN (c : Name) (us : List Level) (as : List Expr) (a : Expr) :
    Expr.app (mkAppN (.const c us) as.toArray) a = mkAppN (.const c us) (as ++ [a]).toArray := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl

/-- The head of a short application is a short spine with fewer arguments than its arity. -/
theorem short_head {XF a : Expr} (h : ShortSpine σ (.app XF a)) :
    ∃ c us ar as, XF = mkAppN (.const c us) (as : List Expr).toArray ∧
      specialArity σ c = some ar ∧ as.length + 1 ≤ ar := by
  obtain ⟨c, us, ar, hfn, har, hle⟩ := h
  have hfn' : XF.getAppFn = .const c us := by simpa [Expr.getAppFn] using hfn
  obtain ⟨as, rfl⟩ := eq_mkAppN_of_getAppFn hfn'
  refine ⟨c, us, ar, as, rfl, har, ?_⟩
  rw [SrcDefeq.getAppNumArgs_app, SrcDefeq.getAppNumArgs_mkAppN_const] at hle
  exact hle

/-- The simulation for every head-β-reduct of the evaluated term. -/
theorem sim (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hinj : KernameInj σ.decls) (hbinj : BlockNamesInj σ.decls) (harity : ArityTypes σ.decls)
    {e v : Expr} (hev : SrcEval σ e v) :
    ∀ X, HeadBeta σ e X → SrcEval σ X v ∧ ErasesSim E B lps σ lenv X v := by
  have hsat : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      {us : List Level} {as₁ as₂ : List (Metalean.Expr ζ lps.length 0)}
      {t₁ t T : Metalean.Expr ζ lps.length 0},
      SatTr E lps (.ind η s) us as₁ t₁ → SatTr E lps (.ind η s) us (as₁ ++ as₂) t →
      E[.nil] ⊢ t : T → ∃ T₁, E[.nil] ⊢ t₁ : T₁ :=
    by
      intro ι η s us as₁ as₂ t₁ t T h₁ h ht
      exact SatTr.typed (b := .ind η s) hE SrcDefeq.nil_ok (fun _ _ _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) h₁ h ht
  have spine : ∀ {c us} {as : List Expr} {X}, HeadBeta σ (mkAppN (.const c us) as.toArray) X →
      X = mkAppN (.const c us) as.toArray := fun hX => hX.eq_of_head fun _ _ _ n A b bi h => by
    rw [SrcDefeq.getAppFn_mkAppN_const] at h; cases h
  induction hev with
  | @beta f a x A b bi a' v hns hf ha hb ihf iha ihb =>
    intro X hX
    rcases hX.app_inv with rfl | ⟨hfix, ⟨XF, hXF, rfl⟩ | ⟨n', A', b', bi', hFl, hX'⟩⟩
    · exact ⟨.beta hns hf ha hb, erases_correct_beta henv hE hsub hns hf ha hb (ihf _ .refl).2
        (iha _ .refl).2 (ihb _ .refl).2⟩
    · have haa : a' = a := hfix _ ha
      subst haa
      obtain ⟨hXFe, hXFs⟩ := ihf XF hXF
      by_cases hsh : ShortSpine σ (.app XF a')
      · obtain ⟨c, us, ar, as, rfl, har, hle⟩ := short_head hsh
        have heta := eval_short hXFe har (by omega)
        obtain ⟨ar', har', -, hstep1, hstep2⟩ := etaSpine?_snoc a' heta
        rw [har] at har'
        cases har'
        rw [app_mkAppN]
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · have he' := hstep1 hlt
          obtain ⟨_, _, _, _, hlam⟩ := SimInd.etaSpine?_lam he'
          have hvv : v = b.instantiate1' a' := fixed_atom (by rw [hlam]; trivial) _ hb
          subst hvv
          exact ⟨.eta he', erases_correct_eta henv hE hsub he'⟩
        · rw [← hstep2 heq]
          exact ihb _ .refl
      · exact ⟨.beta hsh hXFe ha hb, erases_correct_beta henv hE hsub hsh hXFe ha hb hXFs
          (iha _ .refl).2 (ihb _ .refl).2⟩
    · obtain ⟨hl, -⟩ := ihf _ hFl
      have hll := fixed_atom (show SrcAtom (.lam n' A' b' bi') from trivial) _ hl
      cases hll
      have haa : a' = a := hfix _ ha
      subst haa
      exact ihb X hX'
  | zeta hv hb ihv ihb =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.zeta hv hb, erases_correct_zeta henv hE hsub hv hb (ihv _ .refl).2 (ihb _ .refl).2⟩
  | delta hu hb ih =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.delta hu hb, erases_correct_delta henv hE hsub hinj hu hb (ih _ .refl).2⟩
  | constAtom ha =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.constAtom ha, erases_correct_constAtom ha⟩
  | eta he =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.eta he, erases_correct_eta henv hE hsub he⟩
  | ctor hc hlen hlen' hev ih =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.ctor hc hlen hlen' hev, erases_correct_ctor henv hE hsub hbinj hc hlen hlen' hev
      fun i a v h₁ h₂ => (ih i a v h₁ h₂ _ .refl).2⟩
  | casesIota hcs hlen hm hmv hcv halt hv ihm ihb =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.casesIota hcs hlen hm hmv hcv halt hv, erases_correct_casesIota henv hE hsub hbinj
      harity hcs hlen hm hmv hcv halt hv (ihm _ .refl).2 fun X hX => (ihb X hX).2⟩
  | casesLitZero hcs hnat hlen hm hmv halt hv ihm ihb =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.casesLitZero hcs hnat hlen hm hmv halt hv, erases_correct_casesLitZero henv hE hsub
      hbinj hcs hnat hlen hm hmv halt hv (ihm _ .refl).2 (ihb _ .refl).2⟩
  | casesLitSucc hcs hnat hlen hm hmv halt hv ihm ihb =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.casesLitSucc hcs hnat hlen hm hmv halt hv, erases_correct_casesLitSucc henv hE hsub
      hbinj hcs hnat hlen hm hmv halt hv (ihm _ .refl).2 fun X hX => (ihb X hX).2⟩
  | casesProof hcs hlen hm hmv hat hl hz hcn hcv hnf hst hps hpi halt hv ihm ihb =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.casesProof hcs hlen hm hmv hat hl hz hcn hcv hnf hst hps hpi halt hv,
      erases_correct_casesProof henv hE hsub hcs hlen hm hmv hat hl hz hcn hcv hnf hst hps hpi
        halt hv (ihb _ .refl).2⟩
  | quotMk hc hk ha iha =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.quotMk hc hk ha, erases_correct_quotMk henv hE hsub hc hk ha (iha _ .refl).2⟩
  | recIota hcr hall hcT hblk hni hshape hihs hps hms hmins hlm hmv hmaj hcv hmi hmk hrfs hrl hih hv
      ihm ihmaj ihih ihv =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.recIota hcr hall hcT hblk hni hshape hihs hps hms hmins hlm hmv hmaj hcv hmi hmk hrfs hrl
      hih hv, SimRec.erases_correct_recIota henv hE hsub hbinj hcr hall hcT hblk hni hshape hihs hps
      hms hmins hlm hmv hmaj hcv hmi hmk hrfs hrl hih hv
      (fun i m mv h1 h2 => (ihm i m mv h1 h2 _ .refl).2) (ihmaj _ .refl).2
      (fun i f w h1 h2 => (ihih i f w h1 h2 _ .refl).2) (ihv _ .refl).2⟩
  | quotLift hc hk hf hq hc' hk' hb ihf ihq ihb =>
    intro X hX
    obtain rfl := spine hX
    exact ⟨.quotLift hc hk hf hq hc' hk' hb, erases_correct_quotLift henv hE hsub hc hk hf hq hc'
      hk' hb (ihf _ .refl).2 (ihq _ .refl).2 (ihb _ .refl).2⟩
  | proj hm hcv ha ih =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.proj hm hcv ha, erases_correct_proj henv hE hsub hbinj hm hcv ha (ih _ .refl).2⟩
  | projProp hS hm hv ih =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.projProp hS hm hv, erases_correct_projProp henv hE hsub hbinj hS hm hv (ih _ .refl).2⟩
  | lit =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.lit, erases_correct_lit henv hsub hbinj⟩
  | @appCong f a f' a' hns hf hnb ha ihf iha =>
    intro X hX
    rcases hX.app_inv with rfl | ⟨hfix, ⟨XF, hXF, rfl⟩ | ⟨n', A', b', bi', hFl, -⟩⟩
    · exact ⟨.appCong hns hf hnb ha, erases_correct_appCong henv hE hsub hsat hns hf hnb ha
        (ihf _ .refl).2 (iha _ .refl).2⟩
    · have haa := hfix _ ha
      subst haa
      obtain ⟨hXFe, hXFs⟩ := ihf XF hXF
      have hsh : ¬ ShortSpine σ (.app XF a') := by
        intro h
        obtain ⟨c, us, ar, as, rfl, har, hle⟩ := short_head h
        obtain ⟨_, _, _, _, rfl⟩ := SimInd.etaSpine?_lam (eval_short hXFe har (by omega))
        exact hnb trivial
      exact ⟨.appCong hsh hXFe hnb ha, erases_correct_appCong henv hE hsub hsat hsh hXFe hnb ha hXFs
        (iha _ .refl).2⟩
    · obtain ⟨hl, -⟩ := ihf _ hFl
      have hll := fixed_atom (show SrcAtom (.lam n' A' b' bi') from trivial) _ hl
      subst hll
      exact absurd trivial hnb
  | mdata hev ih =>
    intro X hX
    obtain rfl := hX.eq_of_head fun _ _ h => by cases h
    exact ⟨.mdata hev, erases_correct_mdata henv hE hsub hev (ih _ .refl).2⟩
  | atom ha =>
    intro X hX
    rename_i e
    obtain rfl := hX.eq_of_head fun _ _ h => by subst h; simp [SrcAtom] at ha
    exact ⟨.atom ha, erases_correct_atom ha⟩

end SimMain

/-- The relation-level simulation: an erasure, with erased dependencies, of a typed source term
that evaluates, evaluates in λ□ to an erasure of the source value. Reference: `erases_correct`
(`MR E/ErasureCorrectness.v:51`); MC §7.3, Thm 7.3. -/
theorem erases_correct : erases_correct_statement := by
  intro ζ E B P σ lps lenv e tb v henv hE hsub hinj hbinj harity _ t he hty her hdeps hev
  exact (SimMain.sim henv hE hsub hinj hbinj harity hev e .refl).2 he hty her hdeps

end EraseProof
