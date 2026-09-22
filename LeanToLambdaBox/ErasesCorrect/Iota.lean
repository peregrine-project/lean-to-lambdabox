import LeanToLambdaBox.ErasesCorrect.Steps
import LeanToLambdaBox.IotaBridge

/-!
# The ι arm of the simulation

`step_iota` is the arm of `erases_correct` at `SEval.iota`: a `casesOn` spine
`mkApps (.const con us) (pre ++ disc :: minors ++ extra)` whose discriminant reaches a
constructor value. It takes no premise beyond `StepIota`'s own `UpstreamAsks env`. Six
steps, in the order the module lands them:

* `erases_mkApps_inv` splits the erasure into a head reading with pointwise arguments or a
  boxed proper prefix; the boxed prefix boxes the whole redex and folds by
  `WcbvEval.mkApps_box`, whose discarded arguments evaluate because the induction
  hypotheses at the prefix, the minors and the extra arguments do;
* the head is `Erases.const`'s — the constructor reading is refuted by the rule's own
  `ConstOrigin` — and `Lower.source_constApp` reads the pass back at that head: the
  congruence, refuted by the `ElimDecl` `ErasesEnv.elims` gives at the reached key against
  the rule's own `hsh`/`hinf`, or `Lower.elimApp`'s `.case` node, whose data `ElimDecl.uniq`
  equates with that one's;
* the discriminant's induction hypothesis gives the target constructor value, its boxed
  readings refuted by `not_erasable_of_informative` against `elim_major`'s typing;
* the node's arity data comes from `ElimDecl`'s block through `LowerEnv.inds`, and the
  rule's own `hnp` names the same block by `IndArity.inj`; the `propositional = false`
  `WcbvEval.iota` reads is `ElimDecl`'s `IndNotPropositional`, which the clause's producers
  discharge from their own `InformativeInd`;
* the branch's induction hypothesis is taken at the *un-contracted* application of the
  selected minor, and `IotaBridge`'s β-chain rewrite under `wcbvEval_mkApps_head_congr`
  turns it into `WcbvEval.iota`, over-application included.

Over-application rides outside the emitted node and costs no premise: the arguments past
the node's arity are the `extra` of both the source rule and `Lower.elimApp`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Pointwise lists over an append, a cons and a drop

The ι rule and `Lower.elimApp` cut the same spine into the same four pieces; these lemmas
move a pointwise relation across that cut.
-/

/-- Splitting a pointwise relation at an append in the left list. -/
theorem forall₂_append_inv {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m : List β}, List.Forall₂ R (l₁ ++ l₂) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons hab hrest =>
          obtain ⟨m₁, m₂, rfl, h1, h2⟩ := forall₂_append_inv hrest
          exact ⟨_ :: m₁, m₂, rfl, .cons hab h1, h2⟩

/-- A pointwise relation is closed under `List.append`. -/
theorem forall₂_append {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {m₁ : List β}, List.Forall₂ R l₁ m₁ →
      ∀ {l₂ : List α} {m₂ : List β}, List.Forall₂ R l₂ m₂ →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, .nil, _, _, h => h
  | _, _, .cons hab hrest, _, _, h => .cons hab (forall₂_append hrest h)

/-- A pointwise relation is closed under `List.drop`. -/
theorem forall₂_drop {α β : Type _} {R : α → β → Prop} :
    ∀ (n : Nat) {l : List α} {m : List β}, List.Forall₂ R l m →
      List.Forall₂ R (l.drop n) (m.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ hrest => by simpa using forall₂_drop n hrest

/-- A spine splits at an append of its arguments. -/
theorem LBTerm.mkApps_append : ∀ (l : List LBTerm) (f : LBTerm) (k : List LBTerm),
    LBTerm.mkApps f (l ++ k) = LBTerm.mkApps (LBTerm.mkApps f l) k
  | [], _, _ => rfl
  | a :: l, f, k => by
      rw [List.cons_append, LBTerm.mkApps, LBTerm.mkApps, LBTerm.mkApps_append l (.app f a) k]

/-- **The two spine cuts agree.** One pointwise-related pair of spines, cut on the left at
the source's segmentation and on the right at the emitted node's, splits into four
pointwise-related pairs as soon as the two cuts have the same lengths. -/
theorem forall₂_split3 {α β : Type _} {R : α → β → Prop} {l₁ l₂ l₃ : List α} {x : α}
    {m₁ m₂ m₃ : List β} {y : β}
    (h : List.Forall₂ R (l₁ ++ x :: l₂ ++ l₃) (m₁ ++ y :: m₂ ++ m₃))
    (h1 : m₁.length = l₁.length) (h2 : m₂.length = l₂.length) :
    List.Forall₂ R l₁ m₁ ∧ R x y ∧ List.Forall₂ R l₂ m₂ ∧ List.Forall₂ R l₃ m₃ := by
  obtain ⟨n₁, n₃, heq, hf₁₂, hf₃⟩ := forall₂_append_inv (l₁ := l₁ ++ x :: l₂) (l₂ := l₃) h
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm (by
    have := hf₁₂.length_eq
    simp only [List.length_append, List.length_cons] at this ⊢
    omega)
  obtain ⟨n₁, n₂, heq₂, hf₁, hcons⟩ := forall₂_append_inv (l₁ := l₁) (l₂ := x :: l₂) hf₁₂
  obtain ⟨rfl, rfl⟩ := List.append_inj heq₂.symm (by
    have := hf₁.length_eq
    omega)
  cases hcons with
  | cons hxy hf₂ => exact ⟨hf₁, hxy, hf₂, hf₃⟩

/-- A pointwise `Lower` pair survives `List.drop`. -/
theorem lower_drop {Γ : GlobalDeclarations} {l l' : List LBTerm} (m : Nat)
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!) :
    (l'.drop m).length = (l.drop m).length ∧
      ∀ i, i < (l.drop m).length → Lower Γ (l.drop m)[i]! (l'.drop m)[i]! := by
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_drop] at hi
  rw [getElem!_drop l m i (by simp only [List.length_drop]; omega),
    getElem!_drop l' m i (by simp only [List.length_drop, hlen]; omega)]
  exact h _ (by omega)

/-- A pointwise `Lower` pair survives `List.append`. -/
theorem lower_append {Γ : GlobalDeclarations} {l l' k k' : List LBTerm}
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!)
    (hlen₂ : k'.length = k.length) (h₂ : ∀ i, i < k.length → Lower Γ k[i]! k'[i]!) :
    (l' ++ k').length = (l ++ k).length ∧
      ∀ i, i < (l ++ k).length → Lower Γ (l ++ k)[i]! (l' ++ k')[i]! := by
  refine ⟨by simp [hlen, hlen₂], fun i hi => ?_⟩
  simp only [List.length_append] at hi
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · rw [getElem!_pos (l ++ k) i (by simp; omega), getElem!_pos (l' ++ k') i (by simp; omega),
      List.getElem_append_left hlt, List.getElem_append_left (by omega),
      ← getElem!_pos l i hlt, ← getElem!_pos l' i (by omega)]
    exact h i hlt
  · rw [getElem!_pos (l ++ k) i (by simp; omega), getElem!_pos (l' ++ k') i (by simp; omega),
      List.getElem_append_right hge, List.getElem_append_right (by omega),
      ← getElem!_pos k (i - l.length) (by omega),
      ← getElem!_pos k' (i - l'.length) (by omega), hlen]
    exact h₂ _ (by omega)

/-! ## An erasure is closed

The ι bridge substitutes the constructor's fields simultaneously and in reverse, which
agrees with the β-chain only at closed field values (`IotaBridge.lean`). The fields are
the arguments of a target value, so the closedness they need comes from the program's own:
an erasure at the empty context has no loose index.
-/

/-- A bound variable the local context answers is one the context binds. -/
theorem vlctx_find_inl_lt_bvars :
    ∀ {Δ : VLCtx} {i : Nat} {p : VExpr × VExpr}, Δ.find? (.inl i) = some p → i < Δ.bvars
  | [], _, _, h => by simp [VLCtx.find?] at h
  | (ofv, _) :: Δ, i, _, h => by
      cases ofv with
      | none =>
          cases i with
          | zero => simp [VLCtx.bvars]
          | succ n =>
              simp only [VLCtx.find?, VLCtx.next] at h
              cases hfd : VLCtx.find? Δ (Sum.inl n) with
              | none => rw [hfd] at h; simp at h
              | some q =>
                  have := vlctx_find_inl_lt_bvars hfd
                  simp only [VLCtx.bvars]; omega
      | some x =>
          simp only [VLCtx.find?, VLCtx.next] at h
          cases hfd : VLCtx.find? Δ (Sum.inl i) with
          | none => rw [hfd] at h; simp at h
          | some q => simpa [VLCtx.bvars] using vlctx_find_inl_lt_bvars hfd

/-- **Erasure produces no loose index.** The `bvar` rule copies an index the context
answers, and the two binder rules recurse under an extended context. -/
theorem Erases.lbClosed {env : VEnv} {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {t : LBTerm}, Erases env Us Δ e t → LBClosed t Δ.bvars := by
  intro Δ e t h
  induction h with
  | box => trivial
  | bvar hf => exact vlctx_find_inl_lt_bvars hf
  | fvar => trivial
  | ctor => trivial
  | const => trivial
  | app _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ ih => exact ih
  | letE _ _ _ _ ihv ihb => exact ⟨ihv, ihb⟩
  | proj _ _ _ _ ih => exact ih
  | lit _ _ ih => exact ih
  | mdata _ ih => exact ih

/-! ## A peeled alternative, read back -/

/-- The minor a `LowerAlt` peels is the alternative's λ-telescope, and the binder list has
exactly the field arity `iota_red` reads. -/
theorem LowerAlt.lower {Γ : GlobalDeclarations} :
    ∀ (nf : Nat) {m : LBTerm} {alt : List BinderName × LBTerm}, LowerAlt Γ nf m alt →
      alt.1.length = nf ∧ Lower Γ m (mkLambdas alt.1 alt.2)
  | 0, _, _, h => by cases h with | done hl => exact ⟨rfl, hl⟩
  | nf + 1, _, _, h => by
      cases h with
      | lam h' =>
          obtain ⟨hlen, hlow⟩ := LowerAlt.lower nf h'
          exact ⟨by simpa using hlen, .lambda hlow⟩

/-! ## A lowered spine at a constant head -/

/-- The two readings of a lowered spine at a constant head: the congruence, at a head the
pass has no key for, or the eliminator application `Lower.elimApp` emits as a `.case`
node — with the arguments past the node's arity riding outside it. -/
def LowerConstApp (Γ : GlobalDeclarations) (kn : Kername) (ts : List LBTerm)
    (t : LBTerm) : Prop :=
  (¬ RuntimeKey Γ kn ∧ ∃ hd' ts', t = LBTerm.mkApps hd' ts' ∧ Lower Γ (.const kn) hd' ∧
      ts'.length = ts.length ∧ ∀ i, i < ts.length → Lower Γ ts[i]! ts'[i]!) ∨
  (∃ (iid : InductiveId) (np dp : Nat) (nfs : List Nat) (pre : List LBTerm)
      (disc disc' : LBTerm) (minors : List LBTerm)
      (alts : List (List BinderName × LBTerm)) (extra extra' : List LBTerm),
    ElimDecl Γ kn iid np dp nfs ∧ ts = pre ++ disc :: minors ++ extra ∧
    pre.length = dp ∧ minors.length = nfs.length ∧ alts.length = nfs.length ∧
    (∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!) ∧
    Lower Γ disc disc' ∧ extra'.length = extra.length ∧
    (∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) ∧
    t = LBTerm.mkApps (.case (iid, np) disc' alts) extra')

/-- **Inverting the pass at a constant-headed spine.** The block targets are excluded by
`Lower.ne_block_image`, which reads the block's own `hfl` — an application is neither a
constant nor a λ — so an argument at a time the derivation is either the `app` congruence
or `elimApp`, and an `elimApp` at a shorter spine absorbs the remaining arguments into its
`extra`. -/
theorem Lower.source_constApp {Γ : GlobalDeclarations} {kn : Kername} :
    ∀ (n : Nat) (ts : List LBTerm), ts.length = n → ∀ {s t : LBTerm}, Lower Γ s t →
      s = LBTerm.mkApps (.const kn) ts → LowerConstApp Γ kn ts t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ts hn s t h hs
    rcases List.eq_nil_or_concat ts with rfl | ⟨init, last, rfl⟩
    · subst hs
      obtain ⟨hnk, -⟩ := Lower.source_const h rfl
      exact .inl ⟨hnk, t, [], rfl, h, rfl, by simp⟩
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hs
      have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
        (by rw [hs]; rfl)
      cases h with
      | box | bvar | fvar | prim | const | lambda | letIn | proj | construct | «case» =>
          exact LBTerm.noConfusion hs
      | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
      | fixEta => exact absurd hni.2 (by simp [isLambda])
      | @app f₀ f' a₀ a' hf ha =>
          injection hs with hff haa
          subst hff; subst haa
          rcases ih init.length (by simp [List.concat_eq_append] at hn; omega) init rfl hf rfl with
            ⟨hnk, hd', is', rfl, hconst, hilen, hi⟩ |
            ⟨iid, np, dp, nfs, pre, disc, disc', minors, alts, extra₀, extra₀',
              helim, hinit, hpl, hml, hal, hmin, hdisc, hxlen, hx, rfl⟩
          · obtain ⟨hlen', hpt'⟩ := Lower.concat hilen hi ha
            refine .inl ⟨hnk, hd', is' ++ [a'], (LBTerm.mkApps_concat _ _ _).symm, hconst, ?_, ?_⟩
            · rw [List.concat_eq_append]; exact hlen'
            · rw [List.concat_eq_append]; exact hpt'
          · obtain ⟨hlen', hpt'⟩ := Lower.concat hxlen hx ha
            refine .inr ⟨iid, np, dp, nfs, pre, disc, disc', minors, alts, extra₀ ++ [a₀],
              extra₀' ++ [a'], helim, ?_, hpl, hml, hal, hmin, hdisc, hlen', hpt', ?_⟩
            · rw [List.concat_eq_append, hinit]; simp
            · exact (LBTerm.mkApps_concat _ _ _).symm
      | @elimApp kn' iid np dp nfs pre disc disc' minors alts extra extra'
          hh hlen hmlen halen hmin hdisc hxlen hx =>
          have heq : LBTerm.mkApps (.const kn') (pre ++ disc :: minors ++ extra)
              = LBTerm.mkApps (.const kn) (init ++ [last]) := by
            rw [LBTerm.mkApps_concat]; exact hs
          obtain ⟨hhd, hargs⟩ :=
            mkApps_head_inj (fun _ _ => LBTerm.noConfusion) (fun _ _ => LBTerm.noConfusion) heq
          injection hhd with hknq
          subst hknq
          refine .inr ⟨iid, np, dp, nfs, pre, disc, disc', minors, alts, extra, extra',
            hh, ?_, hlen, hmlen, halen, hmin, hdisc, hxlen, hx, rfl⟩
          rw [List.concat_eq_append, ← hargs]

/-! ## The ι arm -/

/-- **The ι arm.** The subject is the `casesOn` spine, the induction hypotheses come with
the rule's own subderivations, and the target is the emitted `.case` node with the
over-application riding outside it. -/
theorem step_iota {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    StepIota env bo lp Us fl Γspec Γ := by
  intro A con I ctor us cus pre prev minors minorsv extra extrav cargs disc r np cidx nfsR
    henv henvL hfl hsh ho hct hnp hinf hpre hpres hdiscr ihdiscr hmin hmins hxlen hxs hidx
    hdef hcont ihcont ve t₀ t hwt her hlow hspec
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓv := hΔ.toCtx
  have hΓcl : ClosedBodies Γspec := henvL.specClosed
  have hev : SEval env bo Us fl [] (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r :=
    .iota hfl hsh ho hct hnp hinf hpre (fun i hi => (hpres i hi).1) hdiscr hmin
      (fun i hi => (hmins i hi).1) hxlen (fun i hi => (hxs i hi).1) hidx hdef hcont
  have ihmem : ∀ a ∈ pre ++ disc :: minors ++ extra,
      ∃ av, Simulates env bo lp Us Γspec Γ a av := by
    intro a ha
    rcases List.mem_append.1 ha with h1 | h2
    · rcases List.mem_append.1 h1 with h3 | h4
      · obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! h3
        exact ⟨_, (hpres i hi).2⟩
      · rcases List.mem_cons.1 h4 with rfl | h5
        · exact ⟨_, ihdiscr⟩
        · obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! h5
          exact ⟨_, (hmins i hi).2⟩
    · obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! h2
      exact ⟨_, (hxs i hi).2⟩
  have hargEv : ∀ a ∈ pre ++ disc :: minors ++ extra, ∀ (s u : LBTerm),
      Erases env Us [] a s → ErasesEnv env bo lp Γspec s → Lower Γspec s u →
      ∃ x, WcbvEval Γ eraseFlags u x := by
    intro a ha s u hes hss hsu
    obtain ⟨w, htrw⟩ := trExprS_spine_mem _ hwt a ha
    obtain ⟨av, iha⟩ := ihmem a ha
    obtain ⟨x, y, -, -, hx, -⟩ := iha htrw hes hsu hss
    exact ⟨y, hx⟩
  rcases erases_mkApps_inv (pre ++ disc :: minors ++ extra) her with
    ⟨th, ts, hth, hts, rfl⟩ | ⟨bpre, bsuf, bts, heqargs, hbw, hbts, rfl⟩
  case inr =>
    rw [heqargs] at hwt hev
    refine erases_correct_boxSpineLow henv hwt hbw hlow hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hbts s hs
    exact hargEv a (by rw [heqargs]; exact List.mem_append_right _ ha) s u hea
      (hspec.subterm (subTerm_mkApps_arg bts .box s hs)) hsu
  rcases Erases.const_inv hth with ⟨hb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
    ⟨-, -, rfl⟩
  · refine erases_correct_boxSpineLow (pre := []) (suf := pre ++ disc :: minors ++ extra)
      henv hwt hb hlow hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a ha s u hea (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
  · exact absurd hc' (constOrigin_not_ctorOf A ho _ _)
  obtain ⟨eiid, enp, enfs, helimS, hi, hnme⟩ := hspec.elims hsh hinf ho
    (reachableFrom_of_mem_constRefs (by rw [constRefs_mkApps]; simp [constRefs]))
  have hdec : IndDeclOf env I := IndInfo.indDeclOf A hi
  rcases Lower.source_constApp ts.length ts rfl hlow rfl with
    ⟨hnk, -, -, -, -, -, -⟩ |
    ⟨iid, nps, dp, nfs, tpre, tdisc, disc', tminors, alts, textra, textra',
      helim, htseq, hpl, hml, hal, hminAlt, hdiscL, hxl, hxL, rfl⟩
  · exact absurd ⟨eiid, enp, pre.length, enfs, helimS⟩ hnk
  subst htseq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ElimDecl.uniq helim helimS
  obtain ⟨-, herdisc, hfmin, hfextra⟩ :=
    forall₂_split3 hts hpl (by rw [hml, hnme])
  obtain ⟨w, htrdisc⟩ := trExprS_spine_mem _ hwt disc (by simp)
  obtain ⟨ius, iargs, hwty⟩ := elim_major henv hsh rfl rfl hwt htrdisc
  have hspecdisc : ErasesEnv env bo lp Γspec tdisc :=
    hspec.subterm (subTerm_mkApps_arg _ _ _ (by simp))
  obtain ⟨dv₀, dv', herdv, hlowdv, hEdisc, hspecdv⟩ := ihdiscr htrdisc herdisc hdiscL hspecdisc
  obtain ⟨vv, htrvv, hdefvv⟩ := SEval.defeq henv hΔ htrdisc hdiscr
  have hvvty : env.HasType Us.length (VLCtx.toCtx []) vv (VExpr.mkApps (.const I ius) iargs) :=
    VEnv.HasType.defeqU_l henv hΓv hdefvv hwty
  have hnotEr : ¬ Erasable env Us.length (VLCtx.toCtx []) vv :=
    not_erasable_of_informative henv A hΓv hdec hinf hvvty
  rcases erases_mkApps_inv cargs herdv with
    ⟨cth, cargs₀, hcth, hcts, rfl⟩ | ⟨cpre, csuf, cts, hceq, hcbw, hcts, rfl⟩
  case inr =>
    exfalso
    obtain ⟨we, htrwe, herwe⟩ := hcbw
    rw [hceq, mkApps_append] at htrvv
    exact hnotEr (erasable_mkApps henv hΔ csuf htrvv htrwe herwe)
  rcases Erases.const_inv hcth with ⟨hcb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
    ⟨-, ho', -⟩
  · exfalso
    obtain ⟨we, htrwe, herwe⟩ := hcb
    exact hnotEr (erasable_mkApps henv hΔ cargs htrvv htrwe herwe)
  case inr.inr => exact absurd hct (constOrigin_not_ctorOf A ho' I cidx)
  obtain ⟨rfl, rfl⟩ := CtorOf.inj A hct hc'
  obtain ⟨rfl, rfl, rfl⟩ := IndInfo.inj A hi hi'
  obtain ⟨hd₂, cargs', rfl, hhd₂, hclen, hcpt⟩ :=
    Lower.source_mkApps (fun _ _ => LBTerm.noConfusion) (fun _ => LBTerm.noConfusion)
      cargs₀ hlowdv
  obtain rfl : hd₂ = .construct iid cidx [] := by
    rcases Lower.source_construct_nil hhd₂ rfl with h | ⟨defs, j, h⟩
    · exact h
    · exact absurd h (Lower.ne_fix_of_block hhd₂ (fun _ => LBTerm.noConfusion) rfl defs j)
  have hsat : cargs.length = nps + nfs[cidx]! := ctor_saturated henv A hct hi htrvv hvvty
  obtain ⟨rfl, -⟩ := IndArity.inj A hnp hi.arity
  have hcidxlt : cidx < nfs.length := by omega
  obtain ⟨-, mib, hmib, -, oib, hoib, hprop⟩ := helim
  have hmibΓ := henvL.inds _ _ hmib
  have hpropΓ : isPropositionalInductive Γ iid = false := by
    simp only [isPropositionalInductive, hmibΓ, hoib, hprop]
  have hcargsLen : cargs₀.length = cargs.length := hcts.length_eq.symm
  obtain ⟨hnames, hlowmin⟩ := LowerAlt.lower nfs[cidx]! (hminAlt cidx hcidxlt)
  have haltsel : alts[cidx]? = some ((alts[cidx]!).1, (alts[cidx]!).2) := by
    rw [getElem!_pos alts cidx (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  have hfieldsLen : (alts[cidx]!).1.length = (cargs'.drop np).length := by
    simp only [List.length_drop, hclen, hcargsLen, hsat, hnames]
    omega
  obtain ⟨_, _, -, htrcont, -⟩ := hdef
  have hercont : Erases env Us [] (mkApps minors[cidx]! (cargs.drop np ++ extra))
      (LBTerm.mkApps tminors[cidx]! (cargs₀.drop np ++ textra)) :=
    Erases.mkApps_forall₂ (forall₂_append (forall₂_drop np hcts) hfextra)
      (forall₂_getElem! hfmin cidx (by omega))
  have hlowcont : Lower Γspec (LBTerm.mkApps tminors[cidx]! (cargs₀.drop np ++ textra))
      (LBTerm.mkApps (mkLambdas (alts[cidx]!).1 (alts[cidx]!).2)
        (cargs'.drop np ++ textra')) := by
    obtain ⟨hdl, hdp⟩ := lower_drop np hclen hcpt
    obtain ⟨hal', hap⟩ := lower_append hdl hdp hxl hxL
    exact Lower.mkApps hlowmin hal' hap
  have hspeccont : ErasesEnv env bo lp Γspec
      (LBTerm.mkApps tminors[cidx]! (cargs₀.drop np ++ textra)) := by
    refine ErasesEnv.mkApps (hspec.subterm (subTerm_mkApps_arg _ _ _ ?_)) (fun x hx => ?_)
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (Lower.getElem!_mem (by omega))))
    · rcases List.mem_append.1 hx with h1 | h2
      · exact hspecdv.subterm (subTerm_mkApps_arg _ _ _ (List.mem_of_mem_drop h1))
      · exact hspec.subterm (subTerm_mkApps_arg _ _ _ (List.mem_append_right _ h2))
  obtain ⟨r₀, r', herr, hlowr, hEr, hspecr⟩ := ihcont htrcont hercont hlowcont hspeccont
  refine ⟨r₀, r', herr, hlowr, ?_, hspecr⟩
  rw [LBTerm.mkApps_append] at hEr
  refine wcbvEval_mkApps_head_congr textra' (fun {v} hv => ?_) hEr
  have hval : Value Γ eraseFlags (LBTerm.mkApps (.construct iid cidx []) cargs') :=
    eval_to_value hEdisc
  have hvalArgs : ∀ x ∈ cargs', WcbvEval Γ eraseFlags x x := fun x hx =>
    value_final (value_mkApps_construct_args cargs'.length rfl hval x hx)
  have hclosedDisc : LBClosed disc' 0 := Lower.closed hΓcl hdiscL 0 (Erases.lbClosed herdisc)
  have hclosedArgs : ∀ x ∈ cargs', LBClosed x 0 :=
    LBClosed.mkApps_inv (WcbvEval.lbClosed henvL.closed hEdisc hclosedDisc)
  refine WcbvEval.iota rfl hpropΓ hEdisc haltsel hfieldsLen.symm ?_
  exact wcbvEval_mkApps_mkLambdas_substList (cargs'.drop np) (alts[cidx]!).1
    (alts[cidx]!).2 hfieldsLen (fun x hx => hvalArgs x (List.mem_of_mem_drop hx))
    (fun x hx => hclosedArgs x (List.mem_of_mem_drop hx)) hv

/-! ## Non-vacuity

The arm's target side, at `LowerElimFixture`'s block: the branch application the induction
hypothesis returns, turned into the emitted node's own ι step by the same two lemmas the
proof uses — the β-chain rewrite of `IotaBridge` and, for the over-applied spine,
`wcbvEval_mkApps_head_congr`.
-/

namespace LowerElimFixture

/-- The one-field constructor's arity, as the emitted environment reads it. -/
theorem arity_one : constructorArity env iid 1 = some 1 := rfl

/-- The fixture's block is not propositional, which is what `WcbvEval.iota` reads. -/
theorem not_propositional : isPropositionalInductive env iid = false := rfl

/-- The discriminant value: the one-field constructor applied to `□`. -/
theorem discr_value :
    WcbvEval env eraseFlags (LBTerm.mkApps (.construct iid 1 []) [.box])
      (LBTerm.mkApps (.construct iid 1 []) [.box]) := by
  refine wcbvEval_mkApps_construct arity_one [.box] [.box] (by decide) rfl ?_
  intro i hi
  match i, hi with
  | 0, _ => exact .box

/-- **The ι arm's branch step fires.** The selected alternative applied to the
constructor's one field has the same evaluations as the emitted `.case` node: this is
`wcbvEval_mkApps_mkLambdas_substList` feeding `WcbvEval.iota`, the composition step 6
performs. -/
theorem iota_branch_fires {v : LBTerm}
    (hv : WcbvEval env eraseFlags (LBTerm.mkApps (mkLambdas [.anon] (.bvar 0)) [.box]) v) :
    WcbvEval env eraseFlags
      (.case (iid, 0) (LBTerm.mkApps (.construct iid 1 []) [.box])
        [([], .box), ([.anon], .bvar 0)]) v := by
  refine WcbvEval.iota rfl not_propositional discr_value rfl rfl ?_
  exact wcbvEval_mkApps_mkLambdas_substList [.box] [.anon] (.bvar 0) rfl
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact .box)
    (fun x hx => by rw [List.mem_singleton.mp hx]; trivial) hv

/-- **And it fires over-applied.** One argument past the node's arity rides outside it, and
`wcbvEval_mkApps_head_congr` replaces the branch application by the `.case` node with the
extra argument untouched. -/
theorem iota_overapplied_fires :
    WcbvEval env eraseFlags
      (LBTerm.mkApps (.case (iid, 0) (LBTerm.mkApps (.construct iid 1 []) [.box])
        [([], .box), ([.anon], .bvar 0)]) [.box]) .box := by
  refine wcbvEval_mkApps_head_congr [.box] (fun hv => iota_branch_fires hv) ?_
  rw [← LBTerm.mkApps_append]
  exact .app_box (.beta (.lam _ _) .box .box) .box

end LowerElimFixture

end LeanToLambdaBox
