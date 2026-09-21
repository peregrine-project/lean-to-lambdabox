import LeanToLambdaBox.VisitExprRefines.Motives

/-!
# The mechanical steps of the bridge induction

The induction obligations at the seven members that carry no compilation step of their own:
`Erasure.visitExpr`'s dispatch, `Erasure.visitAppArgs`' spine loop, the two binder members
`Erasure.visitLet` and `Erasure.visitLambda`, the head dispatch of `Erasure.visitApp` and
`Erasure.visitConstApp`, and `Erasure.visitAlt`'s telescope.

* `ErasesLBMode` is closed under the congruences the composite inherits from `Erases` and
  `Lower`: box, application, free variable, metadata, and — through `Erases.uninstantiate`,
  `ConstToFVar.abstracts` and `Lower.abstract` at `SpecEnv.fvarFree` — the two binders and one
  alternative.
* The spine kit reads a term's head and arguments back off `Expr.getAppFn`/`Expr.getAppArgs`,
  which is how `Erasure.visitApp` and `Erasure.visitConstApp` decompose their subject;
  `bridge_alt_telescope` is its binder-side twin for `Erasure.lambdaOrIntroToArity`.
* Six of the seven steps carry no premise beyond their own `Stepᵢ`: the binder steps read
  `SpecEnv.fvarFree`, and steps 12 and 18 read `ErasureSpec.lookup_adequate` and
  `ErasureSpec.prim_monotone`. `step_visitConstApp` keeps one hypothesis, `hctab`, which says
  that a constructor the table knows at all it knows as a constructor; its docstring records
  why no standing binder supplies it.
* The last section is not a member's step. It is the λ-headedness `LowerBlock.hfl` asks of
  the block `Erasure.visitMutual` emits, supplied from the emitted program's own
  `LBWfPeregrine.fixLambda` — the run does not carry it.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

/-! ## The congruences of the composite, in either fixvar mode -/

variable {tbl : SourceTable} {ctx : ErasureContext} {env : VEnv} {Us : List Name}
  {Γspec : GlobalDeclarations} {Δ : VLCtx}

/-- An irrelevant term is the composite's `box` in either mode. -/
theorem ErasesLBMode.box {e : Expr} {ve : VExpr} (htr : TrExprS env Us Δ e ve)
    (her : Erasable env Us.length Δ.toCtx ve) : ErasesLBMode tbl ctx env Us Γspec Δ e .box :=
  ⟨fun _ => ErasesLB.box htr her, fun _ _ _ => ErasesLBFix.box htr her⟩

/-- Application is a congruence of the composite in either mode. -/
theorem ErasesLBMode.app {f a : Expr} {f' a' : LBTerm}
    (hf : ErasesLBMode tbl ctx env Us Γspec Δ f f')
    (ha : ErasesLBMode tbl ctx env Us Γspec Δ a a') :
    ErasesLBMode tbl ctx env Us Γspec Δ (.app f a) (.app f' a') :=
  ⟨fun h => (hf.1 h).app (ha.1 h), fun nms ids h => (hf.2 nms ids h).app (ha.2 nms ids h)⟩

/-- A free variable keeps its identifier: `Erases.fvar` composed with `Lower.fvar`, which the
block rewriting fixes. -/
theorem ErasesLBMode.fvar {x : FVarId} {e' A : VExpr}
    (h : Δ.find? (.inr x) = some (e', A)) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.fvar x) (.fvar x) :=
  ⟨fun _ => ⟨.fvar x, .fvar h, .fvar x⟩,
    fun _ _ _ => .of_erasesLB ⟨.fvar x, .fvar h, .fvar x⟩ (.fvar x)⟩

/-- Metadata is transparent to both factors. -/
theorem ErasesLBMode.mdata {d : MData} {e : Expr} {t : LBTerm}
    (h : ErasesLBMode tbl ctx env Us Γspec Δ e t) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.mdata d e) t :=
  ⟨fun hf => let ⟨t₀, h₀, h₁⟩ := h.1 hf; ⟨t₀, .mdata h₀, h₁⟩,
    fun nms ids hf => let ⟨t₀, t₁, h₀, h₁, hc⟩ := h.2 nms ids hf; ⟨t₀, t₁, .mdata h₀, h₁, hc⟩⟩

/-! ## Application spines

`Erasure.visitApp` decomposes its subject with `Expr.withApp`, so the step needs the head
and the arguments of a spine read back off the whole term: the reconstruction identity, the
`SupportedTm` inversion, the `TrExprS` inversion, and the reachability inclusion that carries
the fragment condition's body clause to a spine component.
-/

/-- Spine reconstruction: folding `Expr.app` over `Expr.getAppArgs` from `Expr.getAppFn`
gives the term back. -/
theorem getAppArgs_spine (e : Expr) :
    e.getAppArgs.toList.foldl Expr.app e.getAppFn = e := by
  rw [Lean.Expr.getAppArgs_toList, ← Lean.Expr.mkAppList_eq_foldl,
    Lean.Expr.mkAppList_getAppArgsList]

/-- On a bvar-free context — the shape a real `LocalContext` models — de Bruijn lookups
fail, which is what refutes `Erasure.visitExpr`'s `.bvar` arm from the translation premise. -/
theorem VLCtx.find?_bvar_none_of_noBV :
    ∀ {Δ : VLCtx}, Δ.NoBV → ∀ i, Δ.find? (.inl i) = none
  | [], _, _ => rfl
  | (none, _) :: _, h, _ => by simp [Lean4Lean.VLCtx.NoBV, Lean4Lean.VLCtx.bvars] at h
  | (some _, _) :: Δ, h, i => by
    have hΔ : Lean4Lean.VLCtx.NoBV Δ := h
    simp only [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next,
      VLCtx.find?_bvar_none_of_noBV hΔ i]
    rfl

/-- Every constant named by a spine's head or by one of its arguments is named by the
spine, which is what `Supported.subterm` consumes. -/
theorem constNames_spine_sub : ∀ (args : List Expr) (f : Expr),
    (∀ d ∈ constNames f, d ∈ constNames (args.foldl Expr.app f)) ∧
    (∀ a ∈ args, ∀ d ∈ constNames a, d ∈ constNames (args.foldl Expr.app f))
  | [], f => ⟨fun _ h => h, by simp⟩
  | a :: as, f => by
    obtain ⟨ih1, ih2⟩ := constNames_spine_sub as (f.app a)
    refine ⟨fun d hd => ih1 d (by simp [constNames, hd]), fun b hb d hd => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ih1 d (by simp [constNames, hd])
    · exact ih2 b hb d hd

/-- The shape condition of a spine, inverted: the head carries it at the whole argument
list and every argument carries it on its own. -/
theorem supportedTm_foldl_app_inv {env : VEnv} {tbl : SourceTable} :
    ∀ {args : List Expr} {f : Expr} {sp : List Expr},
      SupportedTm env tbl (args.foldl Expr.app f) sp →
      SupportedTm env tbl f (args ++ sp) ∧ ∀ a ∈ args, SupportedTm env tbl a []
  | [], _, _, h => ⟨by simpa using h, by simp⟩
  | a :: as, f, sp, h => by
    obtain ⟨hfa, hrest⟩ := supportedTm_foldl_app_inv (args := as) (f := f.app a) h
    cases hfa with
    | app ha hf =>
      refine ⟨by simpa using hf, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hrest b hb

/-- Translating an application spine yields a translation of the head and, pointwise, of
every argument: inversion by induction on the spine, peeling one `TrExprS.app` a step. -/
theorem trExprS_appSpine_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (args : List Expr) (f : Expr) (ve : VExpr),
      TrExprS env Us Δ (args.foldl Expr.app f) ve →
      (∃ fve, TrExprS env Us Δ f fve) ∧
      (∀ i (h : i < args.length), ∃ ave, TrExprS env Us Δ args[i] ave)
  | [], _, ve, htr => ⟨⟨ve, htr⟩, fun i h => absurd h (by simp)⟩
  | a :: as, f, ve, htr => by
    simp only [List.foldl_cons] at htr
    obtain ⟨⟨fve, htrapp⟩, hpt⟩ := trExprS_appSpine_inv as (f.app a) ve htr
    cases htrapp with
    | app _ _ htrf htra =>
      refine ⟨⟨_, htrf⟩, fun i h => ?_⟩
      cases i with
      | zero => exact ⟨_, htra⟩
      | succ j => exact hpt j (by simpa using h)

/-- The per-argument premises `Motive7` asks for, read off a supported, translatable spine.
No condition on the head: an argument's own condition is independent of it. -/
theorem spine_args_ok {env : VEnv} {Us : List Name} {tbl : SourceTable} {Δ : VLCtx} {e : Expr}
    (hsupp : Supported env tbl e) (hex : ∃ ve, TrExprS env Us Δ e ve) :
    ArgsOk env Us tbl Δ e.getAppArgs := by
  obtain ⟨ve, hve⟩ := hex
  have hveS : TrExprS env Us Δ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) ve := by
    rw [getAppArgs_spine]; exact hve
  obtain ⟨-, hargtr⟩ := trExprS_appSpine_inv _ _ _ hveS
  have hsuppS : SupportedTm env tbl (e.getAppArgs.toList.foldl Expr.app e.getAppFn) [] := by
    rw [getAppArgs_spine]; exact hsupp.term
  obtain ⟨-, hargs⟩ := supportedTm_foldl_app_inv hsuppS
  obtain ⟨-, hsuba⟩ := constNames_spine_sub e.getAppArgs.toList e.getAppFn
  have hspine : ∀ d, d ∈ constNames (e.getAppArgs.toList.foldl Expr.app e.getAppFn) →
      d ∈ constNames e := by rw [getAppArgs_spine]; exact fun _ h => h
  intro i hi
  have hi' : i < e.getAppArgs.toList.length := by simpa using hi
  have hmem : e.getAppArgs.toList[i] ∈ e.getAppArgs.toList := List.getElem_mem hi'
  refine ⟨hsupp.subterm (fun d hd => hspine d (hsuba _ hmem d hd)) (by simpa using hargs _ hmem),
    ?_⟩
  obtain ⟨ave, hav⟩ := hargtr i hi'
  exact ⟨ave, by simpa using hav⟩

/-- The head and the arguments of a supported, translatable spine, packaged as the two
premises `Motive1` and `Motive7` ask for. `hhd` is the head's own shape condition at the
empty spine, which the whole term's does not imply — see `Supported.head`. -/
theorem spine_facts {env : VEnv} {Us : List Name} {tbl : SourceTable} {Δ : VLCtx} {e : Expr}
    (hsupp : Supported env tbl e) (hex : ∃ ve, TrExprS env Us Δ e ve)
    (hhd : SupportedTm env tbl e.getAppFn []) :
    (Supported env tbl e.getAppFn ∧ ∃ ve, TrExprS env Us Δ e.getAppFn ve) ∧
      ArgsOk env Us tbl Δ e.getAppArgs := by
  obtain ⟨ve, hve⟩ := hex
  have hveS : TrExprS env Us Δ (e.getAppArgs.toList.foldl Expr.app e.getAppFn) ve := by
    rw [getAppArgs_spine]; exact hve
  obtain ⟨⟨fve, htrfn⟩, hargtr⟩ := trExprS_appSpine_inv _ _ _ hveS
  have hsuppS : SupportedTm env tbl (e.getAppArgs.toList.foldl Expr.app e.getAppFn) [] := by
    rw [getAppArgs_spine]; exact hsupp.term
  obtain ⟨-, hargs⟩ := supportedTm_foldl_app_inv hsuppS
  obtain ⟨hsubf, hsuba⟩ := constNames_spine_sub e.getAppArgs.toList e.getAppFn
  have hspine : ∀ d, d ∈ constNames (e.getAppArgs.toList.foldl Expr.app e.getAppFn) →
      d ∈ constNames e := by rw [getAppArgs_spine]; exact fun _ h => h
  refine ⟨⟨hsupp.subterm (fun d hd => hspine d (hsubf d hd)) hhd, fve, htrfn⟩, fun i hi => ?_⟩
  · have hi' : i < e.getAppArgs.toList.length := by simpa using hi
    have hmem : e.getAppArgs.toList[i] ∈ e.getAppArgs.toList := List.getElem_mem hi'
    refine ⟨hsupp.subterm (fun d hd => hspine d (hsuba _ hmem d hd)) (by simpa using hargs _ hmem),
      ?_⟩
    obtain ⟨ave, hav⟩ := hargtr i hi'
    exact ⟨ave, by simpa using hav⟩

/-! ## Abstraction and the two pass factors

`Erasure.mkLambda`/`mkLetIn`/`mkAlt` close the emitted body over the binder's identifier with
`abstract = toBvar _ 0`, while `Erases.uninstantiate` closes the *source* image. The two meet
only if both factors of the composite commute with the closing.
-/

/-- Block rewriting commutes with abstracting a free variable that is none of the block's own
fix variables. At one of those they disagree: the rewriting produces exactly that variable
and the abstraction would bind it. -/
theorem ConstToFVar.abstracts {kns : List Kername} {ids : List FVarId} {x : FVarId}
    (hx : x ∉ ids) {s t : LBTerm} (h : ConstToFVar kns ids s t) :
    ∀ lvl, ConstToFVar kns ids (toBvar x lvl s) (toBvar x lvl t) := by
  induction h with
  | box => exact fun _ => .box
  | bvar i => exact fun _ => .bvar i
  | fvar y =>
    intro lvl
    simp only [toBvar]
    split
    · exact .bvar lvl
    · exact .fvar y
  | prim p => exact fun _ => .prim p
  | @hit j kn y hkn hy =>
    intro lvl
    have hne : ¬ (y == x) = true := by
      simp only [fvarId_beq_iff_eq]
      rintro rfl
      exact hx (List.mem_of_getElem? hy)
    simp only [toBvar, if_neg hne]
    exact .hit hkn hy
  | miss h => exact fun _ => .miss h
  | lambda _ ih => exact fun lvl => .lambda (ih (lvl + 1))
  | letIn _ _ ihv ihb => exact fun lvl => .letIn (ihv lvl) (ihb (lvl + 1))
  | app _ _ ihf iha => exact fun lvl => .app (ihf lvl) (iha lvl)
  | proj _ ih => exact fun lvl => .proj (ih lvl)
  | @construct iid k args args' hlen _ ih =>
    intro lvl
    simp only [toBvar, toBvarArgs_eq_map]
    refine .construct (by simp [hlen]) fun i hi => ?_
    rw [List.length_map] at hi
    rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
    exact ih i hi lvl
  | @«case» ip d d' alts alts' _ hlen hn _ ihd ihb =>
    intro lvl
    simp only [toBvar, toBvarAlts_eq_map]
    refine .case (ihd lvl) (by simp [hlen]) (fun i hi => ?_) fun i hi => ?_ <;>
      rw [List.length_map] at hi <;>
      rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
            (a.1, toBvar x (lvl + a.1.length) a.2)) alts' i (by omega),
        Lower.getElem!_map (fun a : List BinderName × LBTerm =>
            (a.1, toBvar x (lvl + a.1.length) a.2)) alts i hi]
    · exact hn i hi
    · rw [hn i hi]; exact ihb i hi (lvl + (alts[i]!).1.length)
  | fix defs i => exact fun _ => .fix _ _

/-- The composite at a λ binder: the run opens the binder into `x`, erases, and closes with
`toBvar x 0`; `Erases.uninstantiate` closes the erasure image and the two pass factors follow
it. `Lower.lambda` leaves the emitted binder name free, so the run's own name is admissible. -/
theorem ErasesLBMode.lam (hfv : FVarFreeBodies Γspec) {x : FVarId}
    (hxids : ∀ nms ids, BlockKeyed tbl ctx nms ids → x ∉ ids)
    {n : Name} {ty b : Expr} {bi : BinderInfo} {ty' body' : VExpr} {deps : List FVarId}
    {t : LBTerm} {N : BinderName} (hΔbv : Δ.NoBV)
    (hty : TrExprS env Us Δ ty ty')
    (hbody : TrExprS env Us ((none, .vlam ty') :: Δ) b body') (hx : x ∉ Δ.fvars)
    (h : ErasesLBMode tbl ctx env Us Γspec ((some (x, deps), .vlam ty') :: Δ)
      (b.instantiate1' (.fvar x)) t) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.lam n ty b bi) (.lambda N (toBvar x 0 t)) := by
  have sc : FVarsIn (· ≠ x) b := by
    have hin : FVarsIn (· ∈ Δ.fvars) b := by
      have := hbody.fvarsIn; simpa [Lean4Lean.VLCtx.fvars] using this
    exact hin.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have hc : b.Closed 1 := by
    have := hbody.closed; simpa [Lean4Lean.VLCtx.bvars, hΔbv] using this
  refine ⟨fun hfx => ?_, fun nms ids hfx => ?_⟩
  · obtain ⟨t₀, her, hl⟩ := h.1 hfx
    exact ⟨_, .lam hty (her.uninstantiate sc hc), .lambda (Lower.abstract hfv hl x 0)⟩
  · obtain ⟨t₀, t₁, her, hl, hcf⟩ := h.2 nms ids hfx
    exact ⟨.lambda (.named n.toString) (toBvar x 0 t₀), .lambda N (toBvar x 0 t₁),
      .lam hty (her.uninstantiate sc hc), .lambda (Lower.abstract hfv hl x 0),
      .lambda (hcf.abstracts (hxids nms ids hfx) 0)⟩

/-- The composite at a `let` binder. The value is erased *inside* the extended context, so
`Erases.strengthen_vlet` brings it back out. -/
theorem ErasesLBMode.letE (hfv : FVarFreeBodies Γspec) {x : FVarId}
    (hxids : ∀ nms ids, BlockKeyed tbl ctx nms ids → x ∉ ids)
    {n : Name} {ty v b : Expr} {nd : Bool} {ty' val' body' : VExpr} {deps : List FVarId}
    {tv t : LBTerm} {N : BinderName} (hΔbv : Δ.NoBV)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hbody : TrExprS env Us ((none, .vlet ty' val') :: Δ) b body') (hx : x ∉ Δ.fvars)
    (hv : ErasesLBMode tbl ctx env Us Γspec ((some (x, deps), .vlet ty' val') :: Δ) v tv)
    (h : ErasesLBMode tbl ctx env Us Γspec ((some (x, deps), .vlet ty' val') :: Δ)
      (b.instantiate1' (.fvar x)) t) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.letE n ty v b nd) (.letIn N tv (toBvar x 0 t)) := by
  have scv : FVarsIn (· ≠ x) v := hval.fvarsIn.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have scb : FVarsIn (· ≠ x) b := by
    have hin : FVarsIn (· ∈ Δ.fvars) b := by
      have := hbody.fvarsIn; simpa [Lean4Lean.VLCtx.fvars] using this
    exact hin.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have hc : b.Closed 1 := by
    have := hbody.closed; simpa [Lean4Lean.VLCtx.bvars, hΔbv] using this
  refine ⟨fun hfx => ?_, fun nms ids hfx => ?_⟩
  · obtain ⟨v₀, herv, hlv⟩ := hv.1 hfx
    obtain ⟨t₀, her, hl⟩ := h.1 hfx
    exact ⟨_, .letE hty hval (herv.strengthen_vlet scv) (her.uninstantiate scb hc),
      .letIn hlv (Lower.abstract hfv hl x 0)⟩
  · obtain ⟨v₀, v₁, herv, hlv, hcv⟩ := hv.2 nms ids hfx
    obtain ⟨t₀, t₁, her, hl, hcf⟩ := h.2 nms ids hfx
    exact ⟨.letIn (.named n.toString) v₀ (toBvar x 0 t₀), .letIn N v₁ (toBvar x 0 t₁),
      .letE hty hval (herv.strengthen_vlet scv) (her.uninstantiate scb hc),
      .letIn hlv (Lower.abstract hfv hl x 0),
      .letIn hcv (hcf.abstracts (hxids nms ids hfx) 0)⟩

/-! ## Step 7 — `Erasure.visitAppArgs` -/

section Steps

variable {lenv : Environment} {cfg : ErasureConfig}
  {gw : Void IO.RealWorld → NameGenerator}

/-- **Step 7.** The spine loop: the accumulator is the composite's image of the prefix
already consumed, and each iteration extends it by one `app` congruence. A specification
environment of a later state is read at the earlier one by `SpecEnv.mono`. -/
theorem step_visitAppArgs : Step7 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vExpr ih1
  refine ⟨?_, bodyLe7 ih1.2⟩
  replace ih1 := ih1.1
  intro hd args s ctx cctx ref w t s' w' hrun Δ e hinv hhd hargs
  simp only [visitAppArgsBody] at hrun
  have hmem : ∀ a ∈ args.toList, Supported env tbl a ∧ ∃ ve, TrExprS env Us Δ a ve := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hi' : i < args.size := by simpa using hi
    simpa using hargs i hi'
  have hP := run_array_foldlM_ok ctx cctx ref
    (P := fun pre acc s₁ w₁ =>
      RunConcl s s₁ ∧ IndRegistryModelled env s₁ ∧ gw w ≤ gw w₁ ∧
        ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s₁ Γspec →
          ErasesLBMode tbl ctx env Us Γspec Δ (pre.foldl Expr.app e) acc)
    ⟨RunConcl.rfl' _, hinv.indcanon, NameGenerator.LE.rfl, hhd⟩
    (fun pre x post acc s₁ w₁ acc' s₂ w₂ hLpre hPacc hg => by
      rw [run_bind_ok] at hg
      obtain ⟨tx, s₃, w₃, hvx, hp⟩ := hg
      rw [run_pure] at hp
      cases hp
      obtain ⟨hrc, hreg, hle, hacc⟩ := hPacc
      obtain ⟨hsx, hex⟩ := hmem x (by rw [hLpre]; exact List.mem_append_right _ List.mem_cons_self)
      obtain ⟨hrc₂, hreg₂, hle₂, hx⟩ :=
        ih1 _ _ _ _ _ _ _ _ _ hvx Δ ((hinv.mono_state hrc hreg).mono hle) hsx hex
      refine ⟨hrc.trans hrc₂, hreg₂, NameGenerator.LE.trans hle hle₂, fun Γspec hspec => ?_⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (hacc Γspec (SpecEnv.mono hrc₂.le hspec)).app (hx Γspec hspec))
    hrun
  exact hP

/-! ## Step 1 — `Erasure.visitExpr` -/

/-- **Step 1.** The relevance oracle first: a `true` verdict is `ErasesLBMode.box`, at the
ambient scope through the verified checker and at any other scope through the assumed
`Oracle.MetaSound`. Otherwise the shape condition selects the arm, and each arm is one
member's motive. A `false` verdict is also where the type-former exclusion is produced:
`EraserAsks.oracle_informative` reads it off the two oracle clauses at the ambient scope, which
`BridgeInv.lparams` says the reader is at, and the two spine arms hand it to `Motive11`. -/
theorem step_visitExpr (E : EraserAsks lenv env Us gw) : Step1 lenv env Us tbl cfg gw := by
  intro P _htbl _hcfg _hcb vExpr vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
  refine ⟨?_, bodyLe1 ih1.2 ih2.2 ih8.2 ih9.2 ih10.2 ih11.2⟩
  replace ih1 := ih1.1
  replace ih2 := ih2.1
  replace ih8 := ih8.1
  replace ih9 := ih9.1
  replace ih10 := ih10.1
  replace ih11 := ih11.1
  intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex
  simp only [visitExprBody] at hrun
  rw [run_read_bind, run_bind_ok] at hrun
  obtain ⟨c, s₁, w₁, horc, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ horc
  rw [hs₁] at horc hk
  have hle₁ : gw w ≤ gw w₁ := (P.oracle_refl e s ctx cctx ref w c s w₁ horc).1
  by_cases hc : c = true
  · subst hc
    rw [if_pos rfl, run_pure] at hk
    cases hk
    obtain ⟨ve, hve⟩ := hex
    obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
    subst hvlctx
    have her : Erasable env Us.length m.vlctx.toCtx ve := by
      by_cases hlp : ctx.lparams = Us
      · exact P.oracle_sound_of_run horc hlp mwf hlctx hinv.kfresh hve
      · exact P.oracle_meta _ _ _ _ _ _ _ _ horc hlp m ve mwf hlctx hinv.kfresh hve
    exact ⟨RunConcl.rfl' _, hinv.indcanon, hle₁, fun _ _ => ErasesLBMode.box hve her⟩
  · rw [if_neg hc] at hk
    have hinv' := hinv.mono hle₁
    -- the head is not a type former: the oracle said `false` at the ambient level scope
    have hnind : ∀ (c' : Name) (us' : List Level), e.getAppFn = .const c' us' →
        ∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env c' iid np nfs := by
      obtain ⟨ve, hve⟩ := hex
      obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
      refine E.oracle_informative mwf hlctx (hvlctx ▸ hinv.kfresh)
        (show Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
            = .ok (false, s) w₁ from (Bool.not_eq_true c ▸ hc : c = false) ▸ horc)
        hinv.lparams (hvlctx ▸ hve)
    have hnext : ∀ {t₀ : LBTerm} {s₂ : ErasureState} {w₂ : Void IO.RealWorld},
        RunConcl s s₂ ∧ IndRegistryModelled env s₂ ∧ gw w₁ ≤ gw w₂ ∧
          (∀ Γspec, SpecEnv env tbl.body? tbl.levels? s₂ Γspec →
            ErasesLBMode tbl ctx env Us Γspec Δ e t₀) →
        RunRefines env Us tbl ctx Δ s s₂ (gw w) (gw w₂) e t₀ :=
      fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, NameGenerator.LE.trans hle₁ h3, h4⟩
    obtain ⟨hterm, hbodies, hkn⟩ := hsupp
    cases hterm with
    | @bvar i _ =>
      obtain ⟨ve, hve⟩ := hex
      cases hve with
      | bvar hfind => rw [VLCtx.find?_bvar_none_of_noBV hinv.noBV] at hfind; cases hfind
    | @fvar x _ =>
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      obtain ⟨ve, hve⟩ := hex
      cases hve with
      | fvar hfind =>
          exact ⟨RunConcl.rfl' _, hinv.indcanon, hle₁, fun _ _ => ErasesLBMode.fvar hfind⟩
    | @sort u _ =>
      obtain ⟨ve, hve⟩ := hex
      simp only [] at hk
      rw [run_panicWithPosWithDecl] at hk
      cases hk
      exact ⟨RunConcl.rfl' _, hinv.indcanon, hle₁,
        fun _ _ => ErasesLBMode.box hve (Erases.sort_erasable P.envWF hve)⟩
    | @forallE n ty b bi _ =>
      obtain ⟨ve, hve⟩ := hex
      simp only [] at hk
      rw [run_panicWithPosWithDecl] at hk
      cases hk
      exact ⟨RunConcl.rfl' _, hinv.indcanon, hle₁,
        fun _ _ => ErasesLBMode.box hve (Erases.forallE_erasable P.envWF hinv.vlctx_wf hve)⟩
    | @mdata d b hb =>
      simp only [] at hk
      have hsub : ∀ n ∈ constNames b, n ∈ constNames (Expr.mdata d b) := fun _ h => h
      have hexb : ∃ ve, TrExprS env Us Δ b ve := by
        obtain ⟨ve, hve⟩ := hex; cases hve with | mdata h => exact ⟨_, h⟩
      obtain ⟨hrc, hreg, hle₂, hmb⟩ :=
        ih1 _ _ _ _ _ _ _ _ _ hk Δ hinv' (Supported.subterm ⟨hb.mdata, hbodies, hkn⟩ hsub hb) hexb
      exact hnext ⟨hrc, hreg, hle₂, fun Γspec hspec => (hmb Γspec hspec).mdata⟩
    | @lam n ty b bi _ hb =>
      simp only [] at hk
      exact hnext (ih9 _ _ _ _ _ _ _ _ _ hk Δ n ty b bi hinv' rfl ⟨.lam hb, hbodies, hkn⟩ hex)
    | @letE n ty v b nd _ hv hb =>
      simp only [] at hk
      exact hnext (ih8 _ _ _ _ _ _ _ _ _ hk Δ n ty v b nd hinv' rfl ⟨.letE hv hb, hbodies, hkn⟩ hex)
    | @proj S i b _ I np nf hind hinf harity hi hb =>
      simp only [] at hk
      have hsub : ∀ n ∈ constNames b, n ∈ constNames (Expr.proj S i b) := fun _ h => h
      have hexb : ∃ ve, TrExprS env Us Δ b ve := by
        obtain ⟨ve, hve⟩ := hex; cases hve with | proj h _ => exact ⟨_, h⟩
      exact hnext (ih10 _ _ _ _ _ _ _ _ _ _ _ hk Δ I np nf hinv' hind hinf harity hi
        (Supported.subterm ⟨.proj hind hinf harity hi hb, hbodies, hkn⟩ hsub hb) hexb)
    | @app f a _ ha hf =>
      simp only [] at hk
      exact hnext (ih11 _ _ _ _ _ _ _ _ _ hk Δ hinv' ⟨.app ha hf, hbodies, hkn⟩ hex hnind)
    | @natLit n _ hpeano hidx =>
      simp only [] at hk
      exact hnext (ih2 _ _ _ _ _ _ _ _ _ hk Δ n hinv' rfl hpeano hidx
        ⟨.natLit hpeano hidx, hbodies, hkn⟩ hex)
    | @const c us _ hplain hcases hrec hsat hknown =>
      simp only [] at hk
      exact hnext (ih11 _ _ _ _ _ _ _ _ _ hk Δ hinv'
        ⟨.const hplain hcases hrec hsat hknown, hbodies, hkn⟩ hex hnind)
    | @casesApp c us _ minors I hplain hcases hind hinf harity hmin hlen htel =>
      simp only [] at hk
      exact hnext (ih11 _ _ _ _ _ _ _ _ _ hk Δ hinv'
        ⟨.casesApp hplain hcases hind hinf harity hmin hlen htel, hbodies, hkn⟩ hex hnind)

/-! ## Steps 8 and 9 — the two binder members -/

/-- Instantiating a de Bruijn variable with a free variable names no constant the term did
not already name, so the fragment's body clause transports across a binder opening. -/
theorem constNames_instantiate1'_fvar (x : FVarId) :
    ∀ (e : Expr) (k : Nat), constNames (e.instantiate1' (.fvar x) k) = constNames e
  | .bvar i, k => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · rfl
      · rfl
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ | .const _ _, _ => rfl
  | .mdata _ b, k => by
    simp only [Expr.instantiate1', constNames, constNames_instantiate1'_fvar x b k]
  | .proj _ _ b, k => by
    simp only [Expr.instantiate1', constNames, constNames_instantiate1'_fvar x b k]
  | .app f a, k => by
    simp only [Expr.instantiate1', constNames, constNames_instantiate1'_fvar x f k,
      constNames_instantiate1'_fvar x a k]
  | .lam _ _ b _, k => by
    simp only [Expr.instantiate1', constNames, constNames_instantiate1'_fvar x b (k + 1)]
  | .forallE _ _ _ _, _ => rfl
  | .letE _ _ v b _, k => by
    simp only [Expr.instantiate1', constNames, constNames_instantiate1'_fvar x v k,
      constNames_instantiate1'_fvar x b (k + 1)]

/-- The fragment is closed under opening a binder with a free variable. -/
theorem Supported.instantiate1 {env : VEnv} {tbl : SourceTable} {e : Expr} (x : FVarId)
    (h : Supported env tbl e) : Supported env tbl (e.instantiate1 (.fvar x)) :=
  h.subterm
    (by rw [Lean.Expr.instantiate1_eq, constNames_instantiate1'_fvar]; exact fun _ hd => hd)
    (by simpa using h.term.instantiate1 (args := []) x)

/-- **Step 9.** `Erasure.lambdaMonocular` mints a fresh identifier, opens the body under it
and `Erasure.mkLambda` closes the result with `abstract`; the invariant crosses the binder by
`BridgeInv.mkLocalDecl` and the composite by `ErasesLBMode.lam`. -/
theorem step_visitLambda : Step9 lenv env Us tbl cfg gw := by
  intro P _htbl _hcfg _hcb vExpr ih1
  refine ⟨?_, bodyLe9 ih1.2⟩
  replace ih1 := ih1.1
  intro e s ctx cctx ref w t s' w' hrun Δ n ty b bi hinv he hsupp hex
  subst he
  simp only [visitLambdaBody, Erasure.lambdaMonocular, Erasure.withLocalDecl] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
  obtain ⟨hnres, hxres, hle₁, hkres⟩ := P.fresh_names _ _ _ _ _ _ _ _ hfresh
  have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
  rw [hs₁, run_withReader, run_bind_ok] at hk
  obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk
  obtain ⟨hs2, hw2, N, hteq⟩ := run_mkLambda_ok hm
  obtain ⟨hterm, hbodies, hkn⟩ := hsupp
  cases hterm with
  | @lam _ _ _ _ _ hb =>
  obtain ⟨ve, hve⟩ := hex
  cases hve with
  | lam hty' hty hbody =>
  have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
  have hΔ' := TrLCtx.mkLocalDecl (n := n) (bi := bi) hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hty'
  have hinv' := hinv.mkLocalDecl (n := n) (bi := bi) hty hty' hx hnres hle₁ hxres hkres
  rw [Lean.Expr.instantiate1_eq] at hvb
  have hbext := TrExprS.inst_fvar P.envWF.ordered hΔ'.wf hbody
  have hsuppb : Supported env tbl b :=
    Supported.subterm ⟨.lam hb, hbodies, hkn⟩ (fun _ hd => hd) hb
  have hsuppb' : Supported env tbl (b.instantiate1' (.fvar x)) := by
    have := hsuppb.instantiate1 x; rwa [Lean.Expr.instantiate1_eq] at this
  obtain ⟨hrc, hreg, hle₂, hmb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb _ hinv' hsuppb' ⟨_, hbext⟩
  subst hs2
  subst hw2
  subst hteq
  refine ⟨hrc, hreg, NameGenerator.LE.trans hle₁ hle₂, fun Γspec hspec => ?_⟩
  exact ErasesLBMode.lam hspec.fvarFree
    (fun _ _ hbk hmem => hnres (hinv.fixvars_ids_subset hbk x hmem).1)
    hinv.noBV hty hbody hx (hmb Γspec hspec)

/-- **Step 8.** As step 9, with the value erased inside the extended context — where the
shipping code puts it — and brought back out by `Erases.strengthen_vlet`. -/
theorem step_visitLet : Step8 lenv env Us tbl cfg gw := by
  intro P _htbl _hcfg _hcb vExpr ih1
  refine ⟨?_, bodyLe8 ih1.2⟩
  replace ih1 := ih1.1
  intro e s ctx cctx ref w t s' w' hrun Δ n ty v b nd hinv he hsupp hex
  subst he
  simp only [visitLetBody, Erasure.letMonocular, Erasure.withLocalDef] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
  obtain ⟨hnres, hxres, hle₁, hkres⟩ := P.fresh_names _ _ _ _ _ _ _ _ hfresh
  have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
  rw [hs₁, run_withReader, run_bind_ok] at hk
  obtain ⟨tv, s₂, w₂, hvv, hk2⟩ := hk
  rw [run_bind_ok] at hk2
  obtain ⟨tb, s₃, w₃, hvb, hm⟩ := hk2
  obtain ⟨hs3, hw3, N, hteq⟩ := run_mkLetIn_ok hm
  obtain ⟨hterm, hbodies, hkn⟩ := hsupp
  cases hterm with
  | @letE _ _ _ _ _ _ hsv hsb =>
  obtain ⟨ve, hve⟩ := hex
  cases hve with
  | letE hvt hty hval hbody =>
  have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
  have hΔ' := TrLCtx.mkLetDecl (n := n) (nd := false) hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hval hvt
  have hinv' := hinv.mkLetDecl (n := n) hty hval hvt hx hnres hle₁ hxres hkres
  have hsuppv : Supported env tbl v :=
    Supported.subterm ⟨.letE hsv hsb, hbodies, hkn⟩ (fun _ hd => List.mem_append_left _ hd) hsv
  have hsuppb : Supported env tbl b :=
    Supported.subterm ⟨.letE hsv hsb, hbodies, hkn⟩ (fun _ hd => List.mem_append_right _ hd) hsb
  have hsuppb' : Supported env tbl (b.instantiate1' (.fvar x)) := by
    have := hsuppb.instantiate1 x; rwa [Lean.Expr.instantiate1_eq] at this
  have hvext := hval.weakFV P.envWF.ordered (.skip_fvar _ _ .refl) hΔ'.wf
  obtain ⟨hrcv, hregv, hle₂, hmv⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv _ hinv' hsuppv ⟨_, hvext⟩
  rw [Lean.Expr.instantiate1_eq] at hvb
  have hbext := TrExprS.inst_fvar P.envWF.ordered hΔ'.wf hbody
  obtain ⟨hrcb, hregb, hle₃, hmb⟩ :=
    ih1 _ _ _ _ _ _ _ _ _ hvb _ ((hinv'.mono_state hrcv hregv).mono hle₂) hsuppb' ⟨_, hbext⟩
  subst hs3
  subst hw3
  subst hteq
  refine ⟨hrcv.trans hrcb, hregb,
    NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hle₃), fun Γspec hspec => ?_⟩
  exact ErasesLBMode.letE hspec.fvarFree
    (fun _ _ hbk hmem => hnres (hinv.fixvars_ids_subset hbk x hmem).1)
    hinv.noBV hty hval hbody hx (hmv Γspec (SpecEnv.mono hrcb.le hspec)) (hmb Γspec hspec)

/-! ## Step 11 — `Erasure.visitApp` -/

/-- **Step 11.** A constant head goes to `Erasure.visitConstApp`; any other head is erased
on its own and the spine is rebuilt by `Erasure.visitAppArgs`. -/
theorem step_visitApp : Step11 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vExpr vArgs vConstApp ih1 ih7 ih12
  refine ⟨?_, bodyLe11 ih1.2 ih7.2 ih12.2⟩
  replace ih1 := ih1.1
  replace ih7 := ih7.1
  replace ih12 := ih12.1
  intro e s ctx cctx ref w t s' w' hrun Δ hinv hsupp hex hnind
  simp only [visitAppBody] at hrun
  cases hfn : e.getAppFn with
  | const cn us =>
    rw [hfn] at hrun
    simp only [] at hrun
    exact ih12 _ _ _ _ _ _ _ _ _ hrun Δ cn us hinv hfn hsupp hex (hnind cn us hfn)
  | _ =>
    all_goals (
      have hne : ∀ c us, e.getAppFn ≠ .const c us := by
        intro c us h; rw [hfn] at h; exact absurd h (by simp)
      obtain ⟨⟨hsuppfn, fve, htrfn⟩, hargs⟩ := spine_facts hsupp hex (hsupp.head hne)
      rw [hfn] at hrun
      simp only [] at hrun
      rw [Erasure.expr_withApp_eq, run_bind_ok] at hrun
      obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
      obtain ⟨hrc₁, hreg₁, hle₁, hf⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf Δ hinv hsuppfn ⟨fve, htrfn⟩
      obtain ⟨hrc₂, hreg₂, hle₂, hsp⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ e.getAppFn
        ((hinv.mono_state hrc₁ hreg₁).mono hle₁) hf hargs
      refine ⟨hrc₁.trans hrc₂, hreg₂, NameGenerator.LE.trans hle₁ hle₂, fun Γspec hspec => ?_⟩
      have := hsp Γspec hspec
      rwa [srcSpine, getAppArgs_spine] at this)

/-! ## Step 18 — `Erasure.visitAlt`

`Erasure.lambdaOrIntroToArity` peels the alternative's binders through the *inferred type*:
`Erasure.forallMonocular` pushes the `∀`'s binder name and domain, so the fragment's manifest
λ-telescope must be matched by the type's `∀`-telescope. `ForallMatchesLam` is that agreement;
`ErasureSpec.prim_monotone.inferType` is the clause that supplies it.
-/

/-- `ForallMatchesLam` holds whenever neither side has the shape it constrains. -/
theorem forallMatchesLam_of_not_lam {ty e : Expr}
    (h : ∀ n a b bi, e ≠ .lam n a b bi) : ForallMatchesLam ty e := by
  cases ty with
  | forallE n d c bi =>
    cases e with
    | lam m a b bi' => exact absurd rfl (h m a b bi')
    | _ => trivial
  | _ =>
    cases e with
    | lam m a b bi' => exact absurd rfl (h m a b bi')
    | _ => trivial

/-- Substituting a free variable never creates a λ head. -/
theorem instantiate1'_fvar_not_lam {e : Expr} (x : FVarId) (k : Nat)
    (h : ∀ n a b bi, e ≠ .lam n a b bi) :
    ∀ n a b bi, e.instantiate1' (.fvar x) k ≠ .lam n a b bi := by
  intro n a b bi
  cases e with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · simp
    · split
      · simp [Expr.liftLooseBVars']
      · simp
  | lam p q r t => exact absurd rfl (h p q r t)
  | _ => simp [Expr.instantiate1']

/-- The agreement survives opening one binder: `Erasure.lambdaMonocularOrIntro` instantiates
the `∀`'s codomain and the λ's body with the same fresh identifier. -/
theorem ForallMatchesLam.instantiate1' {ty e : Expr} (x : FVarId) :
    ForallMatchesLam ty e → ∀ k, ForallMatchesLam (ty.instantiate1' (.fvar x) k)
      (e.instantiate1' (.fvar x) k) := by
  induction ty generalizing e with
  | forallE n d c bi ihd ihc =>
    cases e with
    | lam m a b bi' =>
      intro h k
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by rw [h2], ihc h3 (k + 1)⟩
    | _ =>
      intro _ k
      exact forallMatchesLam_of_not_lam (instantiate1'_fvar_not_lam x k (by intro _ _ _ _; simp))
  | _ =>
    intro h k
    refine forallMatchesLam_of_not_lam (instantiate1'_fvar_not_lam x k ?_)
    intro nn aa bb bb'
    cases e with
    | lam p q r t => exact absurd h id
    | _ => simp

/-! ### `Erasure.mkAlt`'s closing, as a pure function -/

/-- Abstraction pushes under a λ-telescope, its insertion level raised by the telescope's
length. -/
theorem toBvar_mkLambdas (x : FVarId) (lvl : Nat) (names : List BinderName) (body : LBTerm) :
    toBvar x lvl (mkLambdas names body) = mkLambdas names (toBvar x (lvl + names.length) body) := by
  induction names generalizing lvl with
  | nil => rfl
  | cons n ns ih =>
    have h : lvl + (ns.length + 1) = lvl + 1 + ns.length := by omega
    simp only [mkLambdas, toBvar, List.length_cons, h, ih]

/-- `Erasure.mkAlt`'s de Bruijn closing loop as a pure function: the `i`-th binder counted
from the end becomes `.bvar i`. -/
def closeAlt : List FVarId → LBTerm → LBTerm
  | [], t => t
  | x :: xs, t => toBvar x xs.length (closeAlt xs t)

/-- …and it is the `for` loop `Erasure.mkAlt` runs. -/
theorem closeAlt_foldl (xs : List FVarId) (t : LBTerm) :
    xs.reverse.zipIdx.foldl (fun b p => toBvar p.1 p.2 b) t = closeAlt xs t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, List.zipIdx_append]
    simp only [List.foldl_append, List.length_reverse, List.zipIdx_cons, List.zipIdx_nil,
      List.foldl_cons, List.foldl_nil, ih, closeAlt]
    simp

/-- **Peeling one alternative binder.** A λ-telescope over a `closeAlt` on a cons is one
`.lambda` over `toBvar x 0` of the rest — the shape the binder case produces. -/
theorem mkLambdas_closeAlt_cons (N : BinderName) (Ns : List BinderName)
    (x : FVarId) (xs : List FVarId) (t : LBTerm) (h : Ns.length = xs.length) :
    mkLambdas (N :: Ns) (closeAlt (x :: xs) t)
      = .lambda N (toBvar x 0 (mkLambdas Ns (closeAlt xs t))) := by
  rw [toBvar_mkLambdas]
  simp only [mkLambdas, closeAlt, Nat.zero_add, h]

/-! ### Opening the alternative's telescope -/

/-- **`Erasure.lambdaOrIntroToArity` on a manifest λ-telescope.** It peels `n` binders through
the inferred type, extends the invariant at each one, and hands the continuation the opened
body with the `n` fresh identifiers. The closing conjunct re-binds them: any erasure of the
opened body is an erasure of the original telescope against `mkLambdas … (closeAlt …)`, which
is the shape `Erasure.mkAlt` emits. `K` is arbitrary, so the fixpoint step stays plumbing. -/
theorem bridge_alt_telescope {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (P : ErasureSpec lenv env Us gw)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) :
    ∀ (n : Nat) (e ty : Expr) (Δ : VLCtx)
      (K : Expr → List FVarId → EraseM (List BinderName × LBTerm))
      (s : ErasureState) (ctx : ErasureContext) (w : Void IO.RealWorld)
      (r : List BinderName × LBTerm) (s' : ErasureState) (w' : Void IO.RealWorld),
      Erasure.lambdaOrIntroToArity e ty n K s ctx cctx ref w = .ok (r, s') w' →
      BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      IsLamTelescope n e → Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      ForallMatchesLam ty e →
      ∃ (ys : List FVarId) (Ns : List BinderName) (efin : Expr) (Δ' : VLCtx)
        (ctx' : ErasureContext) (w₁ : Void IO.RealWorld),
        ys.length = n ∧ Ns.length = n ∧ gw w ≤ gw w₁ ∧ ctx'.fixvars = ctx.fixvars ∧
        (∀ y ∈ ys, ¬ (gw w).Reserves y) ∧
        BridgeInv env Us tbl cfg (gw w₁) ctx' s Δ' ∧
        Supported env tbl efin ∧ (∃ ve, TrExprS env Us Δ' efin ve) ∧
        K efin ys s ctx' cctx ref w₁ = .ok (r, s') w' ∧
        ∀ t : LBTerm, Erases env Us Δ' efin t →
          Erases env Us Δ e (mkLambdas Ns (closeAlt ys t)) := by
  intro n
  induction n with
  | zero =>
    intro e ty Δ K s ctx w r s' w' hrun hinv _ hsupp hex _
    exact ⟨[], [], e, Δ, ctx, w, rfl, rfl, NameGenerator.LE.rfl, rfl,
      (fun y hy => absurd hy (by simp)), hinv, hsupp, hex, hrun, fun _ het => het⟩
  | succ n ih =>
    intro e ty Δ K s ctx w r s' w' hrun hinv hlam hsupp hex hfml
    cases e with
    | lam nm A b bi =>
      cases ty with
      | forallE nm' A' Cc bi' =>
        obtain ⟨rfl, rfl, hfml'⟩ := hfml
        have hlam' : IsLamTelescope n b := hlam
        simp only [Erasure.lambdaOrIntroToArity, Erasure.lambdaMonocularOrIntro,
          Erasure.forallMonocular, Erasure.withLocalDecl] at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
        obtain ⟨hnres, hxres, hle₁, hkres⟩ := P.fresh_names _ _ _ _ _ _ _ _ hfresh
        have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
        rw [hs₁, run_withReader] at hk
        obtain ⟨ve, hve⟩ := hex
        cases hve with
        | lam hty' hty hbody =>
        obtain ⟨hterm, hbodies, hkn⟩ := hsupp
        cases hterm with
        | @lam _ _ _ _ _ hb =>
        have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
        have hfind : ctx.lctx.find? x = none := hinv.trlctx.find?_eq_none.mpr hx
        have hΔ' := TrLCtx.mkLocalDecl (n := nm') (bi := bi') hinv.trlctx hfind hty hty'
        have hinv' := hinv.mkLocalDecl (n := nm') (bi := bi') hty hty' hx hnres hle₁ hxres hkres
        rw [Lean.Expr.instantiate1_eq, Lean.Expr.instantiate1_eq] at hk
        have hbext := TrExprS.inst_fvar P.envWF.ordered hΔ'.wf hbody
        have hsuppb : Supported env tbl b :=
          Supported.subterm ⟨.lam hb, hbodies, hkn⟩ (fun _ hd => hd) hb
        have hsuppb' : Supported env tbl (b.instantiate1' (.fvar x)) := by
          have := hsuppb.instantiate1 x; rwa [Lean.Expr.instantiate1_eq] at this
        obtain ⟨ys, Ns, efin, Δ'', ctx'', w₂, hlen, hnlen, hle₂, hfx, hfr, hinv'', hsupp'',
          hex'', hK, hclose⟩ :=
          ih (b.instantiate1' (.fvar x)) (Cc.instantiate1' (.fvar x)) _
            (fun e' fvs => K e' (x :: fvs)) _ _ _ _ _ _ hk hinv' (hlam'.instantiate1' 0)
            hsuppb' ⟨_, hbext⟩ (hfml'.instantiate1' x 0)
        refine ⟨x :: ys, .named nm'.toString :: Ns, efin, Δ'', ctx'', w₂, by simp [hlen],
          by simp [hnlen], NameGenerator.LE.trans hle₁ hle₂, by rw [hfx], ?_, hinv'', hsupp'',
          hex'', hK, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hnres
          · exact fun hres => hfr y hy (hres.mono hle₁)
        · intro t het
          rw [mkLambdas_closeAlt_cons _ _ _ _ _ (by omega)]
          refine .lam hty ((hclose t het).uninstantiate ?_ ?_)
          · have hfv : FVarsIn (· ∈ Δ.fvars) b := by
              have := hbody.fvarsIn; simpa [Lean4Lean.VLCtx.fvars] using this
            exact hfv.mono fun fv hfv' heq => hx (heq ▸ hfv')
          · have := hbody.closed; simpa [Lean4Lean.VLCtx.bvars, hinv.noBV] using this
      | _ => exact absurd hfml id
    | _ => exact absurd hlam id

/-! ### The alternative, closed -/

/-- A trivial argmask filters nothing: the list-level computation. -/
theorem filterMap_zip_replicate {α : Type} (n : Nat) : ∀ (l : List α), l.length = n →
    ((List.replicate n Erasure.ConstructorArgRelevance.keep).zip l).filterMap
      (fun x => match x.1 with
        | Erasure.ConstructorArgRelevance.erase => none
        | Erasure.ConstructorArgRelevance.keep => some x.2) = l := by
  induction n with
  | zero => intro l hl; rw [List.eq_nil_of_length_eq_zero hl]; rfl
  | succ n ih =>
    intro l hl
    match l with
    | a :: as =>
      simp only [List.replicate, List.zip_cons_cons, List.filterMap_cons]
      rw [ih as (by simpa using hl)]

/-- A trivial argmask of the field list's own width is the identity on it, which is what
makes `Erasure.visitAlt`'s `Erasure.filter` disappear. `ConfigPinned` is where the argmask's
triviality comes from; the model represents no argmask filtering at all. -/
theorem filter_replicate_keep_of_size {α : Type} (n : Nat) (arr : Array α) (h : arr.size = n) :
    Erasure.filter (Array.replicate n Erasure.ConstructorArgRelevance.keep) arr = arr := by
  unfold Erasure.filter
  apply Array.toList_inj.mp
  rw [Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  exact filterMap_zip_replicate n arr.toList (by rw [Array.length_toList]; exact h)

/-- The mode reads only the reader's fixvar map, so it transports along an extension that
leaves it alone — which is every extension the binder helpers make. -/
theorem ErasesLBMode.congr_fixvars {ctx' : ErasureContext} {e : Expr} {t : LBTerm}
    (hfx : ctx'.fixvars = ctx.fixvars) (h : ErasesLBMode tbl ctx' env Us Γspec Δ e t) :
    ErasesLBMode tbl ctx env Us Γspec Δ e t :=
  ⟨fun hn => h.1 (by rw [hfx]; exact hn),
    fun nms ids hs => h.2 nms ids ⟨by rw [hfx]; exact hs.1, hs.2⟩⟩

/-- The pass pushes through `closeAlt`, one `Lower.abstract` step per field binder. -/
theorem lower_closeAlt {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) :
    ∀ (ys : List FVarId) {a b : LBTerm}, Lower Γ a b → Lower Γ (closeAlt ys a) (closeAlt ys b)
  | [], _, _, h => h
  | y :: ys, _, _, h => Lower.abstract hfv (lower_closeAlt hfv ys h) y ys.length

/-- Block rewriting pushes through `closeAlt`, provided no field binder is a fix variable. -/
theorem constToFVar_closeAlt {kns : List Kername} {ids : List FVarId} :
    ∀ (ys : List FVarId), (∀ y ∈ ys, y ∉ ids) → ∀ {a b : LBTerm},
      ConstToFVar kns ids a b → ConstToFVar kns ids (closeAlt ys a) (closeAlt ys b)
  | [], _, _, _, h => h
  | y :: ys, hy, _, _, h =>
    (constToFVar_closeAlt ys (fun z hz => hy z (List.mem_cons_of_mem _ hz)) h).abstracts
      (hy y List.mem_cons_self) ys.length

/-- A λ-telescope over a lowered body is the alternative `Erasure.mkAlt` emits: `LowerAlt`
peels one binder per field and leaves the names free. -/
theorem lowerAlt_mkLambdas {Γ : GlobalDeclarations} :
    ∀ (Ns names : List BinderName) {a b : LBTerm}, names.length = Ns.length → Lower Γ a b →
      LowerAlt Γ Ns.length (mkLambdas Ns a) (names, b)
  | [], [], _, _, _, h => .done h
  | N :: Ns, n' :: names, a, b, hlen, h => by
    have := lowerAlt_mkLambdas Ns names (by simpa using hlen) h
    exact .lam (alt := (names, b)) this

/-- **The composite at one alternative.** The telescope's closing gives the source side; the
two pass factors follow it through `closeAlt`. -/
theorem ErasesLBAltMode.mk (hfv : FVarFreeBodies Γspec) {ys : List FVarId}
    (hyids : ∀ nms ids, BlockKeyed tbl ctx nms ids → ∀ y ∈ ys, y ∉ ids)
    {Δ' : VLCtx} {Ns : List BinderName} {nf : Nat} {m efin : Expr} {t : LBTerm}
    {alt : List BinderName × LBTerm}
    (hNs : Ns.length = nf) (hnames : alt.1.length = nf) (halt : alt.2 = closeAlt ys t)
    (hclose : ∀ t₀, Erases env Us Δ' efin t₀ →
      Erases env Us Δ m (mkLambdas Ns (closeAlt ys t₀)))
    (h : ErasesLBMode tbl ctx env Us Γspec Δ' efin t) :
    ErasesLBAltMode tbl ctx env Us Γspec Δ nf m alt := by
  subst hNs
  refine ⟨fun hfx => ?_, fun nms ids hfx => ?_⟩
  · obtain ⟨t₀, her, hl⟩ := h.1 hfx
    refine ⟨mkLambdas Ns (closeAlt ys t₀), hclose t₀ her, ?_⟩
    have := lowerAlt_mkLambdas Ns alt.1 hnames (lower_closeAlt hfv ys hl)
    rwa [← halt] at this
  · obtain ⟨t₀, t₁, her, hl, hcf⟩ := h.2 nms ids hfx
    refine ⟨(alt.1, closeAlt ys t₁), ⟨mkLambdas Ns (closeAlt ys t₀), hclose t₀ her,
      lowerAlt_mkLambdas Ns alt.1 hnames (lower_closeAlt hfv ys hl)⟩, rfl, ?_⟩
    rw [halt]
    exact constToFVar_closeAlt ys (hyids nms ids hfx) hcf

/-! ## Step 12 — `Erasure.visitConstApp` -/

/-- **A tabled constructor's arithmetic is the kernel's.** `ctorOf?` reads the constructor
column of the tabled inductive the head's name prefix picks out, and
`Witness.ReifiedInduct.Pinned` matches that entry against `lenv`'s own `ConstructorVal`. -/
theorem ctorOf?_pinned (htbl : SourceTableAdequate lenv tbl) {c : Name}
    {p : Name × ReifiedCtor} (h : ctorOf? tbl c = some p) :
    ∃ cv : ConstructorVal, lenv.find? c = some (.ctorInfo cv) ∧
      cv.numParams = p.2.numParams ∧ cv.numFields = p.2.numFields := by
  rw [ctorOf?] at h
  split at h
  next I hind =>
    cases hf : I.ctors.find? (fun x => x.name == c) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some cb =>
      rw [hf] at h
      obtain rfl : (c.getPrefix, cb) = p := by simpa using h
      have hname : cb.name = c := by
        have := List.find?_some hf
        simpa using this
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hf)
      obtain ⟨iv, -, -, -, -, -, -, -, -, -, hcs⟩ := htbl.inds _ I (mem_of_lookup hind)
      obtain ⟨cv, hcvf, -, -, -, hnp, -, hnf, -⟩ :=
        hcs j cb (by rw [List.getElem?_eq_getElem hj, hjeq])
      exact ⟨cv, hname ▸ hcvf, hnp, hnf⟩
  next => exact absurd h (by simp)

/-- **Step 12.** The head's classification picks the arm: an eliminator goes to
`Erasure.visitCasesEta`, a constructor to `Erasure.visitCtorEta`, and any other constant is
erased by `Erasure.visitConst` with the spine rebuilt by `Erasure.visitAppArgs`.

`TableSafe.declCtor` is what closes the gap between the two constructor readings: the fragment
decides N19's constructor half against `ctorOf?`, the run reads
`Lean.Compiler.LCNF.getCtorArity?`, and `KnownHead.defn` admits a constructor `lenv` declares
that the table holds in its constant column alone. The `getCtorArity?` miss is also where
`Motive4`'s constructor exclusion is produced, through `BlockAdequate.ctorBwd`. -/
theorem step_visitConstApp (hsafe : TableSafe lenv tbl) :
    Step12 lenv env Us tbl cfg gw := by
  intro P htbl _hcfg _hcb vConst vArgs vCtorEta vCasesEta ih4 ih7 ih13 ih15
  refine ⟨?_, bodyLe12 ih4.2 ih7.2 ih13.2 ih15.2⟩
  replace ih4 := ih4.1
  replace ih7 := ih7.1
  replace ih13 := ih13.1
  replace ih15 := ih15.1
  intro e s ctx cctx ref w t s' w' hrun Δ cn us hinv hfn hsupp hex hnind
  have hargs := spine_args_ok hsupp hex
  have hheadS : SupportedTm env tbl (.const cn us) e.getAppArgs.toList := by
    have hsuppS : SupportedTm env tbl (e.getAppArgs.toList.foldl Expr.app e.getAppFn) [] := by
      rw [getAppArgs_spine]; exact hsupp.term
    have := (supportedTm_foldl_app_inv hsuppS).1
    rw [hfn] at this
    simpa using this
  simp only [visitConstAppBody] at hrun
  rw [Erasure.expr_withApp_eq, hfn] at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨o, s₁, w₁, hcs, hk⟩ := hrun
  rw [run_liftCoreM_ok] at hcs
  obtain ⟨hcs, rfl⟩ := hcs
  have hlecs : gw w ≤ gw w₁ := (P.lookup_adequate.casesInfo cn cctx ref w o w₁ hcs).1
  cases o with
  | some ci =>
    obtain ⟨hcname, hdecl, hagreeK⟩ :=
      (P.lookup_adequate.casesInfo cn cctx ref w _ w₁ hcs).2.1 ci rfl
    simp only [] at hk
    -- the fragment's own eliminator arm supplies the tabled inductive
    cases hheadS with
    | const hplain hcases _ _ _ => rw [hcname] at hcases; exact absurd hcases (by simp)
    | @casesApp _ _ _ minors I hplain hcases hind hinf harity hmin hlen htel =>
      have hag : CasesInfoAgrees ci cn I := CasesInfoAgrees.of_pinned htbl hind hdecl hagreeK
      have hcasesHead : CasesHead env tbl ci cn I :=
        ⟨hplain, hcname, hind, hinf, hag⟩
      have hsat : ci.arity ≤ e.getAppArgs.size := by
        rw [hag.arity]; simpa using harity
      obtain ⟨hrc, hreg, hle₂, hm⟩ := ih15 _ _ _ _ _ _ _ _ _ _ hk Δ cn us I (hinv.mono hlecs)
        hfn hcasesHead hsat hsupp hargs hex
      exact ⟨hrc, hreg, NameGenerator.LE.trans hlecs hle₂, hm⟩
  | none =>
    have hnc : isCasesOnName cn = false :=
      (P.lookup_adequate.casesInfo cn cctx ref w _ w₁ hcs).2.2 rfl
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨o₂, s₂, w₂, hct, hk⟩ := hk
    rw [run_liftCoreM_ok] at hct
    obtain ⟨hct, rfl⟩ := hct
    have hlect : gw w₁ ≤ gw w₂ := (P.lookup_adequate.ctorArity cn cctx ref w₁ o₂ w₂ hct).1
    cases hheadS with
    | casesApp _ hcases _ _ _ _ _ _ => rw [hnc] at hcases; exact absurd hcases (by simp)
    | @const _ _ _ hplain hcases hrec hsatT hknown =>
      cases o₂ with
      | some ar =>
        obtain ⟨cv, hcvf, harar⟩ :=
          (P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.1 ar rfl
        have hctor : ∃ I k, CtorOf env cn I k := ⟨_, _, P.block_adequate.ctor cn cv hcvf⟩
        have hcol : (ctorOf? tbl cn).isSome := by
          cases hknown with
          | indType hind _ =>
            obtain ⟨iv, hiv, -⟩ := htbl.inds _ _ (mem_of_lookup hind)
            rw [hcvf] at hiv; exact absurd hiv (by simp)
          | ctor hc _ => rw [hc]; rfl
          | defn hd _ => exact hsafe.declCtor cn cv (by rw [hd]; rfl) hcvf
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hcol
        obtain ⟨cv', hcvf', hnp, hnf⟩ := ctorOf?_pinned htbl hp
        obtain rfl : cv' = cv := by simpa using hcvf'.symm.trans hcvf
        have harp : ar ≤ p.2.numParams + p.2.numFields :=
          Nat.le_of_eq (by rw [harar, hnp, hnf])
        have hsat : ar ≤ e.getAppArgs.size := by
          have := hsatT p hp
          simpa using Nat.le_trans harp this
        simp only [] at hk
        obtain ⟨hrc, hreg, hle₃, hm⟩ := ih13 _ _ _ _ _ _ _ _ _ _ _ hk Δ us
          (hinv.mono (NameGenerator.LE.trans hlecs hlect)) hfn hctor hsat hargs
        exact ⟨hrc, hreg, NameGenerator.LE.trans hlecs (NameGenerator.LE.trans hlect hle₃), hm⟩
      | none =>
        have hnoctor : ∀ (I : Name) (k : Nat), ¬ CtorOf env cn I k := by
          intro I k hck
          obtain ⟨cv, hcvf, -, -⟩ := P.block_adequate.ctorBwd cn I k hck
          exact (P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.2 rfl cv hcvf
        have hnone : ctorOf? tbl cn = none := by
          cases hcc : ctorOf? tbl cn with
          | none => rfl
          | some p =>
            obtain ⟨cv, hcvf, -, -⟩ := ctorOf?_pinned htbl hcc
            exact absurd hcvf
              ((P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.2 rfl cv)
        have hheadNil : SupportedTm env tbl (.const cn us) [] :=
          .const hplain hcases hrec (fun p hp => by rw [hnone] at hp; exact absurd hp (by simp))
            hknown
        have hsubf : ∀ d ∈ constNames (Expr.const cn us), d ∈ constNames e := by
          obtain ⟨hsubf, -⟩ := constNames_spine_sub e.getAppArgs.toList e.getAppFn
          rw [getAppArgs_spine] at hsubf
          rw [← hfn]
          exact hsubf
        have hheadSupp : Supported env tbl (.const cn us) := hsupp.subterm hsubf hheadNil
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨tc, s₃, w₃, hvc, hk⟩ := hk
        obtain ⟨hrc₃, hreg₃, hle₃, hmc⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc Δ cn us
          (hinv.mono (NameGenerator.LE.trans hlecs hlect)) rfl hplain hcases hknown hheadSupp
          hnoctor hnind
        obtain ⟨hrc₄, hreg₄, hle₄, hsp⟩ := ih7 _ _ _ _ _ _ _ _ _ _ hk Δ (.const cn us)
          ((hinv.mono_state hrc₃ hreg₃).mono
            (NameGenerator.LE.trans hlecs (NameGenerator.LE.trans hlect hle₃)))
          hmc hargs
        refine ⟨hrc₃.trans hrc₄, hreg₄, NameGenerator.LE.trans hlecs
          (NameGenerator.LE.trans hlect (NameGenerator.LE.trans hle₃ hle₄)),
          fun Γspec hspec => ?_⟩
        have := hsp Γspec hspec
        rw [srcSpine, ← hfn, getAppArgs_spine] at this
        exact this

/-! ## Step 18 — `Erasure.visitAlt` -/

/-- **Step 18.** The minor premise's binders are opened by `bridge_alt_telescope`, the opened
body is erased by `Motive1`, and `Erasure.mkAlt` closes the result — which is what
`ErasesLBAltMode.mk` reads as an alternative of the composite. -/
theorem step_visitAlt : Step18 lenv env Us tbl cfg gw := by
  intro P _htbl _hcfg _hcb vExpr ih1
  refine ⟨?_, bodyLe18 ih1.2⟩
  replace ih1 := ih1.1
  intro nf mask e s ctx cctx ref w r s' w' hrun Δ hinv hmask hlam hsupp hex
  simp only [visitAltBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hity, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hity
  rw [hs₁] at hity hk
  obtain ⟨hlei, hfml⟩ := P.prim_monotone.inferType e s ctx cctx ref w ty s w₁ hity
  obtain ⟨ys, Ns, efin, Δ', ctx', w₂, hlen, hnlen, hle₂, hfx, hyfresh, hinv', hsupp', hex',
    hK, hclose⟩ := bridge_alt_telescope P cctx ref nf e ty Δ _ s ctx w₁ r s' w' hk
      (hinv.mono hlei) hlam hsupp hex hfml
  rw [hmask, filter_replicate_keep_of_size nf ys.toArray (by simp [hlen]), List.toList_toArray,
    run_bind_ok] at hK
  obtain ⟨tb, s₂, w₃, hvb, hm⟩ := hK
  obtain ⟨hs2, hw2, hrlen, hr2⟩ := run_mkAlt_ok hm
  obtain ⟨hrc, hreg, hle₃, hmb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb Δ' hinv' hsupp' hex'
  subst hs2
  subst hw2
  refine ⟨hrc, hreg, NameGenerator.LE.trans hlei (NameGenerator.LE.trans hle₂ hle₃),
    fun Γspec hspec => ?_⟩
  refine ErasesLBAltMode.mk hspec.fvarFree ?_ hnlen (by rw [hrlen, hlen])
    (by rw [hr2, closeAlt_foldl]) hclose (ErasesLBMode.congr_fixvars hfx (hmb Γspec hspec))
  intro _ _ hbk y hy hmem
  exact hyfresh y hy ((hinv.fixvars_ids_subset hbk y hmem).1.mono hlei)

end Steps

/-! ## The `visitMutual` step — the block's λ-headedness

`Lower.fixConst`/`fixBody` read a mutual block through `LowerBlock`, whose `hfl` field asks
every emitted definition to be λ-headed. `mkDef`'s closing preserves λ-headedness in both
directions, so the field *is* the λ-headedness of each member's erased body — which
`Erasure.visitExpr` does not deliver, answering `.box` at its erasability gate. It comes
from `LBWfPeregrine.fixLambda`, read at the block through `FixLambda.of_onProgram`.
-/

/-- **λ-headedness is not a run invariant.** A member whose erasure is `.box` — what
`Erasure.visitExpr` returns at its erasability gate — is registered as a definition with a
non-λ body, and `LowerBlock.hfl` fails. That is why `TableBlocks.informative`, which excludes
an erasable member, is a conjunct of the input condition and not a formality. -/
theorem run_mkDef_box_not_lambda {nm : Name} {fixvarnames : List Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : @FixDef LBTerm} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : mkDef nm fixvarnames .box s ctx cctx ref w = .ok (r, s₁) w₁) :
    isLambda r.body = false := run_mkDef_isLambda hrun

/-- A declared entry answers its own lookup when no key is declared twice. -/
theorem envLookup_of_mem_of_keys {Γ : GlobalDeclarations} {kn : Kername} {d : GlobalDecl}
    (hkeys : (Γ.map Prod.fst).Pairwise (fun a b => Kername.beq a b = false))
    (hmem : (kn, d) ∈ Γ) : LBTerm.envLookup Γ kn = some d := by
  induction Γ with
  | nil => exact absurd hmem (by simp)
  | cons hd rest ih =>
      obtain ⟨k, d'⟩ := hd
      rw [List.map_cons, List.pairwise_cons] at hkeys
      rw [LBTerm.envLookup]
      rcases List.mem_cons.mp hmem with heq | hmem'
      · cases heq; rw [if_pos (Kername.beq_self _)]
      · have hne : Kername.beq k kn = false :=
          hkeys.1 kn (List.mem_map.mpr ⟨(kn, d), hmem', rfl⟩)
        rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
        exact ih hkeys.2 hmem'

/-- **`LowerBlock.hfl` at a block the emitted environment declares.** The block's own entry
is one of the constant bodies `LBWfPeregrine.fixLambda` quantifies over, and `keys` makes
that entry answer its lookup. -/
theorem visitMutual_block_hfl {Γ : GlobalDeclarations} {t : LBTerm} {kn : Kername}
    {defs : List (@FixDef LBTerm)} {j : Nat} (hwf : LBWfPeregrine Γ t)
    (hmem : (kn, .constantDecl ⟨some (.fix defs j)⟩) ∈ Γ) :
    ∀ i, i < defs.length → isLambda (defs[i]!).body = true :=
  FixLambda.of_onProgram
    ⟨hwf.fixLambda.2 kn _ (envLookup_of_mem_of_keys hwf.keys hmem), hwf.fixLambda.2⟩ .refl rfl

/-! ### The block's entries, from the registration fold -/

/-- The registration fold only prepends. -/
theorem gdecls_mono_foldl_recConstStep (defs : List (@FixDef LBTerm)) :
    ∀ (ps : List (Name × Nat)) (s : ErasureState) (q : Kername × GlobalDecl),
      q ∈ s.gdecls → q ∈ (ps.foldl (recConstStep defs) s).gdecls := by
  intro ps
  induction ps with
  | nil => intro s q hq; exact hq
  | cons p rest ih =>
      intro s q hq
      refine ih _ q ?_
      rw [recConstStep, nonrecConstState_gdecls]
      exact List.mem_cons_of_mem _ hq

/-- Every step of the fold leaves its own entry behind. -/
theorem mem_gdecls_foldl_recConstStep (defs : List (@FixDef LBTerm)) :
    ∀ (ps : List (Name × Nat)) (p : Name × Nat) (s : ErasureState), p ∈ ps →
      (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) ∈
        (ps.foldl (recConstStep defs) s).gdecls := by
  intro ps
  induction ps with
  | nil => intro p s hp; exact absurd hp (by simp)
  | cons q rest ih =>
      intro p s hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · refine gdecls_mono_foldl_recConstStep defs rest _ _ ?_
        rw [recConstStep, nonrecConstState_gdecls]
        exact List.mem_cons_self
      · exact ih p _ hp'

/-- `Erasure.visitMutual`'s recursive exit declares the block at every member's kername. -/
theorem mem_gdecls_recConstState {names : List Name} {defs : List (@FixDef LBTerm)}
    {s : ErasureState} {p : Name × Nat} (hp : p ∈ names.zipIdx) :
    (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) ∈
      (recConstState names defs s).gdecls := by
  rw [recConstState_eq]; exact mem_gdecls_foldl_recConstStep defs _ p s hp

/-- A declared entry survives every later registration. -/
theorem stateLe_mem_gdecls {s s' : ErasureState} (h : StateLe s s')
    {q : Kername × GlobalDecl} (hq : q ∈ s.gdecls) : q ∈ s'.gdecls := by
  obtain ⟨pre, hpre⟩ := h.gdecls
  rw [hpre]; exact List.mem_append_right pre hq

/-- **The step's conclusion, at the run.** A block registered by `visitMutual`'s recursive
exit is λ-headed at every member, read off the well-formedness of the program the run ends
with. This is `LowerBlock.hfl`'s statement at the block being closed; the other eleven
fields are the environment-side bridge's. -/
theorem visitMutual_block_hfl_of_run {names : List Name} {defs : List (@FixDef LBTerm)}
    {s s' : ErasureState} {t : LBTerm} {p : Name × Nat}
    (hwf : LBWfPeregrine s'.gdecls t) (hle : StateLe (recConstState names defs s) s')
    (hp : p ∈ names.zipIdx) :
    ∀ i, i < defs.length → isLambda (defs[i]!).body = true :=
  visitMutual_block_hfl hwf (stateLe_mem_gdecls hle (mem_gdecls_recConstState hp))

/-! ### The supply, exercised at a two-member block

`LowerFixFixture`'s block, under a λ so the closure step is a real one: the program's
`FixLambda` yields the fixture's own `hfl` field, and the block rebuilt with it type-checks
against `LowerBlock`. -/

/-- Neither member body of the fixture's block holds a `.fix` node, so the block is the only
one in its own subterm closure. -/
theorem fixtureBlock_fixLambda (j : Nat) : FixLambda (.fix LowerFixFixture.defs j) := by
  intro defs' i' h
  cases h with
  | refl =>
      intro fd hfd
      rw [LowerFixFixture.defs] at hfd
      rcases List.mem_cons.mp hfd with rfl | hfd
      · exact ⟨_, _, rfl⟩
      · rcases List.mem_cons.mp hfd with rfl | hfd
        · exact ⟨_, _, rfl⟩
        · exact absurd hfd (by simp)
  | fixBody hmem hsub =>
      rw [LowerFixFixture.defs] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · cases hsub with
        | lambda hs => cases hs
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · cases hsub with
          | lambda hs => cases hs with
            | appFn h2 => cases h2
            | appArg h2 => cases h2
        · exact absurd hmem (by simp)

/-- The fixture's block under a binder: a program whose `.fix` node is a proper subterm. -/
def fixtureBlockProg : LBTerm := .lambda (.named "y") (.fix LowerFixFixture.defs 1)

/-- The program and the fixture's emitted environment satisfy the `.fix` clause. -/
theorem fixtureBlock_onProgram :
    OnProgram LowerFixFixture.targetEnv fixtureBlockProg FixLambda := by
  constructor
  · intro defs' i' h
    cases h with
    | lambda hs => exact fixtureBlock_fixLambda 1 defs' i' hs
  · intro kn b hb
    rw [LowerFixFixture.targetEnv, LBTerm.envLookup] at hb
    split at hb
    · cases hb; exact fixtureBlock_fixLambda 0
    · rw [LBTerm.envLookup] at hb
      split at hb
      · cases hb; exact fixtureBlock_fixLambda 1
      · exact absurd hb (by simp [LBTerm.envLookup])

/-- The λ-headedness of the fixture's block, through the subterm closure. -/
theorem fixtureBlock_hfl :
    ∀ i, i < LowerFixFixture.defs.length →
      isLambda (LowerFixFixture.defs[i]!).body = true :=
  FixLambda.of_onProgram fixtureBlock_onProgram (.lambda .refl) rfl

/-- **The supply fits the field.** The fixture's `LowerBlock`, rebuilt with the `hfl` the
closure produced in place of its own. -/
theorem fixtureBlock_lowerBlock :
    LowerBlock LowerFixFixture.specEnv LowerFixFixture.kns LowerFixFixture.bs
      LowerFixFixture.bs LowerFixFixture.ids LowerFixFixture.defs :=
  { LowerFixFixture.lowerfix_nv with hfl := fixtureBlock_hfl }

end LeanToLambdaBox
