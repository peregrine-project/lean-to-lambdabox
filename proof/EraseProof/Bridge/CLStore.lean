import EraseProof.Spec
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Model.Inductives.BlockRunFacts
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Verify.Cached.PushChain

/-!
# What con-leche's fold stores of the program's declarations

Each step of con-leche's pure fold pushes exactly the constants and tables its declaration
installs (`CL ConLeche/Kernel/Install.lean:84 declConstants`), under names unbound before it, so
the environment the fold returns finds each of them by its name (`checkDeclsPure_find?`). Read back
through `DeclsOf?`: a safe definition of `P` is stored with its translated type, level parameters
and value; a theorem with its translated type and no value; a safe opaque and a safe axiom as an
axiom with their translated type, except an axiom named `sorryAx`, which is stored as nothing. Of
a safe inductive block, every recursor is stored as its translated record with one install-computed
firing mode on its rules.
-/

open Lean Erasure

namespace EraseProof

/-! ## The fold -/

/-- Two members of a list with the same image under a map that is injective on the list are
equal. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: l, hnd, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (by rw [he]; exact List.mem_map_of_mem hy') hnd.1
    · exact absurd (by rw [← he]; exact List.mem_map_of_mem hx') hnd.1
    · exact eq_of_nodup_map hnd.2 hx' hy' he

/-- Constants pushed under names unbound before them leave every bound name's constant in
place. -/
theorem find?_pushDelta_old {env : ConLeche.Env} {L : List ConLeche.ConstantInfo}
    {Q : List ConLeche.ProjTable} (hL : ∀ c ∈ L, env.find? c.name = none) {n : ConLeche.Name}
    {c : ConLeche.ConstantInfo} (h : env.find? n = some c) : (env.pushDelta L Q).find? n = some c := by
  show (L.reverse ++ env.consts).find? (·.name == n) = some c
  rw [List.find?_append, List.find?_eq_none.mpr]
  · exact h
  · intro c' hc' hn
    rw [beq_iff_eq] at hn
    have := hL c' (List.mem_reverse.mp hc')
    rw [hn, h] at this
    exact nomatch this

/-- A pushed constant whose name is pushed once is found. -/
theorem find?_pushDelta_new {env : ConLeche.Env} {L : List ConLeche.ConstantInfo}
    {Q : List ConLeche.ProjTable} (hnd : (L.map (·.name)).Nodup) {c : ConLeche.ConstantInfo}
    (hc : c ∈ L) : (env.pushDelta L Q).find? c.name = some c := by
  show (L.reverse ++ env.consts).find? (·.name == c.name) = some c
  rw [List.find?_append]
  cases hx : L.reverse.find? (·.name == c.name) with
  | none =>
    exact absurd (List.find?_eq_none.mp hx c (List.mem_reverse.mpr hc)) (by simp)
  | some x =>
    have hxL := List.mem_reverse.mp (List.mem_of_find?_eq_some hx)
    have hxn : x.name = c.name := by simpa using List.find?_some hx
    rw [eq_of_nodup_map hnd hxL hc hxn]
    rfl

/-- `sorryAx` passes no standard-axiom guard. Reference: `CL ConLeche/Verify/Cached/DeclPushes.lean:529
tolerated_not_std`, at the pure guard. -/
theorem stdAxiomOk_sorryAx (env : ConLeche.Env) {cv : ConLeche.ConstantVal}
    (ht : cv.name = ConLeche.sorryAxName) : ConLeche.stdAxiomOk env cv = false := by
  rw [ConLeche.stdAxiomOk, ite_eq_right, ite_eq_right] <;> rw [ht] <;> decide

/-- **One accepted step of the pure fold pushes what its declaration installs**
(`CL ConLeche/Kernel/Install.lean:84 declConstants`, `:99 declTables`), under names unbound
before it: by the step's run record (`CL ConLeche/Semantics/Bridge/Sound.lean:41
checkDeclRun_ofEnvFactsK`), a block's by `CL ConLeche/Semantics/Inductives/DeclBlock.lean:190
blockRun_env` and `CL ConLeche/Model/Inductives/BlockRunFacts.lean:62 blockRun_fresh`. The pure-fold
analogue of `CL ConLeche/Verify/Cached/DeclPushes.lean:694 checkDeclC_pushes`. -/
theorem checkDecl_pushes {F : Nat} {pins : List ConLeche.NatOpPinSet} {env env₂ : ConLeche.Env}
    {d : ConLeche.Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins env d = .ok env₂) :
    env₂ = env.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d) ∧
      ∀ c ∈ ConLeche.declConstants d, env.find? c.name = none := by
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  have one : ∀ c : ConLeche.ConstantInfo, (env.find? c.name).isNone = true →
      (∀ c' ∈ [c], env.find? c'.name = none) := by
    intro c hc c' hc'
    rw [List.mem_singleton.mp hc']
    exact Option.isNone_iff_eq_none.mp hc
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', ⟨hfr, -, -, -, rfl, -⟩, ⟨-, -, rfl, -⟩, rfl, -⟩ := hk
    exact ⟨rfl, one _ hfr⟩
  | thmDecl cv value =>
    obtain ⟨-, type', value', ⟨hfr, -, -, -, rfl, -⟩, -, -, rfl⟩ := hk
    exact ⟨rfl, one _ hfr⟩
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', ⟨hfr, -, -, -, rfl, -⟩, -, rfl, -⟩ := hk
    exact ⟨rfl, one _ hfr⟩
  | axiomDecl cv =>
    rcases hk with ⟨hqs, -, -, hfr, rfl⟩ | ⟨hqs, type', -, ⟨hfr, -, -, -, rfl, -⟩, hb⟩
    · simp only [ConLeche.declConstants, ConLeche.declTables, ite_eq_left hqs]
      exact ⟨rfl, one _ hfr⟩
    · simp only [ConLeche.declConstants, ConLeche.declTables, ite_eq_right hqs]
      by_cases ht : cv.name = ConLeche.sorryAxName
      · rw [ite_eq_left ht]
        rcases hb with ⟨hs, -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
        · rw [stdAxiomOk_sorryAx env ht] at hs; exact nomatch hs
        · rw [ht] at ht'; exact absurd ht' (by decide)
        · rw [ht] at ht'; exact absurd ht' (by decide)
        · exact ⟨by simp [ConLeche.Env.pushDelta], fun _ hc => nomatch hc⟩
      · rw [ite_eq_right ht]
        rcases hb with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, ht', -⟩
        · exact ⟨rfl, one _ hfr⟩
        · exact ⟨rfl, one _ hfr⟩
        · exact ⟨rfl, one _ hfr⟩
        · exact absurd ht' ht
  | quotDecl k cv =>
    obtain ⟨-, -, hfr, rfl⟩ := hk
    exact ⟨rfl, one _ hfr⟩
  | indDecl block nP =>
    have hk' : ConLeche.Semantics.DeclIndRunDispatchK F env block nP env₂ := hk
    unfold ConLeche.Semantics.DeclIndRunDispatchK at hk'
    simp only [ConLeche.declConstants, ConLeche.declTables]
    cases hdf : ConLeche.readBlock nP block with
    | error _ => rw [hdf] at hk'; exact hk'.elim
    | ok p =>
      rw [hdf] at hk'
      have hd := ConLeche.readBlock_declared hdf
      refine ⟨ConLeche.Semantics.blockRun_env hd hk', fun c hc => ?_⟩
      exact ConLeche.Model.blockRun_fresh hd hk' c.name (List.mem_map_of_mem hc)

/-- **What the pure fold stores**: every declaration of the run was accepted at some environment,
and each constant it installs under a name it installs once is the constant the returned
environment finds at that name; a constant found before the run is found after it. -/
theorem foldlM_checkDecl_find? {F : Nat} {pins : List ConLeche.NatOpPinSet} :
    ∀ (ds : List ConLeche.Declaration) {env env' : ConLeche.Env},
      ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) env = .ok env' →
      (∀ n c, env.find? n = some c → env'.find? n = some c) ∧
      ∀ d ∈ ds, (∃ e e', ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e d = .ok e') ∧
        (((ConLeche.declConstants d).map (·.name)).Nodup →
          ∀ c ∈ ConLeche.declConstants d, env'.find? c.name = some c)
  | [], env, env', h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ _ h => h, fun _ hd => nomatch hd⟩
  | d :: ds, env, env', h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env₁ =>
      rw [hd] at h
      obtain ⟨hmono, hrest⟩ := foldlM_checkDecl_find? ds h
      obtain ⟨rfl, hfr⟩ := checkDecl_pushes hd
      refine ⟨fun n c hc => hmono n c (find?_pushDelta_old hfr hc), fun d' hd' => ?_⟩
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨⟨_, _, hd⟩, fun hnd c hc => hmono _ _ (find?_pushDelta_new hnd hc)⟩
      · exact hrest d' hd'

/-- **What con-leche's pure fold stores**, from the empty environment
(`CL ConLeche/Kernel/CheckDecl.lean:178 checkDeclsPure`). The pure-fold analogue of
`CL ConLeche/Model/StreamConsts.lean:220 checkDecls_consts`, for every constant a declaration
installs, an inductive block's included. -/
theorem checkDeclsPure_find? {F : Nat} {pins : List ConLeche.NatOpPinSet}
    {ds : List ConLeche.Declaration} {env : ConLeche.Env}
    (h : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins ds = .ok env)
    {d : ConLeche.Declaration} (hd : d ∈ ds) :
    (∃ e e', ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e d = .ok e') ∧
      (((ConLeche.declConstants d).map (·.name)).Nodup →
        ∀ c ∈ ConLeche.declConstants d, env.find? c.name = some c) :=
  (foldlM_checkDecl_find? ds h).2 d hd

/-! ## The program's declarations -/

/-- `mapM` in `Option` succeeds with the list of the images. -/
theorem mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.map f = l'.map some
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some bs =>
        simp only [hb, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [hb, mapM_eq_some hl]

/-- The records of every constant of `P` are among `DeclsOf? P`'s. -/
theorem DeclsOf?.mem {P : List ConstantInfo} {ds : List ConLeche.Declaration}
    (h : DeclsOf? P = some ds) {ci : ConstantInfo} (hci : ci ∈ P) :
    ∃ L, declOf? P ci = some L ∧ ∀ d ∈ L, d ∈ ds := by
  unfold DeclsOf? at h
  split at h
  · obtain ⟨Ls, hLs, rfl⟩ := Option.map_eq_some_iff.mp h
    have hm : declOf? P ci ∈ Ls.map some :=
      mapM_eq_some hLs ▸ List.mem_map_of_mem (List.mem_reverse.mpr hci)
    obtain ⟨L, hL, he⟩ := List.mem_map.mp hm
    exact ⟨L, he.symm, fun d hd => List.mem_flatten.mpr ⟨L, hL, hd⟩⟩
  · exact nomatch h

/-- What `cvOf?` reads. -/
theorem cvOf?_eq_some {v : Lean.ConstantVal} {cv : ConLeche.ConstantVal} (h : cvOf? v = some cv) :
    ∃ ty, toCL? v.type = some ty ∧ cv = ⟨Name.toCL v.name, v.levelParams.map Name.toCL, ty⟩ := by
  unfold cvOf? at h
  cases ht : toCL? v.type with
  | none => simp [ht] at h
  | some ty =>
    simp only [ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    exact ⟨ty, rfl, h.symm⟩

/-- **A declaration of `P` that `DeclsOf?` translates into one record is stored by con-leche's
fold**: the record's run was accepted at some environment, and the constants it installs under
distinct names are what `env` finds at their names. -/
theorem ConLecheAccepts.stored {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {ci : ConstantInfo} (hci : ci ∈ P) {d : ConLeche.Declaration}
    (hd : declOf? P ci = some [d]) :
    (∃ e e', ConLeche.checkDecl .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
        e d = .ok e') ∧
      (((ConLeche.declConstants d).map (·.name)).Nodup →
        ∀ c ∈ ConLeche.declConstants d, env.find? c.name = some c) := by
  obtain ⟨ds, hds, hf, -⟩ := h
  obtain ⟨L, hL, hLds⟩ := DeclsOf?.mem hds hci
  rw [hd, Option.some.injEq] at hL
  exact checkDeclsPure_find? hf (hLds d (hL ▸ List.mem_singleton_self d))

/-- A record that installs one constant: the constant is found at its name. -/
theorem find?_of_single {env : ConLeche.Env} {d : ConLeche.Declaration} {x : ConLeche.ConstantInfo}
    (hdc : ConLeche.declConstants d = [x])
    (hst : ((ConLeche.declConstants d).map (·.name)).Nodup →
      ∀ c ∈ ConLeche.declConstants d, env.find? c.name = some c) :
    env.find? x.name = some x :=
  hst (by rw [hdc]; simp) x (by rw [hdc]; exact List.mem_singleton_self x)

/-- The constant `findDecl` returns is a constant of the list, of that name. -/
theorem findDecl_mem {P : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (h : findDecl P c = some ci) : ci ∈ P ∧ ci.name = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- **A safe definition of `P` is stored as declared**: under its translated name, with its
translated level parameters and type, its translated value and its hint
(`CL ConLeche/Kernel/Checker.lean:34 checkDefnVal` stores the checked record). An unsafe or
partial definition is not translated (`declOf?`) and has no record. Reference: the declared body
`cst_body` that `MR P/PCUICWcbvEval.v:247 eval_delta` unfolds. -/
theorem ConLecheAccepts.find?_defn {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : DefinitionVal}
    (hv : findDecl P c = some (.defnInfo v)) (hs : v.safety = .safe) :
    ∃ cv value, cvOf? v.toConstantVal = some cv ∧ toCL? v.value = some value ∧
      env.find? (Name.toCL c) = some (.defnInfo cv value (hintOf v.hints)) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hs, hcv] at hL
  | some cv =>
  cases hval : toCL? v.value with
  | none => simp [declOf?, hs, hcv, hval] at hL
  | some value =>
  have hd : declOf? P (.defnInfo v) = some [.defnDecl cv value (hintOf v.hints)] := by
    simp [declOf?, hs, hcv, hval]
  obtain ⟨-, hst⟩ := h.stored hmem hd
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, value, rfl, rfl, ?_⟩
  rw [← hn]
  exact find?_of_single rfl hst

/-- **A theorem of `P` is stored by its statement only**: under its translated name, with its
translated level parameters and type, and no value (`CL ConLeche/Kernel/Checker.lean:59
checkThmVal` checks the translated value against the type and discards it; con-leche never
unfolds a theorem, DV-24). -/
theorem ConLecheAccepts.find?_thm {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : TheoremVal}
    (hv : findDecl P c = some (.thmInfo v)) :
    ∃ cv, cvOf? v.toConstantVal = some cv ∧ (toCL? v.value).isSome ∧
      env.find? (Name.toCL c) = some (.thmInfo cv) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hcv] at hL
  | some cv =>
  cases hval : toCL? v.value with
  | none => simp [declOf?, hcv, hval] at hL
  | some value =>
  have hd : declOf? P (.thmInfo v) = some [.thmDecl cv value] := by simp [declOf?, hcv, hval]
  obtain ⟨-, hst⟩ := h.stored hmem hd
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, rfl, rfl, ?_⟩
  rw [← hn]
  exact find?_of_single rfl hst

/-- **A safe opaque of `P` is stored as an axiom** of its translated name, level parameters and
type (`CL ConLeche/Kernel/Checker.lean:89 checkOpaqueVal`: the value is checked and discarded;
DV-10). -/
theorem ConLecheAccepts.find?_opaque {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : OpaqueVal}
    (hv : findDecl P c = some (.opaqueInfo v)) (hs : v.isUnsafe = false) :
    ∃ cv, cvOf? v.toConstantVal = some cv ∧ (toCL? v.value).isSome ∧
      env.find? (Name.toCL c) = some (.axiomInfo cv) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hs, hcv] at hL
  | some cv =>
  cases hval : toCL? v.value with
  | none => simp [declOf?, hs, hcv, hval] at hL
  | some value =>
  have hd : declOf? P (.opaqueInfo v) = some [.opaqueDecl cv value] := by
    simp [declOf?, hs, hcv, hval]
  obtain ⟨-, hst⟩ := h.stored hmem hd
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, rfl, rfl, ?_⟩
  rw [← hn]
  exact find?_of_single rfl hst

/-- The quotient package's `Quot.sound` record, matched to its pin, stores itself
(`CL ConLeche/Kernel/Basis.lean:169 quotAt`, `:175 quotPinHit`). -/
theorem quotAt_sound {cv : ConLeche.ConstantVal} (h : ConLeche.quotPinHit .sound cv = true) :
    ConLeche.quotAt .sound cv = .axiomInfo cv := by
  simp only [ConLeche.quotPinHit, Bool.and_eq_true] at h
  have he := ConLeche.ConstantVal.eq_of_beqP h.2
  show ConLeche.ConstantInfo.axiomInfo
    ((ConLeche.quotPin .sound).toConstantVal.atLps cv.levelParams) = _
  rw [← he]

/-- **A safe axiom of `P` other than `sorryAx` is stored as declared**, an axiom of its
translated name, level parameters and type; `Quot.sound` too, the quotient package's record
(`CL ConLeche/Kernel/CheckDecl.lean:112`). `sorryAx` is checked and stored as nothing
(`CL ConLeche/Kernel/CheckDecl.lean:140`): no constant of the name is stored. -/
theorem ConLecheAccepts.find?_axiom {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : AxiomVal}
    (hv : findDecl P c = some (.axiomInfo v)) (hs : v.isUnsafe = false)
    (hsorry : Name.toCL c ≠ ConLeche.sorryAxName) :
    ∃ cv, cvOf? v.toConstantVal = some cv ∧ env.find? (Name.toCL c) = some (.axiomInfo cv) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hs, hcv] at hL
  | some cv =>
  have hd : declOf? P (.axiomInfo v) = some [.axiomDecl cv] := by simp [declOf?, hs, hcv]
  obtain ⟨⟨e, e', hrun⟩, hst⟩ := h.stored hmem hd
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, rfl, ?_⟩
  rw [← hn]
  have hn' : Name.toCL v.name ≠ ConLeche.sorryAxName := by rw [← hn] at hsorry; exact hsorry
  by_cases hq : Name.toCL v.name = ConLeche.quotSoundName
  · obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
    rcases hk with ⟨-, hpin, -⟩ | ⟨hq', -⟩
    · have := find?_of_single (by simp only [ConLeche.declConstants]; exact ite_eq_left hq) hst
      rwa [quotAt_sound hpin] at this
    · exact absurd hq hq'
  · exact find?_of_single (by
      simp only [ConLeche.declConstants]; rw [ite_eq_right hq, ite_eq_right hn']) hst

/-! ## Inductive blocks -/

/-- A name some constant of `env` carries is not unbound in it. -/
theorem find?_ne_none {env : ConLeche.Env} {c : ConLeche.ConstantInfo} (hc : c ∈ env.consts)
    {n : ConLeche.Name} (hn : c.name = n) : env.find? n ≠ none := fun h =>
  absurd (List.find?_eq_none.mp h c hc) (by simp [hn])

/-- The recursor stage's first check passed: the block's recursors have distinct names
(`CL ConLeche/Kernel/Inductives/RecCheck.lean:340 targetRecPins`). -/
theorem genRecCheck_recs_nodup {F : Nat} {fe : ConLeche.FEnv} {p : ConLeche.BlockShape}
    {nb : Bool} {params : List ConLeche.Expr} {tbl : List ConLeche.NestCtorNf}
    {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor} {block : List ConLeche.ConstantInfo}
    {out : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)}
    (h : ConLeche.genRecCheck (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) fe p nb
      params tbl rd Ms block = .ok out) : (p.recs.map (·.cvR.name)).Nodup := by
  have hp : ConLeche.targetRecPins (m := ConLeche.CheckM) p block = .ok () := by
    unfold ConLeche.genRecCheck at h
    cases ht : ConLeche.targetRecPins (m := ConLeche.CheckM) p block with
    | error e => simp [ht, bind, Except.bind] at h
    | ok u => rfl
  obtain ⟨h1, h2, h3, -⟩ := ConLeche.targetRecPins_inv hp
  unfold ConLeche.targetRecPins at hp
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, h1, h2, h3,
    ↓reduceIte] at hp
  split at hp
  · split at hp
    · assumption
    · simp at hp
  · simp at hp

/-- **An accepted block installs its constants under distinct names**: the formers' and the
constructors' distinct-name guards, the recursors' (`genRecCheck_recs_nodup`), and the freshness
of the constructors at the formers' environment and of the recursors at the constructors'
(the stages `CL ConLeche/Model/Inductives/BlockRunFacts.lean:62 blockRun_fresh` reads). -/
theorem blockRun_nodup {F : Nat} {env env₂ : ConLeche.Env} {block : List ConLeche.ConstantInfo}
    {p : ConLeche.BlockShape} (hd : ∀ m ∈ p.members, m.declared = m.cvT)
    (h : ConLeche.Semantics.BlockRun F env block p env₂) :
    ((ConLeche.blockConstants p).map (·.name)).Nodup := by
  obtain ⟨ms, hms, -, -, hR⟩ := h
  obtain ⟨hndC, hndM, _, isRec, env₁, p₁, _, _, _, _, _, _, _, _, _, _, outR, _, hInd, hCtors,
    _, _, _, _, _, _, hRec, _⟩ := hR
  obtain ⟨_, _, _, s0, _, _, hq, hcons, _⟩ := ConLeche.checkBlockInds_shape hInd
  obtain ⟨-, hdecl, hname, -, hctors⟩ := ConLeche.reduceMembers_inv hd hms
  have hRec' : ConLeche.genRecCheck (ConLeche.fueledOps .verified F)
      (ConLeche.mkFEnv (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁)) p₁ _ _ _ _ _ block
      = .ok outR := hRec
  have hmem₁ : p₁.members = ms := by rw [hq]; rfl
  have hrecs₁ : p₁.recs = p.recs := by rw [hq]; rfl
  have hE := ConLeche.Model.consBlockCtors_consts p₁.nP p₁.ctorGroups env₁
  have hcs : ∀ c ∈ p.allCtors, ∃ m ∈ ms, c ∈ m.ctors := fun c hc => by
    obtain ⟨L, hL, hcL⟩ := List.mem_flatten.mp hc
    rw [← hctors] at hL
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hL
    exact ⟨m, hm, hcL⟩
  -- the formers are in the formers' environment, and so in the constructors'
  have hF : ∀ m ∈ p.members, ∃ c ∈ env₁.consts, c.name = m.declared.name := fun m hm => by
    have : m.declared ∈ (ms.map (·.declared)).zipIdx.map Prod.fst := by
      rw [List.zipIdx_map_fst, hdecl]; exact List.mem_map_of_mem hm
    obtain ⟨x, hx, hx1⟩ := List.mem_map.mp this
    rw [hcons, ConLeche.consBlockInds_consts']
    exact ⟨_, List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map_of_mem hx)),
      by rw [← hx1]; rfl⟩
  -- the constructors are fresh at the formers' environment and stored in their own
  have hCf : ∀ c ∈ p.allCtors, env₁.find? c.1.name = none := fun c hc => by
    obtain ⟨m, hm, hcm⟩ := hcs c hc
    exact ConLeche.checkBlockCtors_fresh hCtors _ (hmem₁ ▸ List.mem_map_of_mem hm) c hcm
  have hCs : ∀ c ∈ p.allCtors, ∃ c' ∈ (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁).consts,
      c'.name = c.1.name := fun c hc => by
    obtain ⟨m, hm, hcm⟩ := hcs c hc
    have hg : (m.cvT.name, m.ctors) ∈ p₁.ctorGroups := by
      show _ ∈ p₁.members.map _
      rw [hmem₁]; exact List.mem_map_of_mem (f := fun ms => (ms.cvT.name, ms.ctors)) hm
    rw [hE]
    exact ⟨.ctorInfo c.1 _ c.2 m.cvT.name, List.mem_append_left _
      (List.mem_reverse.mpr (List.mem_flatMap.mpr ⟨_, hg, List.mem_map_of_mem hcm⟩)), rfl⟩
  -- the recursors are fresh at the constructors' environment
  have hRf : ∀ rc ∈ p.recs,
      (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁).find? rc.cvR.name = none := fun rc hrc => by
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (hrecs₁ ▸ hrc)
    obtain ⟨hlen, hcv⟩ := ConLeche.Cached.genRecCheck_outCv hRec'
    have hil : i < outR.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    have hn' : outR[i].1.name = rc.cvR.name := by
      rw [hcv i rc _ hi (List.getElem?_eq_getElem hil)]
    rw [← hn']
    exact ConLeche.genRecCheck_out_fresh hRec' _ (List.getElem_mem hil)
  rw [ConLeche.Cached.blockConstants_names, List.nodup_append, List.nodup_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have e : p.members.map (·.declared.name) = p.members.map (·.cvT.name) :=
      List.map_congr_left fun m hm => by rw [hd m hm]
    rw [e, ← hname]; exact hndM
  · have e : ({ p with members := ms } : ConLeche.BlockShape).allCtors = p.allCtors := by
      show (ms.map (·.ctors)).flatten = (p.members.map (·.ctors)).flatten
      rw [hctors]
    rw [← e]; exact hndC
  · intro a ha b hb hab
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    obtain ⟨c', hc', hn⟩ := hF m hm
    exact find?_ne_none hc' (hn.trans hab) (hCf c hc)
  · rw [← hrecs₁]; exact genRecCheck_recs_nodup hRec'
  · intro a ha b hb hab
    obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hb
    have hfr := hRf rc hrc
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c', hc', hn⟩ := hF m hm
      exact find?_ne_none (hE ▸ List.mem_append_right _ hc') (hn.trans hab) hfr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c', hc', hn⟩ := hCs c hc
      exact find?_ne_none hc' (hn.trans hab) hfr

/-- What a block's split reads: each constructor record, and each recursor record, of the block
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:227 blockSplitRecs`); a block whose tail is its
recursors has no constructor or former there. -/
theorem blockSplitRecs_mem :
    ∀ {block : List ConLeche.ConstantInfo}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplitRecs block = some rs →
      (∀ {cv mI rP isK rules}, ConLeche.ConstantInfo.recInfo cv mI rP isK rules ∈ block →
        (cv, mI, rP, isK, rules) ∈ rs) ∧
      (∀ {cv nP nF T}, ConLeche.ConstantInfo.ctorInfo cv nP nF T ∉ block) ∧
      (∀ {cv caps}, ConLeche.ConstantInfo.indInfo cv caps ∉ block)
  | [], _, _ => ⟨fun hx => (nomatch hx), fun hx => (nomatch hx), fun hx => (nomatch hx)⟩
  | .recInfo cvR mI rP isK rules :: rest, rs, h => by
    simp only [ConLeche.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    obtain ⟨hr, hc, hi⟩ := blockSplitRecs_mem h'
    refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hr hx')
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hc hx'
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hi hx'
  | .axiomInfo .. :: _, _, h | .defnInfo .. :: _, _, h | .thmInfo .. :: _, _, h
  | .indInfo .. :: _, _, h | .ctorInfo .. :: _, _, h => nomatch h

/-- What a block's split reads past its formers
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:235 blockSplitCtors`). -/
theorem blockSplitCtors_mem :
    ∀ {block : List ConLeche.ConstantInfo} {cs : List (ConLeche.ConstantVal × Nat × Nat)}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplitCtors block = some (cs, rs) →
      (∀ {cv mI rP isK rules}, ConLeche.ConstantInfo.recInfo cv mI rP isK rules ∈ block →
        (cv, mI, rP, isK, rules) ∈ rs) ∧
      (∀ {cv nP nF T}, ConLeche.ConstantInfo.ctorInfo cv nP nF T ∈ block → (cv, nP, nF) ∈ cs) ∧
      (∀ {cv caps}, ConLeche.ConstantInfo.indInfo cv caps ∉ block)
  | .ctorInfo cvC nP nF T :: rest, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hr, hc, hi⟩ := blockSplitCtors_mem h'
    refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hr hx'
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hc hx')
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hi hx'
  | [], cs, rs, h | .recInfo .. :: _, cs, rs, h | .axiomInfo .. :: _, cs, rs, h
  | .defnInfo .. :: _, cs, rs, h | .thmInfo .. :: _, cs, rs, h | .indInfo .. :: _, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors] at h
    obtain ⟨rs', h', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨hr, hc, hi⟩ := blockSplitRecs_mem h'
    exact ⟨hr, fun hx => absurd hx hc, hi⟩

/-- What a block's split reads: its formers in order, each constructor record and each recursor
record (`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_mem :
    ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
      {cs : List (ConLeche.ConstantVal × Nat × Nat)}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplit block = some (cvTs, cs, rs) →
      (∀ {cv mI rP isK rules}, ConLeche.ConstantInfo.recInfo cv mI rP isK rules ∈ block →
        (cv, mI, rP, isK, rules) ∈ rs) ∧
      (∀ {cv nP nF T}, ConLeche.ConstantInfo.ctorInfo cv nP nF T ∈ block → (cv, nP, nF) ∈ cs) ∧
      (∀ {cv caps rest}, block = .indInfo cv caps :: rest →
        (∀ {cv' caps'}, ConLeche.ConstantInfo.indInfo cv' caps' ∉ rest) → cvTs = [cv])
  | .indInfo cvT caps :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hr, hc, -⟩ := blockSplit_mem h'
    refine ⟨fun hx => ?_, fun hx => ?_, fun hb hno => ?_⟩
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hr hx'
    · rcases List.mem_cons.mp hx with he | hx'
      · cases he
      · exact hc hx'
    · simp only [List.cons.injEq, ConLeche.ConstantInfo.indInfo.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      cases rest with
      | nil =>
        simp only [ConLeche.blockSplit, ConLeche.blockSplitCtors, ConLeche.blockSplitRecs,
          Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
        first | rw [← h'.1] | rw [h'.1]
      | cons x rest' =>
        cases x <;> first
          | exact absurd List.mem_cons_self hno
          | (simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h'
             obtain ⟨_, -, he⟩ := h'
             simp only [Prod.mk.injEq] at he
             rw [← he.1])
  | [], cvTs, cs, rs, h | .recInfo .. :: _, cvTs, cs, rs, h | .axiomInfo .. :: _, cvTs, cs, rs, h
  | .defnInfo .. :: _, cvTs, cs, rs, h | .thmInfo .. :: _, cvTs, cs, rs, h
  | .ctorInfo .. :: _, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hr, hc, -⟩ := blockSplitCtors_mem h'
    exact ⟨hr, hc, fun hb => nomatch hb⟩

/-- **A block's recursor is installed as its record**, its rules at one install-computed firing
mode (`CL ConLeche/Kernel/Install.lean:58 blockRecs`, `:44 recFire`): the stored type, sums, K
flag and rules (constructor, field count, right-hand side) are the record's. -/
theorem readBlock_rec_mem {nP : Nat} {block : List ConLeche.ConstantInfo} {p : ConLeche.BlockShape}
    (h : ConLeche.readBlock nP block = .ok p) {cv : ConLeche.ConstantVal} {mI rP : Nat} {isK : Bool}
    {rules : List ConLeche.RecRule} (hx : .recInfo cv mI rP isK rules ∈ block) :
    ∃ f, .recInfo cv mI rP isK (rules.map fun rl => { rl with fire := f }) ∈
      ConLeche.blockConstants p := by
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, -, hsp, -, -, -, -, -, -, hrecs⟩ :=
    ConLeche.readBlock_inv h
  have hrs := (blockSplit_mem hsp).1 hx
  have hmem : ∀ (l : List ConLeche.RecShape) rc, rc ∈ l →
      .recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map fun rl => { rl with fire := ConLeche.recFire p rc })
        ∈ ConLeche.blockRecs p l := by
    intro l rc hrc
    induction l with
    | nil => exact nomatch hrc
    | cons a l ih =>
      rcases List.mem_cons.mp hrc with rfl | hrc'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hrc')
  refine ⟨_, List.mem_append_right _ (hmem p.recs
    (⟨cv, rP, mI, ConLeche.recTargetOf p.memberNames mI cv.type, rules, isK⟩ : ConLeche.RecShape) ?_)⟩
  rw [hrecs]
  exact List.mem_map_of_mem hrs

/-- What `recOf?` writes: a recursor record of the translated name, level parameters and type,
the two sums, the K flag and the translated rules. -/
theorem recOf?_eq_some {r : RecursorVal} {x : ConLeche.ConstantInfo} (h : recOf? r = some x) :
    ∃ cv rules, cvOf? r.toConstantVal = some cv ∧ r.rules.mapM ruleOf? = some rules ∧
      x = .recInfo cv (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        (r.numParams + r.numMotives + r.numMinors) r.k rules := by
  unfold recOf? at h
  cases hcv : cvOf? r.toConstantVal <;> cases hrs : r.rules.mapM ruleOf? <;>
    simp [hcv, hrs] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- **The records `blockOf?` writes for the block headed by `H`**: the block's recursors'
records. -/
theorem blockOf?_records {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) :
    ∃ block, d = .indDecl block H.numParams ∧
      ∀ {r : RecursorVal}, .recInfo r ∈ P → r.all = H.all → ∃ x, recOf? r = some x ∧ x ∈ block := by
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, -, -, types, htypes, ctors, hctors, recs, hrecs, rfl⟩ := h
  refine ⟨_, rfl, fun {r} hr hall => ?_⟩
  have hm := mapM_eq_some hrecs ▸ List.mem_map_of_mem (f := recOf?)
    (List.mem_filterMap.mpr ⟨_, List.mem_reverse.mpr hr, (by simp [hall] : _ = some r)⟩)
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  exact ⟨x, he.symm, List.mem_append_right _ hx⟩

/-- **The block of `P` headed by `H` is stored by con-leche's fold**: con-leche reads it
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:401 readBlock`) and every constant it installs
(`CL ConLeche/Kernel/Install.lean:78 blockConstants`) is the constant `env` finds at its name. -/
theorem ConLecheAccepts.block {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} {H : InductiveVal}
    (hH : findDecl P n = some (.inductInfo H)) (hhead : H.all.head? = some n)
    (hs : H.isUnsafe = false) :
    ∃ block p, blockOf? P H = some (.indDecl block H.numParams) ∧
      ConLeche.readBlock H.numParams block = .ok p ∧
      ∀ c ∈ ConLeche.blockConstants p, env.find? c.name = some c := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hH
  have hhn : H.all.head? = some H.name := by rw [← hn] at hhead; exact hhead
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hb : blockOf? P H with
  | none => simp [declOf?, hs, hhn, hb] at hL
  | some d =>
  obtain ⟨block, rfl, -⟩ := blockOf?_records hb
  have hd : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, hs, hhn, hb]
  obtain ⟨⟨e, e', hrun⟩, hst⟩ := h.stored hmem hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hk' : ConLeche.Semantics.DeclIndRunDispatchK _ e block H.numParams e' := hk
  unfold ConLeche.Semantics.DeclIndRunDispatchK at hk'
  cases hdf : ConLeche.readBlock H.numParams block with
  | error _ => rw [hdf] at hk'; exact hk'.elim
  | ok p =>
    rw [hdf] at hk'
    have hdc : ConLeche.declConstants (.indDecl block H.numParams) = ConLeche.blockConstants p := by
      simp [ConLeche.declConstants, hdf]
    rw [hdc] at hst
    exact ⟨block, p, rfl, hdf, hst (blockRun_nodup (ConLeche.readBlock_declared hdf) hk')⟩

/-- **A recursor of a block of `P` is stored as its record**: under its translated name, with its
translated level parameters and type, its two sums, its K flag and its translated rules in order
(constructor, field count, right-hand side), each at the one firing mode the install computes
(`CL ConLeche/Kernel/Install.lean:44 recFire`); con-leche compares the record with the recursor it
generates (`CL ConLeche/Kernel/Inductives/StreamRecs.lean:187 streamRecsCheck`) and stores the
record's type and rules (`CL ConLeche/Verify/Inductives/StreamRecsInv.lean:24 streamRecs`). The
block is the one headed by `H`, a safe inductive of `P` first in its `all`. Reference: the rules
`MR P/PCUICWcbvEval.v:253 eval_iota` reads. -/
theorem ConLecheAccepts.find?_rec {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} {H : InductiveVal}
    (hH : findDecl P n = some (.inductInfo H)) (hhead : H.all.head? = some n)
    (hs : H.isUnsafe = false) {r : RecursorVal} (hr : .recInfo r ∈ P) (hall : r.all = H.all) :
    ∃ cv rules f, cvOf? r.toConstantVal = some cv ∧ r.rules.mapM ruleOf? = some rules ∧
      env.find? (Name.toCL r.name) = some (.recInfo cv
        (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        (r.numParams + r.numMotives + r.numMinors) r.k (rules.map fun rl => { rl with fire := f })) := by
  obtain ⟨block, p, hb, hdf, hst⟩ := h.block hH hhead hs
  obtain ⟨_, hbe, hrecs⟩ := blockOf?_records hb
  cases hbe
  obtain ⟨x, hx, hxb⟩ := hrecs hr hall
  obtain ⟨cv, rules, hcv, hrules, rfl⟩ := recOf?_eq_some hx
  obtain ⟨f, hf⟩ := readBlock_rec_mem hdf hxb
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  exact ⟨_, rules, f, hcv, hrules, hst _ hf⟩

end EraseProof
