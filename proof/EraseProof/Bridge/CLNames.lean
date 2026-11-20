import EraseProof.Bridge.CLStore
import EraseProof.Bridge.CLRead
import ConLeche.Semantics.DeclWF
import ConLeche.Verify.Rules.Bridge

/-!
# The names con-leche's acceptance binds

From `ConLecheAccepts P env`: a constant con-leche stores is a constant of `P`
(`ConLecheAccepts.known`); the constants of a term con-leche types are constants of `P`
(`CLTyped.knownIn`); and every declaration of `P` that the fragment test scans (one that
`Erasure.declExclusion` accepts, or a recursor) reads only constants of `P`: the constants of its
type and of its value, which con-leche checked resolve (`CL ConLeche/Kernel/CheckerBase.lean:104
checkConstantVal`, `CL ConLeche/Kernel/Checker.lean:34 checkDefnVal`, `:89 checkOpaqueVal`), and
the block members, constructors, inductive and recursor names of its Lean record, which
`DeclsOf?` checks (`ConLecheAccepts.namesClosed`).
-/

open Lean Erasure

namespace EraseProof

/-! ## Resolution of the constants of an inferred term -/

/-- Every constant, projection structure and literal support constant of a con-leche term is
stored in `env`: con-leche's `CL ConLeche/Kernel/CoreDefs.lean:211 Expr.constsResolve` without
reading the types of free variables, which inference opens binders with. -/
def clResolves (env : ConLeche.Env) : ConLeche.Expr → Bool
  | .const n _ => (env.find? n).isSome
  | .lit (.natVal _) => ConLeche.natLitStored env
  | .lit (.strVal _) => ConLeche.strLitStored env
  | .app f a => clResolves env f && clResolves env a
  | .lam t b | .forallE t b => clResolves env t && clResolves env b
  | .letE t v b => clResolves env t && clResolves env v && clResolves env b
  | .proj s _ e => (env.find? s).isSome && clResolves env e
  | .bvar _ | .fvar _ _ | .sort _ => true

/-- Instantiating a bound variable keeps every constant. -/
theorem clResolves_of_instantiate1 {env : ConLeche.Env} {v : ConLeche.Expr} :
    ∀ (e : ConLeche.Expr) (k : Nat), clResolves env (e.instantiate1 v k) = true →
      clResolves env e = true := by
  intro e
  induction e with
  | bvar _ | fvar _ _ | sort _ => intro _ _; rfl
  | const _ _ | lit _ => intro _ h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b iht ihb | forallE t b iht ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t w b iht ihw ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihw k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih k h.2⟩

/-- A projection's table is a stored structure's (`CL ConLeche/Kernel/Env.lean:476 findTable?`). -/
theorem find?_of_findProj? {env : ConLeche.Env} {T : ConLeche.Name} {i : Nat}
    {entry : ConLeche.ProjEntry} (h : env.findProj? T i = some entry) :
    (env.find? T).isSome = true := by
  unfold ConLeche.Env.findProj? ConLeche.Env.findTable? at h
  by_cases hT : (env.find? T).isSome = true
  · exact hT
  · simp [hT] at h

/-- **A term con-leche infers at the full grade has its constants stored**: the full grade
visits every subterm (`CL ConLeche/Rules/Rel.lean:589 Infer`), a constant is looked up, a literal
needs its support constants, a projection its structure's table. On the pattern of
`CL ConLeche/Verify/Inductives/RecCheckScope.lean:262 infer_bvarClosed_of_full`. -/
theorem infer_clResolves {env : ConLeche.Env} :
    ∀ {g : ConLeche.Rules.Grade} {d : Nat} {e t : ConLeche.Expr},
      ConLeche.Rules.Infer env g d e t → g = .full → clResolves env e = true
  | _, _, _, _, .sort, _ => rfl
  | _, _, _, _, .fvar _, _ => rfl
  | _, _, _, _, .const hf _, _ => by simp [clResolves, hf]
  | _, _, _, _, .natLit h, _ => h
  | _, _, _, _, .strLit h, _ => h
  | _, _, _, _, .forallE hs _ hbs _, hg => by
    simp only [clResolves, Bool.and_eq_true]
    exact ⟨infer_clResolves hs hg, clResolves_of_instantiate1 _ 0 (infer_clResolves hbs hg)⟩
  | _, _, _, _, .lam hs _ hbt, hg => by
    simp only [clResolves, Bool.and_eq_true]
    exact ⟨infer_clResolves (hs hg) rfl, clResolves_of_instantiate1 _ 0 (infer_clResolves hbt hg)⟩
  | _, _, _, _, .letE hs _ hv _ hb, hg => by
    simp only [clResolves, Bool.and_eq_true]
    exact ⟨⟨infer_clResolves (hs hg) rfl, infer_clResolves (hv hg) rfl⟩,
      clResolves_of_instantiate1 _ 0 (infer_clResolves hb hg)⟩
  | _, _, _, _, .app hf _ ha _, hg => by
    simp only [clResolves, Bool.and_eq_true]
    exact ⟨infer_clResolves hf hg, infer_clResolves (ha hg) rfl⟩
  | _, _, _, _, .proj hp _ _ hfp _ _ _, hg => by
    simp only [clResolves, Bool.and_eq_true]
    exact ⟨find?_of_findProj? hfp, infer_clResolves hp hg⟩

/-- A term whose constants resolve (`CL ConLeche/Kernel/CoreDefs.lean:211 Expr.constsResolve`)
has them stored. -/
theorem clResolves_of_constsResolve {env : ConLeche.Env} :
    ∀ {e : ConLeche.Expr}, e.constsResolve env = true → clResolves env e = true := by
  intro e
  induction e with
  | bvar _ | fvar _ _ | sort _ => intro _; rfl
  | const _ _ => intro h; exact h
  | lit l => cases l <;> intro h <;> simpa [ConLeche.Expr.constsResolve, clResolves,
      ConLeche.natLitStored, ConLeche.strLitStored, Bool.and_assoc] using h
  | app f a ihf iha =>
    intro h
    simp only [ConLeche.Expr.constsResolve, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b iht ihb | forallE t b iht ihb =>
    intro h
    simp only [ConLeche.Expr.constsResolve, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t w b iht ihw ihb =>
    intro h
    simp only [ConLeche.Expr.constsResolve, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihw h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.constsResolve, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-! ## From con-leche's names to the program's -/

/-- The constants of `x`, and `Nat` if `x` has a Nat literal, are constants of `P`. -/
def KnownIn (P : List ConstantInfo) (x : Expr) : Prop :=
  ConstsIn (fun c => (findDecl P c).isSome) x ∧ (HasNatLit x = true → (findDecl P ``Nat).isSome)

/-- A Lean term whose reading has its constants stored in `env` has its constants among the
names `env` binds, `Nat` included for a Nat literal. -/
theorem constsIn_of_clResolves {env : ConLeche.Env} :
    ∀ {x : Expr} {c : ConLeche.Expr}, toCL? x = some c → clResolves env c = true →
      ConstsIn (fun n => (env.find? (Name.toCL n)).isSome) x ∧
        (HasNatLit x = true → (env.find? (Name.toCL ``Nat)).isSome)
  | .bvar _, _, _, _ | .sort _, _, _, _ | .lit (.strVal _), _, _, _ => by
    exact ⟨trivial, fun h => by simp [HasNatLit] at h⟩
  | .const n us, c, h, hr => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    exact ⟨hr, fun h => by simp [HasNatLit] at h⟩
  | .lit (.natVal _), c, h, hr => by
    simp only [toCL?, Option.some.injEq] at h
    subst h
    simp only [clResolves, ConLeche.natLitStored, Bool.and_eq_true] at hr
    exact ⟨trivial, fun _ => hr.1.1⟩
  | .app f a, c, h, hr | .lam _ f a _, c, h, hr | .forallE _ f a _, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, hf, _, ha, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨h1, h2⟩ := constsIn_of_clResolves hf hr.1
    obtain ⟨h3, h4⟩ := constsIn_of_clResolves ha hr.2
    exact ⟨⟨h1, h3⟩, fun hn => by
      simp only [HasNatLit, Bool.or_eq_true] at hn; exact hn.elim h2 h4⟩
  | .letE _ t v b _, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, ht, _, hv, _, hb, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨h1, h2⟩ := constsIn_of_clResolves ht hr.1.1
    obtain ⟨h3, h4⟩ := constsIn_of_clResolves hv hr.1.2
    obtain ⟨h5, h6⟩ := constsIn_of_clResolves hb hr.2
    exact ⟨⟨h1, h3, h5⟩, fun hn => by
      simp only [HasNatLit, Bool.or_eq_true] at hn
      exact hn.elim (fun hn => hn.elim h2 h4) h6⟩
  | .mdata _ e, c, h, hr => constsIn_of_clResolves (x := e) h hr
  | .proj s _ e, c, h, hr => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨_, hp, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨h1, h2⟩ := constsIn_of_clResolves hp hr.2
    exact ⟨⟨hr.1, h1⟩, h2⟩
  | .fvar _, _, h, _ | .mvar _, _, h, _ => nomatch h

/-! ## The fold: what each step read and installed -/

/-- `mapM` in `Option` takes every element of its output from an element of its input. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') {b : β} (hb : b ∈ l') : ∃ a ∈ l, f a = some b := by
  have : some b ∈ l.map f := by rw [mapM_eq_some h]; exact List.mem_map_of_mem hb
  obtain ⟨a, ha, he⟩ := List.mem_map.mp this
  exact ⟨a, ha, he⟩

/-- `mapM` in `Option` pairs each input with its output, in order. -/
theorem mem_zip_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.map f = l'.map some → ∀ {a b}, a ∈ l → f a = some b →
      (a, b) ∈ l.zip l'
  | [], _, _, _, _, ha, _ => nomatch ha
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | x :: l, y :: l', h, a, b, ha, hb => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hb, Option.some.injEq] at h
      rw [h.1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_of_mapM h.2 ha hb)

/-- Every record of `DeclsOf? P` is a record of one constant of `P`. -/
theorem DeclsOf?.mem_rev {P : List ConstantInfo} {ds : List ConLeche.Declaration}
    (h : DeclsOf? P = some ds) {d : ConLeche.Declaration} (hd : d ∈ ds) :
    ∃ ci ∈ P, ∃ L, declOf? P ci = some L ∧ d ∈ L := by
  unfold DeclsOf? at h
  split at h
  · obtain ⟨Ls, hLs, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨L, hL, hdL⟩ := List.mem_flatten.mp hd
    obtain ⟨ci, hci, he⟩ := mem_of_mapM hLs hL
    exact ⟨ci, List.mem_reverse.mp hci, L, he, hdL⟩
  · exact nomatch h

/-- `DeclsOf?` sees distinct names. -/
theorem DeclsOf?.nodup {P : List ConstantInfo} {ds : List ConLeche.Declaration}
    (h : DeclsOf? P = some ds) : (P.map (·.name)).Nodup := by
  unfold DeclsOf? at h
  split at h
  · rename_i hc; exact hc.1
  · exact nomatch h

/-- A constant of a list with distinct names is the one its name finds. -/
theorem findDecl_self {P : List ConstantInfo} (hnd : (P.map (·.name)).Nodup) {ci : ConstantInfo}
    (hci : ci ∈ P) : findDecl P ci.name = some ci := by
  cases hf : findDecl P ci.name with
  | none =>
    exact absurd (List.find?_eq_none.mp hf ci hci) (by simp)
  | some y =>
    obtain ⟨hy, hyn⟩ := findDecl_mem hf
    rw [eq_of_nodup_map hnd hy hci hyn]

/-- **What the pure fold read and installed**: every declaration of the run was accepted at an
environment whose names the returned environment binds, and every constant the returned
environment holds is installed by a declaration of the run (or held before it). -/
theorem foldlM_checkDecl_run {F : Nat} {pins : List ConLeche.NatOpPinSet} :
    ∀ (ds : List ConLeche.Declaration) {env env' : ConLeche.Env},
      ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) env = .ok env' →
      (∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) ∧
      (∀ d ∈ ds, ∃ e e',
        ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e d = .ok e' ∧
        ∀ n, (e.find? n).isSome = true → (env'.find? n).isSome = true) ∧
      ∀ c ∈ env'.consts, c ∈ env.consts ∨ ∃ d ∈ ds, c ∈ ConLeche.declConstants d
  | [], env, env', h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun _ hd => (nomatch hd), fun c hc => .inl hc⟩
  | d :: ds, env, env', h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env₁ =>
      rw [hd] at h
      obtain ⟨hmono, hrest, hcs⟩ := foldlM_checkDecl_run ds h
      have hfd := hd
      obtain ⟨rfl, hfr⟩ := checkDecl_pushes hd
      have hm₀ : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true := by
        intro n hn
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
        exact hmono n (by rw [find?_pushDelta_old hfr hc]; rfl)
      refine ⟨hm₀, fun d' hd' => ?_, fun c hc => ?_⟩
      · rcases List.mem_cons.mp hd' with rfl | hd'
        · exact ⟨_, _, hfd, hm₀⟩
        · exact hrest d' hd'
      · rcases hcs c hc with hc | ⟨d', hd', hc⟩
        · rcases List.mem_append.mp hc with hc | hc
          · exact .inr ⟨d, List.mem_cons_self, List.mem_reverse.mp hc⟩
          · exact .inl hc
        · exact .inr ⟨d', List.mem_cons_of_mem _ hd', hc⟩

/-- A stored constant at other level-parameter names keeps its name and reads its type renamed
(`CL ConLeche/Kernel/Basis.lean:65 ConstantInfo.atLps`). -/
theorem atLps_toConstantVal (ci : ConLeche.ConstantInfo) (ps : List ConLeche.Name) :
    (ci.atLps ps).toConstantVal = ci.toConstantVal.atLps ps := by
  cases ci <;> rfl

/-- A quotient record matched to its pin stores itself (`CL ConLeche/Kernel/Basis.lean:169
quotAt`, `:175 quotPinHit`). -/
theorem quotAt_cv {k : ConLeche.QuotKind} {cv : ConLeche.ConstantVal}
    (h : ConLeche.quotPinHit k cv = true) : (ConLeche.quotAt k cv).toConstantVal = cv := by
  simp only [ConLeche.quotPinHit, Bool.and_eq_true] at h
  rw [ConLeche.quotAt, atLps_toConstantVal]
  exact (ConLeche.ConstantVal.eq_of_beqP h.2).symm

/-- **An accepted step installs only constants its record names**
(`CL ConLeche/Kernel/Env.lean:443 Declaration.names`). -/
theorem checkDecl_names {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {d : ConLeche.Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e d = .ok e') :
    ∀ c ∈ ConLeche.declConstants d, c.name ∈ d.names := by
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  intro c hc
  cases d with
  | defnDecl cv v hint | thmDecl cv v | opaqueDecl cv v =>
    simp only [ConLeche.declConstants, List.mem_singleton] at hc
    subst hc; exact List.mem_singleton_self _
  | axiomDecl cv =>
    by_cases hq : cv.name = ConLeche.quotSoundName
    · rcases hk with ⟨-, hpin, -⟩ | ⟨hq', -⟩
      · simp only [ConLeche.declConstants, ite_eq_left hq, List.mem_singleton] at hc
        subst hc
        show (ConLeche.quotAt .sound cv).toConstantVal.name ∈ [cv.name]
        rw [quotAt_cv hpin]; exact List.mem_singleton_self _
      · exact absurd hq hq'
    · simp only [ConLeche.declConstants, ite_eq_right hq] at hc
      split at hc
      · exact nomatch hc
      · rw [List.mem_singleton.mp hc]; exact List.mem_singleton_self _
  | quotDecl k cv =>
    obtain ⟨hpin, -⟩ := hk
    simp only [ConLeche.declConstants, List.mem_singleton] at hc
    subst hc
    show (ConLeche.quotAt k cv).toConstantVal.name ∈ [cv.name]
    rw [quotAt_cv hpin]; exact List.mem_singleton_self _
  | indDecl block nP =>
    simp only [ConLeche.declConstants] at hc
    split at hc
    · rename_i p hdf
      obtain ⟨b, hb, hn⟩ := ConLeche.Model.blockConstants_names_mem hdf c.name
        (List.mem_map_of_mem hc)
      exact hn ▸ List.mem_map_of_mem hb
    · exact nomatch hc

/-- **The records `blockOf?` writes for the block headed by `H`**: each member's former and each
of its constructors, under their translated names; every record carries the translated name of a
constant of `P` that is no definition (an inductive, a constructor or a recursor). -/
theorem blockOf?_spec {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) :
    ∃ block, d = .indDecl block H.numParams ∧
      (∀ b ∈ block, ∃ ci ∈ P, b.name = Name.toCL ci.name ∧ ∀ d, ci ≠ .defnInfo d) ∧
      ∀ n ∈ H.all, ∃ t, findConst P n = some (.inductInfo t) ∧
        (∃ cv, cvOf? t.toConstantVal = some cv ∧ ConLeche.ConstantInfo.indInfo cv {} ∈ block) ∧
        ∀ cn ∈ t.ctors, ∃ c, findConst P cn = some (.ctorInfo c) ∧ ∃ cv,
          cvOf? c.toConstantVal = some cv ∧
          ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields (Name.toCL t.name) ∈ block := by
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, -, -, types, htypes, ctors, hctors, recs, hrecs, rfl⟩ := h
  have hty : ∀ t ∈ tys, .inductInfo t ∈ P := fun t ht => by
    obtain ⟨n, -, he⟩ := mem_of_mapM htys ht
    split at he
    · rename_i t' hf; cases he; exact (findDecl_mem hf).1
    · exact nomatch he
  have hcs : ∀ cs ∈ cvs, ∀ c ∈ cs, .ctorInfo c ∈ P := fun cs hcs c hc => by
    obtain ⟨t, -, he⟩ := mem_of_mapM hcvs hcs
    obtain ⟨n, -, he'⟩ := mem_of_mapM he hc
    split at he'
    · rename_i c' hf; cases he'; exact (findDecl_mem hf).1
    · exact nomatch he'
  refine ⟨_, rfl, fun b hb => ?_, fun n hn => ?_⟩
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨t, ht, he⟩ := mem_of_mapM htypes hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at he
        obtain ⟨cv, hcv, rfl⟩ := he
        obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
        exact ⟨.inductInfo t, hty t ht, rfl, fun _ => nofun⟩
      · obtain ⟨L, hL, hbL⟩ := List.mem_flatten.mp hb
        obtain ⟨⟨t, cs⟩, hz, he⟩ := mem_of_mapM hctors hL
        obtain ⟨c, hc, he'⟩ := mem_of_mapM he hbL
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at he'
        obtain ⟨cv, hcv, rfl⟩ := he'
        obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
        exact ⟨.ctorInfo c, hcs cs (List.of_mem_zip hz).2 c hc, rfl, fun _ => nofun⟩
    · obtain ⟨r, hr, he⟩ := mem_of_mapM hrecs hb
      obtain ⟨cv, rules, hcv, -, rfl⟩ := recOf?_eq_some he
      obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
      obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.mp hr
      refine ⟨x, List.mem_reverse.mp hx, ?_⟩
      cases x with
      | recInfo r' =>
        simp only at hxe
        split at hxe
        · cases hxe; exact ⟨rfl, fun _ => nofun⟩
        · exact nomatch hxe
      | _ => exact nomatch hxe
  · have hm := mapM_eq_some htys ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) hn
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    have hft : findConst P n = some (.inductInfo t) := by
      revert he; split
      · rename_i t' hf; intro he; cases he; exact hf
      · intro he; exact nomatch he
    refine ⟨t, hft, ?_, fun cn hcn => ?_⟩
    · have hm' := mapM_eq_some htypes ▸ List.mem_map_of_mem
        (f := fun (t : InductiveVal) => (cvOf? t.toConstantVal).bind fun cv =>
          some (ConLeche.ConstantInfo.indInfo cv {})) ht
      obtain ⟨b, hb, he'⟩ := List.mem_map.mp hm'
      cases hcv : cvOf? t.toConstantVal with
      | none => simp [hcv] at he'
      | some cv =>
        simp only [hcv, Option.bind_some, Option.some.injEq] at he'
        exact ⟨cv, rfl, List.mem_append_left _ (List.mem_append_left _ (he' ▸ hb))⟩
    · obtain ⟨cs, hcs', hz⟩ : ∃ cs, t.ctors.mapM (fun n => match findConst P n with
          | some (.ctorInfo c) => some c
          | _ => none) = some cs ∧ (t, cs) ∈ tys.zip cvs := by
        have hm₂ := mapM_eq_some hcvs ▸ List.mem_map_of_mem (f := fun (t : InductiveVal) =>
          t.ctors.mapM fun n => match findConst P n with
            | some (.ctorInfo c) => some c
            | _ => none) ht
        obtain ⟨cs, -, he₂⟩ := List.mem_map.mp hm₂
        exact ⟨cs, he₂.symm, mem_zip_of_mapM (mapM_eq_some hcvs) ht he₂.symm⟩
      have hm₃ := mapM_eq_some hcs' ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
        | some (.ctorInfo c) => some c
        | _ => none) hcn
      obtain ⟨c, hc, he₃⟩ := List.mem_map.mp hm₃
      have hfc : findConst P cn = some (.ctorInfo c) := by
        revert he₃; split
        · rename_i c' hf; intro he; cases he; exact hf
        · intro he; exact nomatch he
      refine ⟨c, hfc, ?_⟩
      obtain ⟨L, hL, hzL⟩ : ∃ L, cs.mapM (fun (c : ConstructorVal) =>
          (cvOf? c.toConstantVal).bind fun cv =>
            some (ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields (Name.toCL t.name)))
            = some L ∧ L ∈ ctors := by
        have hm₄ := mapM_eq_some hctors ▸ List.mem_map_of_mem
          (f := fun (x : InductiveVal × List ConstructorVal) => x.2.mapM fun (c : ConstructorVal) =>
            (cvOf? c.toConstantVal).bind fun cv =>
              some (ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields (Name.toCL x.1.name))) hz
        obtain ⟨L, hL, he₄⟩ := List.mem_map.mp hm₄
        exact ⟨L, he₄.symm, hL⟩
      have hm₅ := mapM_eq_some hL ▸ List.mem_map_of_mem (f := fun (c : ConstructorVal) =>
          (cvOf? c.toConstantVal).bind fun cv =>
            some (ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields (Name.toCL t.name))) hc
      obtain ⟨b, hb, he₅⟩ := List.mem_map.mp hm₅
      cases hcv : cvOf? c.toConstantVal with
      | none => simp [hcv] at he₅
      | some cv =>
        simp only [hcv, Option.bind_some, Option.some.injEq] at he₅
        exact ⟨cv, rfl, List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatten.mpr ⟨L, hzL, he₅ ▸ hb⟩))⟩


/-! ## Inductive blocks -/

/-- **What con-leche's recursor stage pins of a block** (`CL ConLeche/Kernel/Inductives/RecCheck.lean:340
targetRecPins`, the first check of `genRecCheck`, which the block's run records): the
constructors it groups by member have distinct names and are, by name, the block's constructor
records (a constructor no member's group holds is rejected there, "constructor grouping"); and
every member's `T.rec` is a recursor of the block (`CL ConLeche/Kernel/Inductives/BlockShape.lean:357
blockRecNameSetOk`). -/
theorem blockRun_pins {F : Nat} {env env₂ : ConLeche.Env} {block : List ConLeche.ConstantInfo}
    {p : ConLeche.BlockShape} (hd : ∀ m ∈ p.members, m.declared = m.cvT)
    (h : ConLeche.Semantics.BlockRun F env block p env₂) :
    (p.allCtors.map (·.1.name)).Nodup ∧
    (∀ {cvTs cs rs}, ConLeche.blockSplit block = some (cvTs, cs, rs) →
      p.allCtors.map (·.1.name) = cs.map (·.1.name)) ∧
    ∀ m ∈ p.members, ∃ rc ∈ p.recs, rc.cvR.name = m.declared.name.str "rec" := by
  obtain ⟨ms, hms, -, -, hR⟩ := h
  obtain ⟨hndC, -, _, isRec, env₁, p₁, _, _, _, _, _, _, _, _, _, _, outR, _, hInd, -,
    _, _, _, _, _, _, hRec, _⟩ := hR
  obtain ⟨_, _, _, s0, _, _, hq, -, _⟩ := ConLeche.checkBlockInds_shape hInd
  obtain ⟨-, -, hname, -, hctors⟩ := ConLeche.reduceMembers_inv hd hms
  have hRec' : ConLeche.genRecCheck (ConLeche.fueledOps .verified F)
      (ConLeche.mkFEnv (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁)) p₁ _ _ _ _ _ block
      = .ok outR := hRec
  have hmem₁ : p₁.members = ms := by rw [hq]; rfl
  have hrecs₁ : p₁.recs = p.recs := by rw [hq]; rfl
  have hall : p₁.allCtors = p.allCtors := by
    show (p₁.members.map (·.ctors)).flatten = (p.members.map (·.ctors)).flatten
    rw [hmem₁, hctors]
  have hp : ConLeche.targetRecPins (m := ConLeche.CheckM) p₁ block = .ok () := by
    unfold ConLeche.genRecCheck at hRec'
    cases ht : ConLeche.targetRecPins (m := ConLeche.CheckM) p₁ block with
    | error e => simp [ht, bind, Except.bind] at hRec'
    | ok u => rfl
  obtain ⟨h1, h2, h3, -⟩ := ConLeche.targetRecPins_inv hp
  refine ⟨?_, fun {cvTs cs rs} hsp => ?_, fun m hm => ?_⟩
  · have e : ({ p with members := ms } : ConLeche.BlockShape).allCtors = p.allCtors := by
      show (ms.map (·.ctors)).flatten = (p.members.map (·.ctors)).flatten
      rw [hctors]
    rw [← e]; exact hndC
  · unfold ConLeche.targetRecPins at hp
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, h1, h2,
      h3, ↓reduceIte] at hp
    split at hp
    · split at hp
      · rw [hsp] at hp
        simp only at hp
        split at hp
        · rename_i hok
          simp only [Bool.and_eq_true, beq_iff_eq] at hok
          rw [← hall]; exact hok.2
        · simp at hp
      · simp at hp
    · simp at hp
  · simp only [ConLeche.blockRecNameSetOk, Bool.and_eq_true, List.all_eq_true] at h3
    obtain ⟨⟨-, hw⟩, -⟩ := h3
    have hm' : m.cvT.name ∈ p₁.members.map (·.cvT.name) := by
      rw [hmem₁, hname]; exact List.mem_map_of_mem hm
    obtain ⟨m', hm'', he⟩ := List.mem_map.mp hm'
    have hc := hw _ (List.mem_map_of_mem (f := fun ms => ms.cvT.name.str "rec") hm'')
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter] at hc
    obtain ⟨rc, ⟨hrc, -⟩, hrn⟩ := hc
    refine ⟨rc, hrecs₁ ▸ hrc, ?_⟩
    rw [hrn, he, hd m hm]

/-- A former record of a block is one of the formers its split reads
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_former :
    ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
      {cs : List (ConLeche.ConstantVal × Nat × Nat)}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplit block = some (cvTs, cs, rs) →
      ∀ {cv caps}, ConLeche.ConstantInfo.indInfo cv caps ∈ block → cv ∈ cvTs
  | .indInfo cvT caps :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    intro hx
    rcases List.mem_cons.mp hx with he | hx'
    · cases he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (blockSplit_former h' hx')
  | [], cvTs, cs, rs, h | .recInfo .. :: _, cvTs, cs, rs, h | .axiomInfo .. :: _, cvTs, cs, rs, h
  | .defnInfo .. :: _, cvTs, cs, rs, h | .thmInfo .. :: _, cvTs, cs, rs, h
  | .ctorInfo .. :: _, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', -⟩ := Option.map_eq_some_iff.mp h
    intro hx
    exact absurd hx (blockSplitCtors_mem h').2.2

/-- **A former record of a block is installed**, at the capabilities the install computes
(`CL ConLeche/Kernel/Install.lean:27 blockFormers`), and it is a member's declared former. -/
theorem readBlock_former_mem {nP : Nat} {block : List ConLeche.ConstantInfo}
    {p : ConLeche.BlockShape} (h : ConLeche.readBlock nP block = .ok p) {cv : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} (hx : .indInfo cv caps ∈ block) :
    (∃ caps', .indInfo cv caps' ∈ ConLeche.blockConstants p) ∧
      ∃ m ∈ p.members, m.declared = cv := by
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hk, -, hnI, -, -, hmem, -⟩ :=
    ConLeche.readBlock_inv h
  have hcv := blockSplit_former hsp hx
  have hproj := (ConLeche.blockMembers_proj (cvTs := cvTs) (nIdxs := nIdxs)
    (groups := ConLeche.blockGroups p.memberNames p.lps p.nP p.k (cs.map fun c => (c.1, c.2.2)))
    (hnI.trans hk.symm) (by rw [ConLeche.blockGroups_length, hk])).1
  rw [← hmem] at hproj
  obtain ⟨m, hm, hmc⟩ := List.mem_map.mp (hproj ▸ hcv)
  have hdm : m.declared = cv := (ConLeche.readBlock_declared h m hm).trans hmc
  refine ⟨?_, m, hm, hdm⟩
  have h1 : m.declared ∈ (p.members.map (·.declared)).zipIdx.map Prod.fst := by
    rw [List.zipIdx_map_fst]; exact List.mem_map_of_mem hm
  obtain ⟨x, hx', hx1⟩ := List.mem_map.mp h1
  refine ⟨ConLeche.blockCapsAt p x.2 (ConLeche.blockIsRec p),
    List.mem_append_left _ (List.mem_append_left _ ?_)⟩
  rw [← hdm, ← hx1]
  exact List.mem_map_of_mem (f := fun (x : ConLeche.ConstantVal × Nat) =>
    ConLeche.ConstantInfo.indInfo x.1 (ConLeche.blockCapsAt p x.2 (ConLeche.blockIsRec p))) hx'

/-- **A constructor record of a block is installed**, under its member's name
(`CL ConLeche/Kernel/Install.lean:32 blockCtors`), when the block's grouped constructors are its
constructor records by name (`blockRun_pins`). -/
theorem readBlock_ctor_mem {nP : Nat} {block : List ConLeche.ConstantInfo}
    {p : ConLeche.BlockShape} (h : ConLeche.readBlock nP block = .ok p)
    (hnd : (p.allCtors.map (·.1.name)).Nodup)
    (hgr : ∀ {cvTs cs rs}, ConLeche.blockSplit block = some (cvTs, cs, rs) →
      p.allCtors.map (·.1.name) = cs.map (·.1.name))
    {cv : ConLeche.ConstantVal} {nP' nF : Nat} {T : ConLeche.Name}
    (hx : .ctorInfo cv nP' nF T ∈ block) :
    ∃ T', .ctorInfo cv p.nP nF T' ∈ ConLeche.blockConstants p := by
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, -, -, -, -, -, hmem, -⟩ :=
    ConLeche.readBlock_inv h
  have hc := (blockSplit_mem hsp).2.1 hx
  have hnames := hgr hsp
  have hin : cv.name ∈ p.allCtors.map (·.1.name) := by
    rw [hnames]; exact List.mem_map_of_mem (f := fun c => c.1.name) hc
  obtain ⟨a, ha, han⟩ := List.mem_map.mp hin
  obtain ⟨L, hL, haL⟩ := List.mem_flatten.mp ha
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hL
  have hmg : m ∈ _ := hmem ▸ hm
  obtain ⟨-, hg⟩ := ConLeche.blockMembers_mem hmg
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (ConLeche.mem_blockGroups hg haL)
  have hcc : c' = (cv, nP', nF) := eq_of_nodup_map (hnames ▸ hnd) hc' hc han
  subst hcc
  refine ⟨m.cvT.name, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
  simp only [ConLeche.blockCtors, ConLeche.BlockShape.ctorGroups]
  exact List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem (f := fun ms => (ms.cvT.name, ms.ctors)) hm,
    List.mem_map.mpr ⟨_, haL, rfl⟩⟩

/-- An inductive of `P` is safe: `DeclsOf?` declines an unsafe one. -/
theorem ConLecheAccepts.ind_safe {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {iv : InductiveVal} (hiv : .inductInfo iv ∈ P) :
    iv.isUnsafe = false := by
  obtain ⟨ds, hds, -⟩ := h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hiv
  cases hu : iv.isUnsafe with
  | false => rfl
  | true => simp [declOf?, hu] at hL

/-- **The block of `P` headed by `H` is stored with its pins**: con-leche reads it, every constant
it installs is the one `env` finds at its name, and the recursor stage's pins hold
(`blockRun_pins`). -/
theorem ConLecheAccepts.blockPins {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} {H : InductiveVal}
    (hH : findDecl P n = some (.inductInfo H)) (hhead : H.all.head? = some n) :
    ∃ block p, blockOf? P H = some (.indDecl block H.numParams) ∧
      ConLeche.readBlock H.numParams block = .ok p ∧
      (∀ c ∈ ConLeche.blockConstants p, env.find? c.name = some c) ∧
      (p.allCtors.map (·.1.name)).Nodup ∧
      (∀ {cvTs cs rs}, ConLeche.blockSplit block = some (cvTs, cs, rs) →
        p.allCtors.map (·.1.name) = cs.map (·.1.name)) ∧
      ∀ m ∈ p.members, ∃ rc ∈ p.recs, rc.cvR.name = m.declared.name.str "rec" := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hH
  have hs := h.ind_safe hmem
  obtain ⟨block, p, hb, hdf, hst⟩ := h.block hH hhead hs
  have hhn : H.all.head? = some H.name := by rw [← hn] at hhead; exact hhead
  obtain ⟨ds, hds, hf, -⟩ := id h
  have hd : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, hs, hhn, hb]
  obtain ⟨⟨e, e', hrun⟩, -⟩ := h.stored hmem hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hk' : ConLeche.Semantics.DeclIndRunDispatchK _ e block H.numParams e' := hk
  unfold ConLeche.Semantics.DeclIndRunDispatchK at hk'
  rw [hdf] at hk'
  obtain ⟨h1, h2, h3⟩ := blockRun_pins (ConLeche.readBlock_declared hdf) hk'
  exact ⟨block, p, hb, hdf, hst, h1, h2, h3⟩

/-! ## The names of the program -/

/-- `ConstsIn` is monotone in the predicate. Port of `ML-V Bridge/Basic.lean` `ConstsIn_mono`. -/
theorem ConstsIn_mono {p q : Name → Prop} (h : ∀ c, p c → q c) :
    ∀ {e : Expr}, ConstsIn p e → ConstsIn q e
  | .const c _, hc => h c hc
  | .app f a, hc => ⟨ConstsIn_mono h hc.1, ConstsIn_mono h hc.2⟩
  | .lam _ t b _, hc | .forallE _ t b _, hc => ⟨ConstsIn_mono h hc.1, ConstsIn_mono h hc.2⟩
  | .letE _ t v b _, hc => ⟨ConstsIn_mono h hc.1, ConstsIn_mono h hc.2.1, ConstsIn_mono h hc.2.2⟩
  | .mdata _ e, hc => ConstsIn_mono (e := e) h hc
  | .proj _ _ e, hc => ⟨h _ hc.1, ConstsIn_mono (e := e) h hc.2⟩
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ => trivial

/-- **The records `DeclsOf?` writes for a constant of `P` carry translated names of constants of
`P`**: of the constant itself, or of one that is no definition (a block's). -/
theorem declOf?_names {P : List ConstantInfo} {ci : ConstantInfo} (hci : ci ∈ P)
    {L : List ConLeche.Declaration} (h : declOf? P ci = some L) {d : ConLeche.Declaration}
    (hd : d ∈ L) : ∀ n ∈ d.names, ∃ ci' ∈ P, n = Name.toCL ci'.name ∧
      (ci' = ci ∨ ∀ dv, ci' ≠ .defnInfo dv) := by
  have one : ∀ {v : Lean.ConstantVal} {cv : ConLeche.ConstantVal}, v.name = ci.name →
      cvOf? v = some cv → ∀ n ∈ [cv.name], ∃ ci' ∈ P, n = Name.toCL ci'.name ∧
        (ci' = ci ∨ ∀ dv, ci' ≠ .defnInfo dv) := by
    intro v cv hv hcv n hn
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    rw [List.mem_singleton.mp hn, hv]; exact ⟨ci, hci, rfl, .inl rfl⟩
  cases ci with
  | axiomInfo v =>
    cases hu : v.isUnsafe
    · cases hcv : cvOf? v.toConstantVal with
      | none => simp [declOf?, hu, hcv] at h
      | some cv =>
        simp [declOf?, hu, hcv] at h; subst h
        rw [List.mem_singleton.mp hd]; exact one rfl hcv
    · simp [declOf?, hu] at h; subst h; exact nomatch hd
  | opaqueInfo v =>
    cases hu : v.isUnsafe
    · cases hcv : cvOf? v.toConstantVal with
      | none => simp [declOf?, hu, hcv] at h
      | some cv =>
        cases hval : toCL? v.value with
        | none => simp [declOf?, hu, hcv, hval] at h
        | some val =>
          simp [declOf?, hu, hcv, hval] at h; subst h
          rw [List.mem_singleton.mp hd]; exact one rfl hcv
    · simp [declOf?, hu] at h; subst h; exact nomatch hd
  | defnInfo v =>
    cases hs : v.safety with
    | safe =>
      cases hcv : cvOf? v.toConstantVal with
      | none => simp [declOf?, hs, hcv] at h
      | some cv =>
        cases hval : toCL? v.value with
        | none => simp [declOf?, hs, hcv, hval] at h
        | some val =>
          simp [declOf?, hs, hcv, hval] at h; subst h
          rw [List.mem_singleton.mp hd]; exact one rfl hcv
    | «unsafe» | «partial» => simp [declOf?, hs] at h; subst h; exact nomatch hd
  | thmInfo v =>
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hcv] at h
    | some cv =>
      cases hval : toCL? v.value with
      | none => simp [declOf?, hcv, hval] at h
      | some val =>
        simp [declOf?, hcv, hval] at h; subst h
        rw [List.mem_singleton.mp hd]; exact one rfl hcv
  | quotInfo v =>
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hcv] at h
    | some cv =>
      simp [declOf?, hcv] at h; subst h
      rw [List.mem_singleton.mp hd]; exact one rfl hcv
  | inductInfo v =>
    cases hu : v.isUnsafe
    · by_cases hh : v.all.head? = some v.name
      · cases hb : blockOf? P v with
        | none => simp [declOf?, hu, hh, hb] at h
        | some d' =>
          simp [declOf?, hu, hh, hb] at h; subst h
          rw [List.mem_singleton.mp hd]
          obtain ⟨block, rfl, hnm, -⟩ := blockOf?_spec hb
          intro n hn
          obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hn
          obtain ⟨ci', h1, h2, h3⟩ := hnm b hb'
          exact ⟨ci', h1, h2, .inr h3⟩
      · simp only [declOf?, hu, hh, beq_iff_eq, Bool.false_eq_true, ↓reduceIte] at h
        revert h; split
        · split
          · intro h; cases h; exact nomatch hd
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    · simp [declOf?, hu] at h
  | ctorInfo c =>
    simp only [declOf?] at h
    revert h; split
    · split
      · intro h; cases h; exact nomatch hd
      · intro h; exact nomatch h
    · intro h; exact nomatch h
  | recInfo r =>
    simp only [declOf?] at h
    revert h; split
    · split
      · intro h; cases h; exact nomatch hd
      · intro h; exact nomatch h
    · intro h; exact nomatch h

/-- **A name con-leche's accepted environment binds is a name of `P`**: every constant the fold
stores is installed by a record (`foldlM_checkDecl_run`) under a name the record declares
(`checkDecl_names`), the translated name of a constant of `P` (`declOf?_names`). -/
theorem ConLecheAccepts.known {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} (hn : (env.find? (Name.toCL n)).isSome = true) :
    (findDecl P n).isSome = true := by
  obtain ⟨ds, hds, hf, -⟩ := h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
  have hcm : c ∈ env.consts := List.mem_of_find?_eq_some hc
  have hcn : c.name = Name.toCL n := by simpa using List.find?_some hc
  obtain ⟨-, hrun, hcs⟩ := foldlM_checkDecl_run ds hf
  rcases hcs c hcm with hc0 | ⟨d, hd, hcd⟩
  · exact absurd hc0 (by simp [ConLeche.Env.empty])
  obtain ⟨e, e', hstep, -⟩ := hrun d hd
  obtain ⟨ci, hci, L, hL, hdL⟩ := DeclsOf?.mem_rev hds hd
  obtain ⟨ci', hci', he, -⟩ := declOf?_names hci hL hdL _ (checkDecl_names hstep c hcd)
  rw [hcn] at he
  rw [Name.toCL_injective he, findDecl_self (DeclsOf?.nodup hds) hci']
  rfl

/-- A term whose reading has its constants stored has its constants in `P`. -/
theorem ConLecheAccepts.knownIn {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {x : Expr} {c : ConLeche.Expr} (hx : toCL? x = some c)
    (hr : clResolves env c = true) : KnownIn P x := by
  obtain ⟨h1, h2⟩ := constsIn_of_clResolves hx hr
  exact ⟨ConstsIn_mono (fun _ hn => h.known hn) h1, fun hn => h.known (h2 hn)⟩

/-- **The constants of a term con-leche types are constants of `P`**, `Nat` included for a Nat
literal: full-grade inference resolves every constant (`infer_clResolves`, on the derivation of
`CL ConLeche/Verify/Rules/Bridge.lean:67 inferTypeCore_bridge`). Reference: none (DV-3). -/
theorem CLTyped.knownIn {P : List ConstantInfo} {env : ConLeche.Env} (h : ConLecheAccepts P env)
    {t : Expr} (ht : CLTyped env t) : KnownIn P t := by
  obtain ⟨c, F, T, hc, hi⟩ := ht
  exact h.knownIn hc (infer_clResolves (ConLeche.Rules.inferTypeCore_bridge hi) rfl)

/-! ## What a declaration of `P` reads -/

/-- The front checks of an accepted `def` (`CL ConLeche/Kernel/CheckerBase.lean:104
checkConstantVal`, `CL ConLeche/Kernel/Checker.lean:34 checkDefnVal`): its type and value resolve
at the step. -/
theorem front_defn {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr} {hint : ConLeche.ReducibilityHint}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e
      (.defnDecl cv v hint) = .ok e') :
    cv.type.constsResolve e = true ∧ v.constsResolve e = true := by
  obtain ⟨-, type', value', ⟨-, -, -, -, rfl, -, hrt, -⟩, ⟨-, -, rfl, -, hrv, -⟩, -⟩ :=
    ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  exact ⟨hrt, hrv⟩

/-- The front checks of an accepted theorem (`CL ConLeche/Kernel/Checker.lean:59 checkThmVal`). -/
theorem front_thm {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e
      (.thmDecl cv v) = .ok e') : cv.type.constsResolve e = true := by
  obtain ⟨-, -, type', value', ⟨-, -, -, -, rfl, -, hrt, -⟩, -⟩ :=
    ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  exact hrt

/-- The front checks of an accepted opaque (`CL ConLeche/Kernel/Checker.lean:89 checkOpaqueVal`):
its type and value resolve at the step, although only its type is stored. -/
theorem front_opaque {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e
      (.opaqueDecl cv v) = .ok e') :
    cv.type.constsResolve e = true ∧ v.constsResolve e = true := by
  obtain ⟨-, -, type', value', ⟨-, -, -, -, rfl, -, hrt, -⟩, ⟨-, -, rfl, -, hrv, -⟩, -⟩ :=
    ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  exact ⟨hrt, hrv⟩

/-- The front check of an accepted axiom other than `Quot.sound`, `sorryAx` included, which is
checked and stored as nothing (`CL ConLeche/Kernel/CheckDecl.lean:88`). -/
theorem front_axiom {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {cv : ConLeche.ConstantVal}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e
      (.axiomDecl cv) = .ok e') (hq : cv.name ≠ ConLeche.quotSoundName) :
    cv.type.constsResolve e = true := by
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  rcases hk with ⟨hq', -⟩ | ⟨-, type', -, ⟨-, -, -, -, rfl, -, hrt, -⟩, -⟩
  · exact absurd hq' hq
  · exact hrt

/-- The block of an inductive of `P`: the inductive heading the `all` list it shares. -/
theorem ConLecheAccepts.head {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {t : InductiveVal} (ht : .inductInfo t ∈ P) :
    ∃ Hn H, findDecl P Hn = some (.inductInfo H) ∧ H.all.head? = some Hn ∧ H.all = t.all ∧
      t.name ∈ H.all := by
  obtain ⟨ds, hds, -⟩ := id h
  have hnd := DeclsOf?.nodup hds
  have hs := h.ind_safe ht
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds ht
  by_cases hh : t.all.head? = some t.name
  · exact ⟨t.name, t, findDecl_self hnd ht, hh, rfl, List.mem_of_mem_head? hh⟩
  · simp only [declOf?, hs, hh, beq_iff_eq, Bool.false_eq_true, ↓reduceIte] at hL
    cases hb : t.all.head? with
    | none => simp [hb] at hL
    | some Hn =>
      cases hf : findConst P Hn with
      | none => simp [hb, hf] at hL
      | some x =>
        cases x with
        | inductInfo H =>
          simp only [hb, hf, Option.bind_some] at hL
          simp at hL
          obtain ⟨⟨hHall, hmem⟩, -⟩ := hL
          exact ⟨Hn, H, hf, by rw [hHall]; exact hb, hHall, hHall ▸ hmem⟩
        | _ => simp [hb, hf] at hL

/-- What the fragment test reads of a declaration of `P` (`Erasure.closureStep`): the constants of
its type, of a definition's and an opaque's value, the block members, constructors and recursor
of an inductive, the inductive of a constructor, the block of a recursor. Each is a name of `P`.
The counterpart of `ML-V Core/Collect.lean` `CollectSub.NamesClosed`. -/
structure NamesClosed (P : List ConstantInfo) (ci : ConstantInfo) : Prop where
  type : KnownIn P ci.type
  defn : ∀ d, ci = .defnInfo d → KnownIn P d.value
  opq : ∀ o, ci = .opaqueInfo o → KnownIn P o.value
  ind : ∀ iv, ci = .inductInfo iv → (∀ n ∈ iv.all, (findDecl P n).isSome = true) ∧
    (∀ n ∈ iv.ctors, (findDecl P n).isSome = true) ∧
    (findDecl P (mkRecName iv.name)).isSome = true
  ctor : ∀ cv, ci = .ctorInfo cv → (findDecl P cv.induct).isSome = true
  recr : ∀ r, ci = .recInfo r → ∀ n ∈ r.all, (findDecl P n).isSome = true

/-- **Every declaration of `P` that the fragment test may scan reads only constants of `P`**: a
safe definition, a safe axiom, a safe opaque, a theorem, a quotient, and every inductive,
constructor and recursor (`DeclsOf?` declines an unsafe inductive, so every block is checked).
The types and values are the ones con-leche resolved (`front_defn` …, or the stored constant's,
`CL ConLeche/Verify/EnvWF.lean:244 EnvWF`); the record fields are the ones `DeclsOf?` reads
(`blockOf?_spec`) and con-leche pins (`blockRun_pins`). Replaces `ML-V Core/Collect.lean`
`ProgEnv.names_closed`. -/
theorem ConLecheAccepts.namesClosed {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {ci : ConstantInfo} (hci : ci ∈ P)
    (hdef : ∀ d, ci = .defnInfo d → d.safety = .safe)
    (hax : ∀ a, ci = .axiomInfo a → a.isUnsafe = false)
    (hop : ∀ o, ci = .opaqueInfo o → o.isUnsafe = false) : NamesClosed P ci := by
  obtain ⟨ds, hds, hf, -⟩ := id h
  have hwf := ConLeche.Semantics.checkDeclsPure_envWF hf
  obtain ⟨-, hrun, -⟩ := foldlM_checkDecl_run ds hf
  have hnd := DeclsOf?.nodup hds
  have kn : ∀ {x : Expr} {c : ConLeche.Expr} {e : ConLeche.Env}, toCL? x = some c →
      c.constsResolve e = true → (∀ n, (e.find? n).isSome = true → (env.find? n).isSome = true) →
      KnownIn P x := fun hx hr hm =>
    h.knownIn hx (clResolves_of_constsResolve (ConLeche.Expr.constsResolve_of_find hm hr))
  have knS : ∀ {x : Expr} {n : ConLeche.Name} {c : ConLeche.ConstantInfo}, env.find? n = some c →
      toCL? x = some c.toConstantVal.type → KnownIn P x := fun hfc hx =>
    kn hx (hwf.consts _ (List.mem_of_find?_eq_some hfc)).2.2.1 (fun _ h => h)
  have rec1 : ∀ {L : List ConLeche.Declaration} {d}, declOf? P ci = some L → L = [d] →
      ∃ e e', ConLeche.checkDecl .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
        e d = .ok e' ∧ ∀ n, (e.find? n).isSome = true → (env.find? n).isSome = true := by
    intro L d hL hLd
    obtain ⟨L', hL', hLds⟩ := DeclsOf?.mem hds hci
    rw [hL, Option.some.injEq] at hL'
    exact hrun d (hLds d (by rw [← hL', hLd]; exact List.mem_singleton_self d))
  -- the block facts of an inductive of `P`
  have blk : ∀ {t : InductiveVal}, .inductInfo t ∈ P →
      ∃ nP block p, ConLeche.readBlock nP block = .ok p ∧
        (∀ c ∈ ConLeche.blockConstants p, env.find? c.name = some c) ∧
        (p.allCtors.map (·.1.name)).Nodup ∧
        (∀ {cvTs cs rs}, ConLeche.blockSplit block = some (cvTs, cs, rs) →
          p.allCtors.map (·.1.name) = cs.map (·.1.name)) ∧
        (∀ m ∈ p.members, ∃ rc ∈ p.recs, rc.cvR.name = m.declared.name.str "rec") ∧
        (∀ b ∈ block, ∃ ci ∈ P, b.name = Name.toCL ci.name) ∧
        (∀ n ∈ t.all, (findDecl P n).isSome = true) ∧
        (∃ cv, cvOf? t.toConstantVal = some cv ∧ ConLeche.ConstantInfo.indInfo cv {} ∈ block) ∧
        ∀ cn ∈ t.ctors, ∃ c, findConst P cn = some (.ctorInfo c) ∧ ∃ cv,
          cvOf? c.toConstantVal = some cv ∧
          ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields (Name.toCL t.name) ∈ block := by
    intro t ht
    obtain ⟨Hn, H, hH, hhead, hall, htH⟩ := h.head ht
    obtain ⟨block, p, hb, hdf, hst, hndC, hgr, hrec⟩ := h.blockPins hH hhead
    obtain ⟨block', he, hnames, hfwd⟩ := blockOf?_spec hb
    cases he
    obtain ⟨t', hft, hfr, hctors⟩ := hfwd t.name htH
    have : t' = t := by
      have := findDecl_self hnd ht
      change findConst P t.name = _ at this
      rw [hft] at this
      cases this; rfl
    subst this
    refine ⟨_, block, p, hdf, hst, hndC, hgr, hrec,
      fun b hb => (hnames b hb).imp fun _ h => ⟨h.1, h.2.1⟩, fun n hn => ?_, hfr, hctors⟩
    obtain ⟨_, hfn, -⟩ := hfwd n (hall ▸ hn)
    exact (show (findConst P n).isSome = true by rw [hfn]; rfl)
  cases ci with
  | defnInfo v =>
    have hs := hdef v rfl
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hs, hcv] at hL
    | some cv =>
    cases hval : toCL? v.value with
    | none => simp [declOf?, hs, hcv, hval] at hL
    | some val =>
    have hd : declOf? P (.defnInfo v) = some [.defnDecl cv val (hintOf v.hints)] := by
      simp [declOf?, hs, hcv, hval]
    obtain ⟨e, e', hstep, hm⟩ := rec1 hd rfl
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    obtain ⟨h1, h2⟩ := front_defn hstep
    exact ⟨kn hty h1 hm, fun d hd' => by cases hd'; exact kn hval h2 hm, nofun, nofun, nofun, nofun⟩
  | thmInfo v =>
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hcv] at hL
    | some cv =>
    cases hval : toCL? v.value with
    | none => simp [declOf?, hcv, hval] at hL
    | some val =>
    have hd : declOf? P (.thmInfo v) = some [.thmDecl cv val] := by simp [declOf?, hcv, hval]
    obtain ⟨e, e', hstep, hm⟩ := rec1 hd rfl
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    exact ⟨kn hty (front_thm hstep) hm, nofun, nofun, nofun, nofun, nofun⟩
  | opaqueInfo v =>
    have hs := hop v rfl
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hs, hcv] at hL
    | some cv =>
    cases hval : toCL? v.value with
    | none => simp [declOf?, hs, hcv, hval] at hL
    | some val =>
    have hd : declOf? P (.opaqueInfo v) = some [.opaqueDecl cv val] := by
      simp [declOf?, hs, hcv, hval]
    obtain ⟨e, e', hstep, hm⟩ := rec1 hd rfl
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    obtain ⟨h1, h2⟩ := front_opaque hstep
    exact ⟨kn hty h1 hm, nofun, fun o ho => by cases ho; exact kn hval h2 hm, nofun, nofun, nofun⟩
  | axiomInfo v =>
    have hs := hax v rfl
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hs, hcv] at hL
    | some cv =>
    have hd : declOf? P (.axiomInfo v) = some [.axiomDecl cv] := by simp [declOf?, hs, hcv]
    obtain ⟨e, e', hstep, hm⟩ := rec1 hd rfl
    have hcv' := hcv
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨?_, nofun, nofun, nofun, nofun, nofun⟩
    by_cases hq : Name.toCL v.name = ConLeche.quotSoundName
    · obtain ⟨cv', hcv'', hfind⟩ := h.find?_axiom (findDecl_self hnd hci) hs
        (by show Name.toCL v.name ≠ _; rw [hq]; decide)
      rw [hcv'] at hcv''
      cases hcv''
      exact knS hfind hty
    · exact kn hty (front_axiom hstep hq) hm
  | quotInfo v =>
    obtain ⟨L, hL, hLds⟩ := DeclsOf?.mem hds hci
    cases hcv : cvOf? v.toConstantVal with
    | none => simp [declOf?, hcv] at hL
    | some cv =>
    have hd : declOf? P (.quotInfo v) = some [.quotDecl (quotKindOf v.kind) cv] := by
      simp [declOf?, hcv]
    obtain ⟨e, e', hstep, -⟩ := rec1 hd rfl
    obtain ⟨-, hpin, -⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hstep
    rw [hd, Option.some.injEq] at hL
    have hdm : ConLeche.Declaration.quotDecl (quotKindOf v.kind) cv ∈ ds :=
      hLds _ (hL ▸ List.mem_singleton_self _)
    have hst := (checkDeclsPure_find? hf hdm).2 (List.pairwise_singleton _ _) _
      (List.mem_singleton_self (ConLeche.quotAt (quotKindOf v.kind) cv))
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨knS hst ?_, nofun, nofun, nofun, nofun, nofun⟩
    rw [quotAt_cv hpin]; exact hty
  | inductInfo v =>
    obtain ⟨_, block, p, hdf, hst, -, -, hrec, hnames, hall, ⟨cv, hcv, hfr⟩, hctors⟩ := blk hci
    obtain ⟨⟨caps', hcs'⟩, m, hm, hmd⟩ := readBlock_former_mem hdf hfr
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨knS (hst _ hcs') hty, nofun, nofun, fun iv hiv => ?_, nofun, nofun⟩
    injection hiv with hiv
    subst hiv
    refine ⟨hall, fun cn hcn => ?_, ?_⟩
    · obtain ⟨c, hfc, -⟩ := hctors cn hcn
      exact (show (findConst P cn).isSome = true by rw [hfc]; rfl)
    · obtain ⟨rc, hrc, hrn⟩ := hrec m hm
      obtain ⟨-, -, hR⟩ := ConLeche.readBlock_names hdf
      obtain ⟨b, hb, hbn⟩ := hR rc hrc
      obtain ⟨ci', hci', hcn⟩ := hnames b hb
      rw [hbn, hrn, hmd] at hcn
      have : mkRecName v.name = ci'.name := Name.toCL_injective hcn
      rw [this, findDecl_self hnd hci']; rfl
  | ctorInfo c =>
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    obtain ⟨t, hft, hct⟩ : ∃ t, findConst P c.induct = some (.inductInfo t) ∧ c.name ∈ t.ctors := by
      simp only [declOf?] at hL
      revert hL; split
      · rename_i t hft; split
        · rename_i hc; intro _
          exact ⟨t, hft, by simpa using hc⟩
        · intro h; exact nomatch h
      · intro h; exact nomatch h
    have htP := (findDecl_mem hft).1
    obtain ⟨_, block, p, hdf, hst, hndC, hgr, -, -, -, -, hctors⟩ := blk htP
    obtain ⟨c', hfc, cv, hcv, hcr⟩ := hctors c.name hct
    have : c' = c := by
      have := findDecl_self hnd hci
      change findConst P c.name = _ at this
      rw [hfc] at this
      cases this; rfl
    subst this
    obtain ⟨T', hT'⟩ := readBlock_ctor_mem hdf hndC hgr hcr
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨knS (hst _ hT') hty, nofun, nofun, nofun, fun cv hc => ?_, nofun⟩
    cases hc
    exact (show (findConst P c'.induct).isSome = true by rw [hft]; rfl)
  | recInfo r =>
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hci
    obtain ⟨t, hft, htall⟩ : ∃ t, r.all.head?.bind (findConst P) = some (.inductInfo t) ∧
        t.all = r.all := by
      simp only [declOf?] at hL
      revert hL; split
      · rename_i t hft; split
        · rename_i hc; intro _
          exact ⟨t, hft, by simpa using hc⟩
        · intro h; exact nomatch h
      · intro h; exact nomatch h
    obtain ⟨Hn, hHn, hfH⟩ : ∃ Hn, r.all.head? = some Hn ∧ findConst P Hn = some (.inductInfo t) := by
      cases hb : r.all.head? with
      | none => rw [hb] at hft; exact nomatch hft
      | some Hn => rw [hb] at hft; exact ⟨Hn, rfl, hft⟩
    have htP := (findDecl_mem hfH).1
    have htn := (findDecl_mem hfH).2
    obtain ⟨-, -, -, -, -, -, -, -, -, hall, -⟩ := blk htP
    obtain ⟨cv, rules, f, hcv, -, hfind⟩ := h.find?_rec hfH (by rw [htall]; exact hHn)
      (h.ind_safe htP) hci htall.symm
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨knS hfind hty, nofun, nofun, nofun, nofun, fun r' hr' n hn => ?_⟩
    cases hr'
    exact hall n (htall ▸ hn)

end EraseProof
