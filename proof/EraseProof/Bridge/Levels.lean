import EraseProof.Bridge.InstL
import EraseProof.Bridge.Basic
import Metalean.Typing.InstLevel

/-!
# Universe instantiation of the translation

The shipping universe instantiation `Pure.instLevels` (`LeanToLambdaBox/Erasure/Pure.lean:164`)
of a Lean term is the Lean form of Metalean's universe instantiation `Expr.instL` of its
translation (`TrM.instLevels`), the levels being translated by `TrLevels`. Metalean's
counterpart on typing is `Defeq.instLevel` (`ML Typing/InstLevel.lean:19`).
-/

open Lean Erasure
open Metalean (InstLevel)

namespace EraseProof

/-- The lookup of `Pure.instLevel` finds a parameter at its first index. -/
theorem find_zip_of_finIdxOf : ∀ {ps : List Name} {us : List Level} {n : Name}
    {p : Fin ps.length} (hl : us.length = ps.length), ps.finIdxOf? n = some p →
    (ps.zip us).find? (·.1 == n) = some (n, us[p.val]'(by omega))
  | [], _, _, p, _, _ => p.elim0
  | a :: ps, u :: us, n, p, hl, h => by
    rw [List.finIdxOf?_eq_some_iff] at h
    obtain ⟨hp, hlt⟩ := h
    obtain ⟨_ | p, hpl⟩ := p
    · have hp' : a = n := hp
      subst hp'
      simp [List.zip_cons_cons]
    · have ha : (a == n) = false := by
        have := hlt ⟨0, by simp⟩ (by simp [Fin.lt_def])
        simpa using this
      have hl' : us.length = ps.length := by simpa using hl
      have ih := find_zip_of_finIdxOf (p := ⟨p, by simpa using hpl⟩) hl'
        (List.finIdxOf?_eq_some_iff.mpr ⟨by simpa using hp, fun j hj => by
          simpa using hlt ⟨j.val + 1, by simp⟩ (by simpa [Fin.lt_def] using hj)⟩)
      simp [List.zip_cons_cons, ha, ih]
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- A declaration's own universe parameters, instantiated, are the instantiating levels. -/
theorem params_instLevel {ps : List Name} (hnd : ps.Nodup) {us : List Level}
    (hl : us.length = ps.length) : (ps.map .param).map (Pure.instLevel ps us) = us := by
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  simp only [List.map_map, List.getElem_map, Function.comp_apply, Pure.instLevel]
  have hi : i < ps.length := by simpa using h₁
  have hfi : ps.finIdxOf? ps[i] = some ⟨i, hi⟩ :=
    List.finIdxOf?_eq_some_iff.mpr ⟨rfl, fun j hj heq => by
      have := (List.Nodup.getElem_inj hnd).mp heq
      rw [Fin.lt_def] at hj; simp at hj this; omega⟩
  rw [find_zip_of_finIdxOf hl hfi]

/-- A successful `mapM` in `Option` relates the lists componentwise. -/
theorem mapM_option_get {α β : Type} {f : α → Option β} : ∀ {xs : List α} {ys : List β},
    xs.mapM f = some ys → ∃ h : ys.length = xs.length, ∀ i (hi : i < xs.length),
      f xs[i] = some (ys[i]'(by omega))
  | [], ys, h => by simp at h; subst h; exact ⟨rfl, fun i hi => by simp at hi⟩
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    obtain ⟨hl, hget⟩ := mapM_option_get hys
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using hget i (by simpa using hi)

/-- `TrLevels` translates each level at its own index. -/
theorem TrLevels_get {lps : List Name} {us : List Level} {k : Nat}
    {ls : Fin k → Metalean.Level lps.length} (h : TrLevels lps us k = some ls) :
    ∃ hk : us.length = k, ∀ i : Fin k, TrLevel lps (us[i.val]'(by omega)) = some (ls i) := by
  simp only [TrLevels, bind, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, h⟩ := h
  split at h
  · rename_i hlen
    cases h
    obtain ⟨hl, hget⟩ := mapM_option_get hL
    exact ⟨by omega, fun i => hget i.val (by omega)⟩
  · cases h

section
variable {lps lps' : List Name} {us : List Level} {ls : Fin lps'.length → Metalean.Level lps.length}

/-- Universe instantiation of one level: if `u` translates to `l` over `lps'`, then
`Pure.instLevel lps' us u` translates to `l` instantiated by the translation `ls` of `us`. Reference:
`ofLevel_instLevel` (`L4 Typing/InstLevels.lean:53`). -/
theorem TrLevel_instLevel (hus : TrLevels lps us lps'.length = some ls) :
    ∀ {u : Level} {l : Metalean.Level lps'.length}, TrLevel lps' u = some l →
      TrLevel lps (Pure.instLevel lps' us u) = some l{ls}
  | .zero, l, h => by cases h; rfl
  | .succ u, l, h => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨l₀, h₀, rfl⟩ := h
    simp [Pure.instLevel, TrLevel, TrLevel_instLevel hus h₀]
  | .max a b, l, h => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp [Pure.instLevel, TrLevel, TrLevel_instLevel hus ha, TrLevel_instLevel hus hb]
  | .imax a b, l, h => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp [Pure.instLevel, TrLevel, TrLevel_instLevel hus ha, TrLevel_instLevel hus hb]
  | .param n, l, h => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨hk, hget⟩ := TrLevels_get hus
    simp only [Pure.instLevel, find_zip_of_finIdxOf hk hp]
    simpa using hget p
  | .mvar _, l, h => by cases h

/-- `TrLevel_instLevel` on a list of levels with `mapM`. -/
theorem mapM_TrLevel_instLevel (hus : TrLevels lps us lps'.length = some ls) :
    ∀ {vs : List Level} {ws : List (Metalean.Level lps'.length)},
      vs.mapM (TrLevel lps') = some ws →
      (vs.map (Pure.instLevel lps' us)).mapM (TrLevel lps) = some (ws.map (·{ls}))
  | [], ws, h => by simp at h; subst h; rfl
  | v :: vs, ws, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    simp [List.mapM_cons, TrLevel_instLevel hus hw, mapM_TrLevel_instLevel hus hws]

/-- `TrLevel_instLevel` on the levels of a constant occurrence. -/
theorem TrLevels_instLevel (hus : TrLevels lps us lps'.length = some ls) {vs : List Level}
    {k : Nat} {ls₀ : Fin k → Metalean.Level lps'.length} (h : TrLevels lps' vs k = some ls₀) :
    TrLevels lps (vs.map (Pure.instLevel lps' us)) k = some ls₀{ls} := by
  simp only [TrLevels, bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨L, hL, h⟩ := h
  split at h
  · rename_i hlen
    cases h
    refine ⟨_, mapM_TrLevel_instLevel hus hL, ?_⟩
    rw [dite_eq_left (by simpa using hlen)]
    congr 1
    funext i
    simp
  · cases h

end

/-- Universe instantiation of an application spine. -/
theorem instLevels_foldl (ps : List Name) (us : List Level) (f : Expr) (as : List Expr) :
    Pure.instLevels ps us (as.foldl .app f) =
      (as.map (Pure.instLevels ps us)).foldl .app (Pure.instLevels ps us f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, Pure.instLevels]

/-- Universe instantiation commutes with taking the head of a spine. -/
theorem instLevels_getAppFn (ps : List Name) (us : List Level) (f : Expr) :
    (Pure.instLevels ps us f).getAppFn = Pure.instLevels ps us f.getAppFn := by
  induction f with
  | app f a ih => simpa [Pure.instLevels, Expr.getAppFn] using ih
  | _ => simp [Pure.instLevels, Expr.getAppFn]

/-- A term whose universe instantiation is a constant is that constant at other levels. -/
theorem instLevels_eq_const {ps : List Name} {us : List Level} {g : Expr} {c : Name}
    {vs : List Level} (h : Pure.instLevels ps us g = .const c vs) : ∃ vs', g = .const c vs' := by
  cases g <;> simp only [Pure.instLevels] at h <;> first | (cases h; exact ⟨_, rfl⟩) | cases h

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {lps lps' : List Name} {us : List Level}
  {ls : Fin lps'.length → Metalean.Level lps.length}

/-- The recursor's level arguments under universe instantiation. -/
theorem RecrLevels.instL {ι : Metalean.IndSig} {I : Metalean.Inductive ζ ι} {vs vs' : List Level}
    {l : Metalean.Level lps'.length} (hus : TrLevels lps us lps'.length = some ls)
    (h : RecrLevels I lps' vs l vs') :
    RecrLevels I lps (vs.map (Pure.instLevel lps' us)) l{ls} (vs'.map (Pure.instLevel lps' us)) := by
  rcases h with ⟨hL, u, rfl, hu⟩ | ⟨hL, rfl, rfl⟩
  · exact .inl ⟨hL, _, rfl, TrLevel_instLevel hus hu⟩
  · exact .inr ⟨hL, rfl, rfl⟩

/-- Every rule of `SatTr` commutes with universe instantiation. -/
theorem SatTr.instL {n : Nat} {b : MBinding ζ} {vs : List Level}
    {args : List (Metalean.Expr ζ lps'.length n)} {t : Metalean.Expr ζ lps'.length n}
    (hus : TrLevels lps us lps'.length = some ls) (h : SatTr E lps' b vs args t) :
    SatTr E lps b (vs.map (Pure.instLevel lps' us)) (args.map (·{ls})) t{ls} := by
  cases h with
  | indSat ps is rest hls =>
    simp only [List.map_append, List.map_ofFn, Metalean.Expr.instL_appList]
    exact SatTr.indSat (E := E) (fun p => (ps p){ls}) (fun i => (is i){ls}) (rest.map (·{ls}))
      (TrLevels_instLevel hus hls)
  | indEta hls hlen =>
    rw [Metalean.Expr.instL_appList, Metalean.Expr.instL_wkClosed, indTerm_instL]
    exact SatTr.indEta (E := E) (args := args.map (·{ls})) (TrLevels_instLevel hus hls)
      (by simpa using hlen)
  | ctorSat ps fs rest fds recFds hls hfs hord hperm =>
    simp only [List.map_append, List.map_ofFn, Metalean.Expr.instL_appList]
    exact SatTr.ctorSat (E := E) (fun p => (ps p){ls}) (fs.map (·{ls})) (rest.map (·{ls}))
      (fun i => (fds i){ls}) (fun i => (recFds i){ls}) (TrLevels_instLevel hus hls)
      (by simpa using hfs) hord
      fun o => by
        obtain ⟨j, a, h₁, h₂, h₃⟩ := hperm o
        refine ⟨j, a{ls}, h₁, by simp [h₂], ?_⟩
        rw [← h₃]
        exact (congrFun (Fin.append_comp fds recFds (·{ls})) o).symm
  | ctorEta hls hlen ht =>
    rw [Metalean.Expr.instL_appList, Metalean.Expr.instL_wkClosed]
    exact SatTr.ctorEta (E := E) (args := args.map (·{ls})) (TrLevels_instLevel hus hls)
      (by simpa using hlen) (ctorTerm_instL _ _ _ _ _ _ ls ht)
  | recrSat mo A rest mins hRL hls hmo hwrap =>
    simp only [List.map_append, List.map_ofFn, Metalean.Expr.instL_appList]
    exact SatTr.recrSat (E := E) mo (fun i => (A i){ls}) (rest.map (·{ls}))
      (fun t c => (mins t c){ls}) (RecrLevels.instL hus hRL) (TrLevels_instLevel hus hls) hmo
      fun t c => wrapCase_instL _ _ _ _ _ _ _ _ ls (hwrap t c)
  | recrEta mo hRL hls hmo hlen ht =>
    rw [Metalean.Expr.instL_appList, Metalean.Expr.instL_wkClosed]
    exact SatTr.recrEta (E := E) (args := args.map (·{ls})) mo (RecrLevels.instL hus hRL)
      (TrLevels_instLevel hus hls) hmo (by simpa using hlen) (recrTerm_instL _ _ _ _ _ _ ls ht)
  | quotType hu | quotMk hu | quotLift hu | quotInd hu =>
    have hu' := mapM_TrLevel_instLevel hus hu
    simp only [List.map_cons, List.map_nil] at hu'
    simp only [List.map_cons, Metalean.Expr.instL_appList, List.cons_append, List.nil_append]
    first | exact .quotType hu' | exact .quotMk hu' | exact .quotLift hu' | exact .quotInd hu'
  | quotEta hu hlen ht =>
    rw [Metalean.Expr.instL_appList, Metalean.Expr.instL_wkClosed]
    exact SatTr.quotEta (E := E) (args := args.map (·{ls})) (mapM_TrLevel_instLevel hus hu)
      (by simpa using hlen) (quotTerm_instL _ _ _ _ ls ht)

end

section
variable {ζ : Metalean.Sigs} {ℓ ℓ' : Nat}

/-- Universe instantiation of a local's denotation. -/
def MLDecl.instL (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat} : MLDecl ζ ℓ n → MLDecl ζ ℓ' n
  | .vlam v => .vlam v
  | .vlet e => .vlet e{ls}

/-- Universe instantiation of the locals. -/
def MLCtx.instL (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat} (Δ : MLCtx ζ ℓ n) : MLCtx ζ ℓ' n :=
  Δ.map fun (y, d) => (y, d.instL ls)

/-- `findB` after universe instantiation of the locals. -/
theorem MLCtx.findB_instL (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat} (Δ : MLCtx ζ ℓ n) (i : Nat) :
    (Δ.instL ls).findB i = (Δ.findB i).map (·{ls}) := by
  induction Δ generalizing i with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨_ | y, d⟩ := p
    · cases i <;> cases d <;> simp [MLCtx.instL, MLCtx.findB, MLDecl.instL, MLDecl.denote, ← ih]
    · simpa [MLCtx.instL, MLCtx.findB] using ih i

/-- `findF` after universe instantiation of the locals. -/
theorem MLCtx.findF_instL (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat} (Δ : MLCtx ζ ℓ n) (x : FVarId) :
    (Δ.instL ls).findF x = (Δ.findF x).map (·{ls}) := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨_ | y, d⟩ := p
    · simpa [MLCtx.instL, MLCtx.findF] using ih
    · simp only [MLCtx.instL, List.map_cons, MLCtx.findF]
      split
      · cases d <;> rfl
      · simpa [MLCtx.instL] using ih

/-- Universe instantiation of the locals commutes with entering a binder. -/
theorem MLCtx.instL_pushLam (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat} (Δ : MLCtx ζ ℓ n)
    (x : Option FVarId) : (Δ.pushLam x).instL ls = (Δ.instL ls).pushLam x := by
  simp only [MLCtx.pushLam, MLCtx.instL, List.map_cons, List.map_map]
  congr 2
  funext ⟨y, d⟩
  cases d <;> simp [MLDecl.instL, MLDecl.wk]

end

/-- `TypedExt` is stable under universe instantiation (the extension instantiated too). -/
theorem LevelsExt.TypedExt.instL {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ ℓ' n : Nat}
    (ls : Fin ℓ → Metalean.Level ℓ') {Γ : Metalean.Ctx ζ ℓ 0 n} {e T : Metalean.Expr ζ ℓ n}
    (h : TypedExt E Γ e T) : TypedExt E (Γ{ls}) (e{ls}) (T{ls}) := by
  obtain ⟨m, Γ', ρ, hρ, hget, hty⟩ := h
  refine ⟨m, Γ'{ls}, ρ, hρ, fun v => ?_, by simpa using Metalean.Defeq.instLevel ls hty⟩
  rw [← Metalean.Ctx.get_instL, ← Metalean.Ctx.get_instL, hget, Metalean.Expr.instL_rename]

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps lps' : List Name}
  {us : List Level} {ls : Fin lps'.length → Metalean.Level lps.length}

/-- Universe instantiation of a translation under binders and locals: `Pure.instLevels` on the
source, `instL` on the image, the context and the locals. Reference: `TrS.instLevels`
(`L4 Typing/InstLevels.lean:113`); `Defeq.instLevel` (`ML Typing/InstLevel.lean:19`). -/
theorem TrM.instL (hus : TrLevels lps us lps'.length = some ls) {n : Nat}
    {Γ : Metalean.Ctx ζ lps'.length 0 n} {Δ : MLCtx ζ lps'.length n} {e : Expr}
    {t : Metalean.Expr ζ lps'.length n} (h : TrM E B lps' Γ Δ e t) :
    TrM E B lps (Γ{ls}) (Δ.instL ls) (Pure.instLevels lps' us e) t{ls} := by
  induction h with
  | bvar hb => exact .bvar (by rw [MLCtx.findB_instL, hb]; rfl)
  | fvar hf => exact .fvar (by rw [MLCtx.findF_instL, hf]; rfl)
  | sort hl => exact .sort (TrLevel_instLevel hus hl)
  | const h₁ h₂ => exact .const h₁ (TrLevels_instLevel hus h₂)
  | @special _ _ _ _ _ as as' _ _ hb hs hlen _ hsat ih =>
    rw [mkAppN_toArray, instLevels_foldl, ← mkAppN_toArray]
    exact .special hb hs (by simpa using hlen) (fun i a a' ha ha' => by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ha ha'
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨a₀', ha₀', rfl⟩ := ha'
      exact ih i a₀ a₀' ha₀ ha₀') (hsat.instL hus)
  | app hns _ _ ih₁ ih₂ =>
    refine .app (fun ⟨c, vs, b, hc, hB, hs⟩ => hns ?_) ih₁ ih₂
    rw [instLevels_getAppFn] at hc
    obtain ⟨vs', hvs'⟩ := instLevels_eq_const hc
    exact ⟨c, vs', b, hvs', hB, hs⟩
  | lam _ _ ih₁ ih₂ =>
    rw [MLCtx.instL_pushLam] at ih₂
    exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ =>
    rw [MLCtx.instL_pushLam] at ih₂
    exact .forallE ih₁ ih₂
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    simp only [Metalean.Expr.inst_letE, Metalean.Expr.instL_wk]
    exact .letE ih₁ ih₂ ih₃
  | mdata _ ih => exact .mdata ih
  | lit hB h₀ h₁ =>
    rw [natLitM_instL]
    exact .lit hB h₀ h₁
  | projStruct hst hi hS _ hty ih =>
    rw [Metalean.Inductive.IsStructure.projTerm_instL]
    exact .projStruct hst hi hS ih (by simpa using LevelsExt.TypedExt.instL ls hty)
  | projProof hi hS hs hc hr hf hns _ hty ih =>
    rw [projProofTerm_instL]
    exact .projProof hi hS hs hc hr hf hns ih (by simpa using LevelsExt.TypedExt.instL ls hty)

/-- Universe instantiation of closed terms: `Pure.instLevels lps' us e` is the Lean form of the
translation of `e` with its universe parameters instantiated by the translation `ls` of `us`.
Reference: `TrS.instLevels` (`L4 Typing/InstLevels.lean:113`); `Defeq.instLevel`
(`ML Typing/InstLevel.lean:19`). -/
theorem TrM.instLevels {lps' : List Name} {us : List Level}
    {ls : Fin lps'.length → Metalean.Level lps.length} {t : Metalean.Expr ζ lps'.length 0}
    (hus : TrLevels lps us lps'.length = some ls) (h : TrM E B lps' .nil [] e t) :
    TrM E B lps .nil [] (Pure.instLevels lps' us e) t{ls} :=
  h.instL hus

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {lps : List Name}

/-- A recursor image with fewer arguments than the arity is the recursor's η-term. -/
theorem satTr_recrEta_inv {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {os : List (List (List Nat))} {lps' : List Name} {n : Nat}
    {us : List Level} {args : List (Metalean.Expr ζ lps'.length n)}
    {t : Metalean.Expr ζ lps'.length n} (h : SatTr E lps' (.recr η s os) us args t)
    (hlt : args.length < ι.recrEnd s) :
    ∃ l us' ls mo t₀, RecrLevels (E.get η).block lps' us l us' ∧
      TrLevels lps' us' ι.nlevels = some ls ∧
      (∀ t c, (os[t.val]?.bind (·[c.val]?)) = some (mo t c)) ∧
      Metalean.Frontend.recrTerm (E.get η).block η s ls l mo = .ok t₀ ∧
      t = t₀.wkClosed.appList args := by
  cases h with
  | recrSat _ _ _ _ =>
    simp only [List.length_append, List.length_ofFn] at hlt; omega
  | recrEta mo hRL hls hmo _ hrt => exact ⟨_, _, _, mo, _, hRL, hls, hmo, hrt, rfl⟩

/-- The levels of a recursor spine translate, as many as the recursor's universe parameters `ps`:
the spine's image and the image of the recursor at its own parameters read their levels by one
`RecrLevels` of the same block. -/
theorem recr_spine_levels {ι : Metalean.IndSig} {I : Metalean.Inductive ζ ι} {ps : List Name}
    {us us' us₁ : List Level} {l : Metalean.Level lps.length} {l₁ : Metalean.Level ps.length}
    {k : Nat} {ls : Fin k → Metalean.Level lps.length} {ls₁ : Fin k → Metalean.Level ps.length}
    (hRL : RecrLevels I lps us l us') (hls : TrLevels lps us' k = some ls)
    (hRL₁ : RecrLevels I ps (ps.map .param) l₁ us₁) (hls₁ : TrLevels ps us₁ k = some ls₁) :
    ∃ ls', TrLevels lps us ps.length = some ls' := by
  obtain ⟨hk₁, -⟩ := TrLevels_get hls₁
  simp only [TrLevels, bind, Option.bind_eq_some_iff] at hls ⊢
  obtain ⟨L, hL, hls⟩ := hls
  have hLk : L.length = k := by
    by_contra hne; rw [dif_neg hne] at hls; cases hls
  rcases hRL with ⟨hI, u, rfl, hu⟩ | ⟨hI, rfl, -⟩ <;>
    rcases hRL₁ with ⟨hI₁, u₁, hps, -⟩ | ⟨hI₁, hps, -⟩
  · have hlen := congrArg List.length hps
    simp only [List.length_map, List.length_cons] at hlen
    have hl' : (l :: L).length = ps.length := by simp; omega
    exact ⟨_, ⟨l :: L, by simp [List.mapM_cons, hu, hL], by rw [dif_pos hl']⟩⟩
  · exact absurd hI hI₁
  · exact absurd hI₁ hI
  · have hlen := congrArg List.length hps
    simp only [List.length_map] at hlen
    exact ⟨_, ⟨L, hL, by rw [dif_pos (by omega)]⟩⟩

end

end EraseProof
