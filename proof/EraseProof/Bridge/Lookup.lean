import EraseProof.Bridge.WkEnv
import EraseProof.Bridge.Levels
import Metalean.Typing.Env

/-!
# `ProgEnv`: the generic lookup

Every declaration of a program over a well-formed environment is bound in the table, and its type
translates to a type of its translation (`ProgEnv.lookup`). Reference: `declared_constant` with
`on_global_env` (MC §3.6); `EnvWF.entryWF` (`ML Typing/Env.lean:97`).
-/

open Lean Erasure
open Metalean (Sigs Sig Env Entry Head EnvWF)

namespace EraseProof

/-- Instantiating the universe parameters by themselves is the identity on a level. -/
private theorem instLevel_self (ps : List Name) : ∀ u : Level,
    Pure.instLevel ps (ps.map .param) u = u
  | .zero => rfl
  | .succ u => by simp [Pure.instLevel, instLevel_self ps u]
  | .max a b => by simp [Pure.instLevel, instLevel_self ps a, instLevel_self ps b]
  | .imax a b => by simp [Pure.instLevel, instLevel_self ps a, instLevel_self ps b]
  | .param n => by
    simp only [Pure.instLevel]
    split
    · rename_i p u h
      have hm := List.mem_of_find?_eq_some h
      have hn : p = n := by simpa using List.find?_some h
      have key : ∀ (l : List Name) q, q ∈ l.zip (l.map Level.param) → q.2 = .param q.1 := by
        intro l
        induction l with
        | nil => simp
        | cons x l ih =>
          intro q hq
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hq
          rcases hq with rfl | hq
          · rfl
          · exact ih q hq
      have := key ps _ hm
      simp only at this
      rw [this, hn]
    · rfl
  | .mvar _ => rfl

/-- Instantiating the universe parameters by themselves is the identity on a term. -/
private theorem instLevels_self (ps : List Name) : ∀ e : Expr,
    Pure.instLevels ps (ps.map .param) e = e
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => rfl
  | .sort u => by simp [Pure.instLevels, instLevel_self]
  | .const c us => by
    simp only [Pure.instLevels, Expr.const.injEq, true_and]
    conv => rhs; rw [← List.map_id us]
    exact List.map_congr_left fun u _ => instLevel_self ps u
  | .app f a => by simp [Pure.instLevels, instLevels_self ps f, instLevels_self ps a]
  | .lam _ t b _ => by simp [Pure.instLevels, instLevels_self ps t, instLevels_self ps b]
  | .forallE _ t b _ => by simp [Pure.instLevels, instLevels_self ps t, instLevels_self ps b]
  | .letE _ t v b _ => by
    simp [Pure.instLevels, instLevels_self ps t, instLevels_self ps v, instLevels_self ps b]
  | .mdata _ e => by simp [Pure.instLevels, instLevels_self ps e]
  | .proj _ _ e => by simp [Pure.instLevels, instLevels_self ps e]

/-- The universe parameters of a declaration translate, as levels of the declaration itself. -/
private theorem TrLevels_params (lps : List Name) :
    ∃ ls, TrLevels lps (lps.map .param) lps.length = some ls := by
  have : ∀ xs : List Name, (∀ x ∈ xs, x ∈ lps) →
      ∃ ys, (xs.map Level.param).mapM (TrLevel lps) = some ys ∧ ys.length = xs.length := by
    intro xs hxs
    induction xs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons x xs ih =>
      obtain ⟨ys, hys, hl⟩ := ih fun y hy => hxs y (List.mem_cons_of_mem _ hy)
      obtain ⟨p, hp⟩ : ∃ p, lps.finIdxOf? x = some p :=
        Option.isSome_iff_exists.mp (by
          simpa [List.isSome_finIdxOf?] using hxs x List.mem_cons_self)
      exact ⟨.param p :: ys, by simp [List.mapM_cons, TrLevel, hp, hys], by simp [hl]⟩
  obtain ⟨ys, hys, hl⟩ := this lps fun _ h => h
  refine ⟨fun i => ys[i.val]'(by omega), ?_⟩
  simp only [TrLevels, bind, Option.bind_eq_some_iff]
  exact ⟨ys, hys, by rw [dite_eq_left (by omega)]⟩

/-- `ConstTyped` survives one new entry whose table agrees with the old one, weakened. -/
private theorem ConstTyped.wkEnv {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {sig : Sig}
    {ent : Entry ζ sig} {B' : Binds (ζ.snoc sig)} (hB : ∀ c b, B c = some b → B' c = some b.wk)
    {ci : ConstantInfo} (h : ConstTyped E B ci) : ConstTyped (E.snoc ent) B' ci := by
  obtain ⟨T, t₀, hT, ht₀, hty⟩ := h
  exact ⟨_, _, TrM.wkEnv hB hT, TrM.wkEnv hB ht₀, Metalean.Defeq.map (envS E ent) hty⟩

/-- The type of the newest constant entry, as an entry of the extended environment. -/
private theorem constType_here {ζ : Sigs} {E : Env ζ} {kind : Metalean.ConstKind} {nl : Nat}
    (ent : Entry ζ (.const kind nl)) :
    ((E.snoc ent).get .here).constType = ent.constType.map wkS := by
  show (ent.map _).constType = _
  cases ent <;> rfl

/-- A well-formed environment's prefix is well-formed. -/
private theorem envWF_prev {ζ : Sigs} {E : Env ζ} {sig : Sig} {ent : Entry ζ sig}
    (h : EnvWF (E.snoc ent)) : EnvWF E := by
  cases h
  assumption

/-- The new constant of a single-declaration entry is typed by its translated type. -/
private theorem ConstTyped.here {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {kind : Metalean.ConstKind}
    {ci : ConstantInfo} {ent : Entry ζ (.const kind ci.levelParams.length)}
    {t : Metalean.Expr ζ ci.levelParams.length 0} (hent : ent.constType = t)
    (hE : EnvWF (E.snoc ent))
    (hB : ∀ c b, B c = some b →
      ((Binds.wk (sig := .const kind ci.levelParams.length) B).set ci.name (.const .here)) c =
        some b.wk)
    (ht : TrM E B ci.levelParams .nil [] ci.type t) :
    ConstTyped (E.snoc ent) ((Binds.wk (sig := .const kind ci.levelParams.length) B).set ci.name
      (.const .here)) ci := by
  obtain ⟨ls, hls⟩ := TrLevels_params ci.levelParams
  have hT := TrM.instLevels hls (TrM.wkEnv (ent := ent) hB ht)
  rw [instLevels_self] at hT
  have hc : TrM (E.snoc ent) ((Binds.wk (sig := .const kind ci.levelParams.length) B).set ci.name
      (.const .here)) ci.levelParams .nil []
      (.const ci.name (ci.levelParams.map .param)) (.const .here ls) :=
    .const (by simp [Binds.set]) hls
  refine ⟨_, _, hT, hc, ?_⟩
  obtain ⟨l, hl⟩ := Metalean.EntryWF.constType (Γ := .nil) (hE.entryWF .here) ls
  have hty := Metalean.Defeq.constDF (Γ := .nil) (η := (.here : Head (ζ.snoc _) _)) (ls := ls) hl
  rw [constType_here, hent] at hty
  exact hty

variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- Every declaration of the program is bound in the table, with its type related to its
translation's type. Reference: `declared_constant` + `on_global_env` (MC §3.6);
`EnvWF.entryWF` (`ML Typing/Env.lean:97`). -/
theorem ProgEnv.lookup {c : Name} {ci : ConstantInfo} (h : ProgEnv P ζ E B) (hE : EnvWF E)
    (hc : findDecl P c = some ci) : ∃ b, B c = some b ∧ ConstTyped E B ci := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v t hP hfr _ _ ht ih =>
    have hE' := envWF_prev hE
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      exact ⟨_, by rw [← hn, Binds.set]; exact ite_eq_left_of_eq_true _ _ (eq_true rfl), ConstTyped.here (ci := .axiomInfo v) rfl hE
        (hP.set_ext hfr _) ht⟩
    · obtain ⟨b, hb, hct⟩ := ih hE' hc
      exact ⟨_, hP.set_ext hfr _ _ _ hb, hct.wkEnv (hP.set_ext hfr _)⟩
  | @defn _ _ _ _ v t e hP hfr _ _ _ ht _ ih =>
    have hE' := envWF_prev hE
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      exact ⟨_, by rw [← hn, Binds.set]; exact ite_eq_left_of_eq_true _ _ (eq_true rfl), ConstTyped.here (ci := .defnInfo v) rfl hE
        (hP.set_ext hfr _) ht⟩
    · obtain ⟨b, hb, hct⟩ := ih hE' hc
      exact ⟨_, hP.set_ext hfr _ _ _ hb, hct.wkEnv (hP.set_ext hfr _)⟩
  | @thm _ _ _ _ v t hP hfr _ _ _ ht _ ih =>
    have hE' := envWF_prev hE
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      exact ⟨_, by rw [← hn, Binds.set]; exact ite_eq_left_of_eq_true _ _ (eq_true rfl), ConstTyped.here (ci := .thmInfo v) rfl hE
        (hP.set_ext hfr _) ht⟩
    · obtain ⟨b, hb, hct⟩ := ih hE' hc
      exact ⟨_, hP.set_ext hfr _ _ _ hb, hct.wkEnv (hP.set_ext hfr _)⟩
  | @«opaque» _ _ _ _ v t hP hfr _ _ _ _ ht ih =>
    have hE' := envWF_prev hE
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      exact ⟨_, by rw [← hn, Binds.set]; exact ite_eq_left_of_eq_true _ _ (eq_true rfl), ConstTyped.here (ci := .opaqueInfo v) rfl hE
        (hP.set_ext hfr _) ht⟩
    · obtain ⟨b, hb, hct⟩ := ih hE' hc
      exact ⟨_, hP.set_ext hfr _ _ _ hb, hct.wkEnv (hP.set_ext hfr _)⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk hct ih =>
    have hE' := envWF_prev hE
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci' =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      subst hn
      rcases IndBlock.mem_decls hm with ⟨s, rfl⟩ | ⟨s, k, rfl⟩ | ⟨s, rfl⟩
      · exact ⟨_, (hblk.recr s).2.1, hct _ hm⟩
      · exact ⟨_, (hblk.ctor s k).1, hct _ hm⟩
      · exact ⟨_, (hblk.ind s).1, hct _ hm⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨b, hb, hct'⟩ := ih hE' hc
      exact ⟨_, hP.ext_ext hfr hext _ _ hb, hct'.wkEnv (hP.ext_ext hfr hext)⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext hq ih =>
    have hE' := envWF_prev hE
    rw [findDecl_append] at hc
    have hfr' : ∀ ci ∈ qs.map ConstantInfo.quotInfo, findDecl _ ci.name = none :=
      fun ci hci => by obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hci; exact hfr q hq'
    have hB := hP.ext_ext (decls := qs.map ConstantInfo.quotInfo) hfr'
      (by rw [List.map_map]; exact hext)
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci' =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      simp only [List.map_reverse, List.mem_reverse, List.mem_map] at hm
      obtain ⟨q, hq', rfl⟩ := hm
      subst hn
      exact ⟨_, (hq q hq').1, (hq q hq').2⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨b, hb, hct'⟩ := ih hE' hc
      exact ⟨_, hB _ _ hb, hct'.wkEnv hB⟩

end EraseProof
