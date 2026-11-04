import EraseProof.Spec
import EraseProof.Oracle.Whnf

/-!
# The oracle on atom spines

`Pure.isErasable_atom`: on an application spine `c.{us} a₁ … aₖ` whose head `c` is an atom
(`EvalEnv.isAtom`), the shipping oracle `Erasure.Pure.isErasable` answers `true` or fails, never
`false`, for every list of locals and without a typing hypothesis. A spine headed by a theorem is
answered `true` by the oracle's first step. Otherwise the proof follows the oracle on syntactic
shapes: the inferred type of a spine over a constant whose declared type is an arity is an arity
(`ArityShape`), which `Erasure.Pure.isArity` accepts; the inferred type of a spine over a proof of
an evident proposition is an evident proposition (`PropShape`), whose inferred sort is a syntactic
sort with an evidently zero level, which `Erasure.Pure.alwaysZero` accepts. The heads of evident
propositions are `DeltaFree`, so no δ step fires. Port of `L4 Oracle/Atom.lean` and
`L4 Oracle/AtomShapes.lean`.
-/

open Lean Erasure

namespace EraseProof

namespace OracleAtom

/-! ## Shapes -/

/-- `T` is the syntactic arity `Π x₁…xₙ, Sort u` (`mdata` transparent), the inductive form of
`arityShape`. -/
inductive ArityShape : Expr → Nat → Level → Prop
  | sort {u : Level} : ArityShape (.sort u) 0 u
  | forallE {b : Expr} {n : Nat} {u : Level} {nm : Name} {t : Expr} {bi : BinderInfo} :
      ArityShape b n u → ArityShape (.forallE nm t b bi) (n + 1) u
  | mdata {e : Expr} {n : Nat} {u : Level} {m : MData} :
      ArityShape e n u → ArityShape (.mdata m e) n u

/-- `e` is the application spine `h.{vs} a₁ … aₖ`. -/
inductive ConstSpine (h : Name) (vs : List Level) : Nat → Expr → Prop
  | const : ConstSpine h vs 0 (.const h vs)
  | app {k : Nat} {f a : Expr} : ConstSpine h vs k f → ConstSpine h vs (k + 1) (.app f a)

/-- `e` is an evident proposition over `D`, the inductive form of `EvidentProp`. -/
inductive PropShape (D : List ConstantInfo) : Expr → Prop
  | forallE {b : Expr} {nm : Name} {t : Expr} {bi : BinderInfo} :
      PropShape D b → PropShape D (.forallE nm t b bi)
  | mdata {e : Expr} {m : MData} : PropShape D e → PropShape D (.mdata m e)
  | tail {h : Name} {ci : ConstantInfo} {k : Nat} {u : Level} {vs : List Level} {e : Expr} :
      findDecl D h = some ci → DeltaFree ci = true → arityShape ci.type = some (k, u) →
      EvidentZero (Pure.instLevel ci.levelParams vs u) = true → ConstSpine h vs k e →
      PropShape D e

/-! ## From the Boolean definitions -/

theorem ArityShape.of_arityShape : ∀ {T : Expr} {n : Nat} {u : Level},
    arityShape T = some (n, u) → ArityShape T n u
  | .sort _, n, u, h => by
    simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact .sort
  | .forallE _ _ b _, n, u, h => by
    simp only [arityShape, Option.map_eq_some_iff] at h
    obtain ⟨⟨n', u'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact .forallE (of_arityShape h1)
  | .mdata _ e, n, u, h => by
    simp only [arityShape] at h; exact .mdata (of_arityShape h)
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .const .., _, _, h
  | .app .., _, _, h | .lam .., _, _, h | .letE .., _, _, h | .lit _, _, _, h
  | .proj .., _, _, h => by simp [arityShape] at h

/-- The number of arguments of an application. -/
theorem getAppNumArgs_app (f a : Expr) : (Expr.app f a).getAppNumArgs = f.getAppNumArgs + 1 := by
  obtain ⟨g, hg, happ, hother⟩ : ∃ g : Expr → Nat → Nat, (∀ e, e.getAppNumArgs = g e 0) ∧
      (∀ f a n, g (.app f a) n = g f (n + 1)) ∧ (∀ e n, (∀ f a, e ≠ .app f a) → g e n = n) :=
    ⟨_, Expr.getAppNumArgs.eq_1, fun _ _ _ => rfl,
      fun e n h => by cases e <;> first | rfl | exact absurd rfl (h _ _)⟩
  have key : ∀ e n, g e (n + 1) = g e n + 1 := by
    intro e
    induction e with
    | app f b ihf _ => intro n; rw [happ, happ, ihf]
    | _ => intro n; rw [hother _ _ (fun _ _ h => by cases h), hother _ _ (fun _ _ h => by cases h)]
  rw [hg, hg, happ, key]

theorem ConstSpine.of_getAppFn : ∀ {e : Expr} {h : Name} {us : List Level},
    e.getAppFn = .const h us → ConstSpine h us e.getAppNumArgs e
  | .const _ _, h, us, H => by
    simp only [Expr.getAppFn, Expr.const.injEq] at H; obtain ⟨rfl, rfl⟩ := H; exact .const
  | .app f a, h, us, H => by
    simp only [Expr.getAppFn] at H
    rw [getAppNumArgs_app]; exact .app (of_getAppFn H)
  | .bvar _, _, _, H | .fvar _, _, _, H | .mvar _, _, _, H | .sort _, _, _, H | .lam .., _, _, H
  | .forallE .., _, _, H | .letE .., _, _, H | .lit _, _, _, H | .mdata .., _, _, H
  | .proj .., _, _, H => by simp [Expr.getAppFn] at H

theorem PropShape.of_evidentProp_tail {D : List ConstantInfo} {e : Expr}
    (hnf : ∀ n t b bi, e = Expr.forallE n t b bi → False)
    (hnm : ∀ m x, e = Expr.mdata m x → False) (H : EvidentProp D e = true) : PropShape D e := by
  rw [EvidentProp.eq_3 D e hnf hnm] at H
  split at H
  next h us hfn =>
    split at H
    next ci hci =>
      simp only [Bool.and_eq_true] at H
      obtain ⟨hdf, H⟩ := H
      split at H
      next n u hsh =>
        simp only [Bool.and_eq_true, beq_iff_eq] at H
        obtain ⟨rfl, hz⟩ := H
        exact .tail hci hdf hsh hz (ConstSpine.of_getAppFn hfn)
      next => cases H
    next => cases H
  next => cases H

theorem PropShape.of_evidentProp {D : List ConstantInfo} (T : Expr) (H : EvidentProp D T = true) :
    PropShape D T := by
  induction T with
  | forallE n t b bi _ ihb => simp only [EvidentProp] at H; exact .forallE (ihb H)
  | mdata m e ih => simp only [EvidentProp] at H; exact .mdata (ih H)
  | _ => exact of_evidentProp_tail (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) H

/-! ## Levels -/

theorem EvidentZero.instLevel {ps : List Name} {us : List Level} :
    ∀ {u : Level}, EvidentZero u = true → EvidentZero (Pure.instLevel ps us u) = true
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true, Pure.instLevel] at h ⊢
    exact ⟨EvidentZero.instLevel h.1, EvidentZero.instLevel h.2⟩
  | .imax a b, h => by
    simp only [EvidentZero, Pure.instLevel] at h ⊢; exact EvidentZero.instLevel h
  | .succ _, h | .param _, h | .mvar _, h => by simp [EvidentZero] at h

theorem find?_zip_map {g : Level → Level} {n : Name} :
    ∀ (qs : List Name) (vs : List Level),
      (qs.zip (vs.map g)).find? (·.1 == n) =
        ((qs.zip vs).find? (·.1 == n)).map fun p => (p.1, g p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | q :: qs, v :: vs => by
    simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
    cases (q == n) with
    | true => rfl
    | false => exact find?_zip_map qs vs

theorem EvidentZero.instLevel_map {qs ps : List Name} {vs us : List Level} :
    ∀ {u : Level}, EvidentZero (Pure.instLevel qs vs u) = true →
      EvidentZero (Pure.instLevel qs (vs.map (Pure.instLevel ps us)) u) = true
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true, Pure.instLevel] at h ⊢
    exact ⟨EvidentZero.instLevel_map h.1, EvidentZero.instLevel_map h.2⟩
  | .imax a b, h => by
    simp only [EvidentZero, Pure.instLevel] at h ⊢; exact EvidentZero.instLevel_map h
  | .succ _, h | .mvar _, h => by simp [EvidentZero, Pure.instLevel] at h
  | .param n, h => by
    simp only [Pure.instLevel] at h ⊢
    rw [find?_zip_map]
    cases hf : (qs.zip vs).find? (·.1 == n) with
    | none => rw [hf] at h; simp [EvidentZero] at h
    | some p => rw [hf] at h; exact EvidentZero.instLevel h

/-! ## Stability under the oracle's substitutions -/

theorem ArityShape.inst {T a : Expr} {n : Nat} {u : Level} (H : ArityShape T n u) :
    ∀ {d : Nat}, ArityShape (T.instantiate1' a d) n u := by
  induction H with
  | sort => intro d; exact .sort
  | forallE _ ih => intro d; exact .forallE ih
  | mdata _ ih => intro d; exact .mdata ih

theorem ConstSpine.inst {h : Name} {vs : List Level} {k : Nat} {T a : Expr}
    (H : ConstSpine h vs k T) : ∀ {d : Nat}, ConstSpine h vs k (T.instantiate1' a d) := by
  induction H with
  | const => intro d; exact .const
  | app _ ih => intro d; exact .app ih

theorem PropShape.inst {D : List ConstantInfo} {T a : Expr} (H : PropShape D T) :
    ∀ {d : Nat}, PropShape D (T.instantiate1' a d) := by
  induction H with
  | forallE _ ih => intro d; exact .forallE ih
  | mdata _ ih => intro d; exact .mdata ih
  | tail h1 h2 h3 h4 h5 => intro d; exact .tail h1 h2 h3 h4 h5.inst

theorem ArityShape.instLevels {T : Expr} {n : Nat} {u : Level} {ps : List Name} {us : List Level}
    (H : ArityShape T n u) : ArityShape (Pure.instLevels ps us T) n (Pure.instLevel ps us u) := by
  induction H with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih
  | mdata _ ih => exact .mdata ih

theorem ConstSpine.instLevels {h : Name} {vs : List Level} {k : Nat} {T : Expr} {ps : List Name}
    {us : List Level} (H : ConstSpine h vs k T) :
    ConstSpine h (vs.map (Pure.instLevel ps us)) k (Pure.instLevels ps us T) := by
  induction H with
  | const => exact .const
  | app _ ih => exact .app ih

theorem PropShape.instLevels {D : List ConstantInfo} {T : Expr} {ps : List Name}
    {us : List Level} (H : PropShape D T) : PropShape D (Pure.instLevels ps us T) := by
  induction H with
  | forallE _ ih => exact .forallE ih
  | mdata _ ih => exact .mdata ih
  | tail h1 h2 h3 h4 h5 => exact .tail h1 h2 h3 (EvidentZero.instLevel_map h4) h5.instLevels

theorem ConstSpine.ne_mdata {h : Name} {vs : List Level} {k : Nat} {T : Expr}
    (H : ConstSpine h vs k T) : ∀ m e, T ≠ .mdata m e := by
  cases H <;> intro m e h <;> cases h

theorem ConstSpine.ne_lam {h : Name} {vs : List Level} {k : Nat} {T : Expr}
    (H : ConstSpine h vs k T) : ∀ n t b bi, T ≠ .lam n t b bi := by
  cases H <;> intro n t b bi h <;> cases h

theorem ConstSpine.ne_forallE {h : Name} {vs : List Level} {k : Nat} {T : Expr}
    (H : ConstSpine h vs k T) : ∀ n t b bi, T ≠ .forallE n t b bi := by
  cases H <;> intro n t b bi h <;> cases h

/-- The oracle's `spine` of a constant's spine. -/
theorem ConstSpine.spine_eq {h : Name} {vs : List Level} {k : Nat} {T : Expr}
    (H : ConstSpine h vs k T) : ∃ args, Erasure.spine T = (Expr.const h vs, args) := by
  induction H with
  | const => exact ⟨[], rfl⟩
  | @app k f a _ ih =>
    obtain ⟨args, hs⟩ := ih
    exact ⟨args ++ [a], by simp only [Erasure.spine, hs]⟩

/-! ## `whnf` and `inferType` on the shapes -/

theorem throw_ne_ok {α : Type} {e : EraseError} {a : α} :
    (throw e : Except EraseError α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

variable {cx : Pure.Ctx} {ls : List Local}

theorem whnf_sort {f : Nat} {u : Level} : Pure.whnf cx (f + 1) ls (.sort u) = .ok (.sort u) := rfl

theorem whnf_forallE {f : Nat} {nm : Name} {t b : Expr} {bi : BinderInfo} :
    Pure.whnf cx (f + 1) ls (.forallE nm t b bi) = .ok (.forallE nm t b bi) := rfl

theorem whnf_mdata {f : Nat} {m : MData} {e : Expr} :
    Pure.whnf cx (f + 1) ls (.mdata m e) = Pure.whnf cx f ls e := rfl

theorem whnf_const_deltaFree {f : Nat} {h : Name} {us : List Level} {ci : ConstantInfo}
    (hf : findConst cx.decls h = some ci) (hd : DeltaFree ci = true) :
    Pure.whnf cx (f + 1) ls (.const h us) = .ok (.const h us) := by
  cases ci <;> (try simp [DeltaFree] at hd) <;> simp [Pure.whnf, hf, pure, Except.pure]

theorem whnf_arityShape :
    ∀ {f : Nat} {T w : Expr} {n : Nat} {u : Level}, ArityShape T n u →
      Pure.whnf cx f ls T = .ok w → ArityShape w n u ∧ ∀ m e, w ≠ .mdata m e
  | 0, _, _, _, _, _, h => absurd h (by rw [Pure.whnf]; exact throw_ne_ok)
  | f + 1, _, w, _, _, .sort, h => by
    rw [whnf_sort] at h; cases h; exact ⟨.sort, fun _ _ h => by cases h⟩
  | f + 1, _, w, _, _, .forallE H, h => by
    rw [whnf_forallE] at h; cases h; exact ⟨.forallE H, fun _ _ h => by cases h⟩
  | f + 1, _, w, _, _, .mdata H, h => by
    rw [whnf_mdata] at h; exact whnf_arityShape H h

theorem whnf_constSpine {h : Name} {ci : ConstantInfo}
    (hf : findConst cx.decls h = some ci) (hd : DeltaFree ci = true) :
    ∀ {f : Nat} {T w : Expr} {vs : List Level} {k : Nat}, ConstSpine h vs k T →
      Pure.whnf cx f ls T = .ok w → w = T
  | 0, _, _, _, _, _, H => absurd H (by rw [Pure.whnf]; exact throw_ne_ok)
  | f + 1, _, w, _, _, .const, H => by
    rw [whnf_const_deltaFree hf hd] at H; cases H; rfl
  | f + 1, _, w, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.whnf] at H
    obtain ⟨g', h1, h2⟩ := OracleWhnf.ok_of_bind H
    have := whnf_constSpine hf hd hg h1; subst this
    split at h2
    · exact absurd rfl (hg.ne_lam _ _ _ _)
    · cases h2; rfl

theorem whnf_propShape :
    ∀ {f : Nat} {T w : Expr}, PropShape cx.decls T → Pure.whnf cx f ls T = .ok w →
      PropShape cx.decls w ∧ ∀ m e, w ≠ .mdata m e
  | 0, _, _, _, h => absurd h (by rw [Pure.whnf]; exact throw_ne_ok)
  | f + 1, _, w, .forallE H, h => by
    rw [whnf_forallE] at h; cases h; exact ⟨.forallE H, fun _ _ h => by cases h⟩
  | f + 1, _, w, .mdata H, h => by
    rw [whnf_mdata] at h; exact whnf_propShape H h
  | f + 1, _, w, .tail h1 h2 h3 h4 h5, h => by
    have := whnf_constSpine h1 h2 h5 h; subst this
    exact ⟨.tail h1 h2 h3 h4 h5, h5.ne_mdata⟩

theorem inferType_const {f : Nat} {Γ : List Expr} {c : Name} {us : List Level} {S : Expr}
    {ci : ConstantInfo} (hf : findConst cx.decls c = some ci)
    (H : Pure.inferType cx (f + 1) ls Γ (.const c us) = .ok S) :
    S = Pure.instLevels ci.levelParams us ci.type := by
  rw [Pure.inferType, hf] at H
  by_cases hl : (us.length == ci.levelParams.length) = true
  · simp only [hl, ite_true, pure, Except.pure, Except.ok.injEq] at H; exact H.symm
  · simp only [hl] at H; exact absurd H throw_ne_ok

theorem inferType_constSpine_arity {h : Name} {ci : ConstantInfo} {n : Nat} {u0 : Level}
    (hf : findConst cx.decls h = some ci) (ha : arityShape ci.type = some (n, u0)) :
    ∀ {f : Nat} {Γ : List Expr} {T S : Expr} {vs : List Level} {k : Nat}, ConstSpine h vs k T →
      Pure.inferType cx f ls Γ T = .ok S →
      ∃ m, ArityShape S m (Pure.instLevel ci.levelParams vs u0) ∧ m + k = n
  | 0, _, _, _, _, _, _, H => absurd H (by rw [Pure.inferType]; exact throw_ne_ok)
  | f + 1, Γ, _, S, _, _, .const, H => by
    rw [inferType_const hf H]
    exact ⟨n, (ArityShape.of_arityShape ha).instLevels, by omega⟩
  | f + 1, Γ, _, S, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.inferType] at H
    obtain ⟨Tg, h1, H⟩ := OracleWhnf.ok_of_bind H
    obtain ⟨w, h2, H⟩ := OracleWhnf.ok_of_bind H
    obtain ⟨m, has, hm⟩ := inferType_constSpine_arity hf ha hg h1
    obtain ⟨has', -⟩ := whnf_arityShape has h2
    split at H
    · cases H
      cases has' with
      | forallE hB => exact ⟨_, hB.inst, by omega⟩
    · exact absurd H throw_ne_ok

theorem inferType_constSpine_prop {c : Name} {ci : ConstantInfo}
    (hf : findConst cx.decls c = some ci) (hp : PropShape cx.decls ci.type) :
    ∀ {f : Nat} {Γ : List Expr} {T S : Expr} {us : List Level} {k : Nat}, ConstSpine c us k T →
      Pure.inferType cx f ls Γ T = .ok S → PropShape cx.decls S
  | 0, _, _, _, _, _, _, H => absurd H (by rw [Pure.inferType]; exact throw_ne_ok)
  | f + 1, Γ, _, S, _, _, .const, H => by
    rw [inferType_const hf H]; exact hp.instLevels
  | f + 1, Γ, _, S, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.inferType] at H
    obtain ⟨Tg, h1, H⟩ := OracleWhnf.ok_of_bind H
    obtain ⟨w, h2, H⟩ := OracleWhnf.ok_of_bind H
    obtain ⟨hw, -⟩ := whnf_propShape (inferType_constSpine_prop hf hp hg h1) h2
    split at H
    · cases H
      cases hw with
      | forallE hB => exact hB.inst
      | tail _ _ _ _ h5 => exact absurd rfl (h5.ne_forallE _ _ _ _)
    · exact absurd H throw_ne_ok

theorem inferType_propShape :
    ∀ {f : Nat} {Γ : List Expr} {T S : Expr}, PropShape cx.decls T →
      Pure.inferType cx f ls Γ T = .ok S → ∃ lvl, ArityShape S 0 lvl ∧ EvidentZero lvl = true
  | f, Γ, _, S, .tail h1 h2 h3 h4 h5, H => by
    obtain ⟨m, has, hm⟩ := inferType_constSpine_arity h1 h3 h5 H
    exact ⟨_, by rwa [show m = 0 by omega] at has, h4⟩
  | 0, _, _, _, .forallE _, H | 0, _, _, _, .mdata _, H =>
    absurd H (by rw [Pure.inferType]; exact throw_ne_ok)
  | f + 1, Γ, _, S, .mdata H', H => by
    rw [Pure.inferType] at H; exact inferType_propShape H' H
  | f + 1, Γ, _, S, .forallE (b := b) (t := t) H', H => by
    rw [Pure.inferType] at H
    obtain ⟨Tt, -, H⟩ := OracleWhnf.ok_of_bind H
    obtain ⟨w1, -, H⟩ := OracleWhnf.ok_of_bind H
    split at H
    · obtain ⟨Tb, h3, H⟩ := OracleWhnf.ok_of_bind H
      obtain ⟨w2, h4, H⟩ := OracleWhnf.ok_of_bind H
      obtain ⟨lvl, has, hz⟩ := inferType_propShape H' h3
      obtain ⟨has', hnm⟩ := whnf_arityShape has h4
      split at H
      · cases H
        cases has' with
        | sort => exact ⟨_, .sort, by simpa [EvidentZero] using hz⟩
      · cases has' with
        | sort => rename_i hns; exact absurd rfl (hns _)
        | mdata => exact absurd rfl (hnm _ _)
    · exact absurd H throw_ne_ok

theorem isArity_arityShape :
    ∀ {f : Nat} {T : Expr} {b : Bool} {n : Nat} {u : Level}, ArityShape T n u →
      Pure.isArity cx f ls T = .ok b → b = true
  | 0, _, _, _, _, _, h => absurd h (by rw [Pure.isArity]; exact throw_ne_ok)
  | f + 1, T, b, n, u, H, h => by
    rw [Pure.isArity] at h
    obtain ⟨w, h1, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨hw, hnm⟩ := whnf_arityShape H h1
    split at h
    · cases h; rfl
    · cases hw with
      | forallE hB => exact isArity_arityShape hB h
    · next _ hns hnf =>
      cases hw with
      | sort => exact absurd rfl (hns _)
      | forallE => exact absurd rfl (hnf _ _ _ _)
      | mdata => exact absurd rfl (hnm _ _)

theorem alwaysZero_eq : Pure.alwaysZero = EvidentZero := by
  funext u
  induction u with
  | max a b iha ihb => simp only [Pure.alwaysZero, EvidentZero, iha, ihb]
  | imax a b _ ihb => simp only [Pure.alwaysZero, EvidentZero, ihb]
  | zero | succ _ _ | param _ | mvar _ => rfl

theorem AtomSpine.constSpine {σ : EvalEnv} {e : Expr} (H : AtomSpine σ e) :
    ∃ c us k, σ.isAtom c = true ∧ ConstSpine c us k e := by
  induction H with
  | const ha => exact ⟨_, _, 0, ha, .const⟩
  | app _ ih =>
    obtain ⟨c, us, k, ha, hs⟩ := ih
    exact ⟨c, us, k + 1, ha, .app hs⟩

/-- The oracle's steps after its theorem test, on a spine whose head is not a theorem: the
inferred type, the arity test, and otherwise the sort test. -/
theorem isErasable_of_not_thm {fuel : Nat} {e : Expr} {c : Name} {us : List Level} {k : Nat}
    {ci : ConstantInfo} {b : Bool} (hs : ConstSpine c us k e)
    (hf : findConst cx.decls c = some ci) (hnt : IsThm ci = false)
    (h : Pure.isErasable cx fuel ls e = .ok b) :
    ∃ T ba, Pure.inferType cx fuel ls [] e = .ok T ∧ Pure.isArity cx fuel ls T = .ok ba ∧
      (ba = true → b = true) ∧
      (ba = false → ∃ S w, Pure.inferType cx fuel ls [] T = .ok S ∧
        Pure.whnf cx fuel ls S = .ok w ∧
        ((∃ u, w = .sort u ∧ b = Pure.alwaysZero u) ∨ ((∀ u, w ≠ .sort u) ∧ b = false))) := by
  obtain ⟨args, hsp⟩ := hs.spine_eq
  unfold Pure.isErasable at h
  rw [hsp] at h
  cases ci <;> simp [IsThm] at hnt <;> simp only [hf] at h <;>
  · obtain ⟨T, h1, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ba, h2, h⟩ := OracleWhnf.ok_of_bind h
    refine ⟨T, ba, h1, h2, fun hb => ?_, fun hb => ?_⟩
    · subst hb; simpa [pure, Except.pure] using h.symm
    · subst hb
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨S, h3, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨w, h4, h⟩ := OracleWhnf.ok_of_bind h
      refine ⟨S, w, h3, h4, ?_⟩
      split at h
      · exact .inl ⟨_, rfl, by simpa [pure, Except.pure] using h.symm⟩
      · rename_i hns
        exact .inr ⟨fun u hu => hns u hu, by simpa [pure, Except.pure] using h.symm⟩

/-- On a spine whose head is not a theorem and has an evident proposition as its declared type,
the oracle answers `true` or fails: the inferred type is an evident proposition, whose sort is
evidently zero. -/
theorem isErasable_propShape {fuel : Nat} {e : Expr} {c : Name} {us : List Level} {k : Nat}
    {ci : ConstantInfo} {b : Bool} (hs : ConstSpine c us k e)
    (hf : findConst cx.decls c = some ci) (hnt : IsThm ci = false)
    (hp : PropShape cx.decls ci.type) (h : Pure.isErasable cx fuel ls e = .ok b) : b = true := by
  obtain ⟨T, ba, h1, h2, hyes, hno⟩ := isErasable_of_not_thm hs hf hnt h
  have hT := inferType_constSpine_prop hf hp hs h1
  cases ba
  · obtain ⟨S, w, h3, h4, hw⟩ := hno rfl
    obtain ⟨lvl, has, hz⟩ := inferType_propShape hT h3
    obtain ⟨has', hnm⟩ := whnf_arityShape has h4
    rcases hw with ⟨u, rfl, rfl⟩ | ⟨hns, -⟩
    · cases has' with
      | sort => rw [alwaysZero_eq]; exact hz
    · cases has' with
      | sort => exact absurd rfl (hns _)
      | mdata => exact absurd rfl (hnm _ _)
  · exact hyes rfl

/-- A constant applied to a list of arguments is its spine. -/
theorem ConstSpine.mkAppN (c : Name) (us : List Level) (as : List Expr) :
    ConstSpine c us as.length (Lean.mkAppN (.const c us) as.toArray) := by
  rw [mkAppN_toArray]
  suffices ∀ (f : Expr) (k : Nat), ConstSpine c us k f → ∀ as : List Expr,
      ConstSpine c us (k + as.length) (as.foldl .app f) by
    simpa using this _ 0 .const as
  intro f k hf as
  induction as generalizing f k with
  | nil => simpa using hf
  | cons a as ih =>
    have := ih _ _ (ConstSpine.app (a := a) hf)
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

end OracleAtom

open OracleAtom in
/-- On an atom spine the oracle never answers `false` (it may fail): the eraser boxes atoms, for
every list of locals, with no typing hypothesis. A spine headed by a theorem is answered `true` by
the oracle's theorem test; a spine over an evident type former has an arity as its inferred type;
a spine over a proof of an evident proposition has an evident proposition as its inferred type,
whose sort is evidently zero. Reference: none directly; it plays the part of `isErasable` on `tInd`
and on propositional constructors (`MR E/Extract.v:106`); DV-11, DV-24; port of
`L4 Oracle/Atom.lean:165`. -/
theorem Pure.isErasable_atom {cx : Pure.Ctx} {σ : EvalEnv} {e : Expr} {fuel : Nat}
    {ls : List Local} {b : Bool} (hcx : cx.decls = σ.decls) (hsp : AtomSpine σ e)
    (h : Pure.isErasable cx fuel ls e = .ok b) : b = true := by
  obtain ⟨c, us, k, ha, hs⟩ := AtomSpine.constSpine hsp
  simp only [EvalEnv.isAtom] at ha
  split at ha
  · rename_i ci hci
    have hf : findConst cx.decls c = some ci := by rw [hcx]; exact hci
    simp only [Bool.and_eq_true, Bool.or_eq_true] at ha
    obtain ⟨-, hty⟩ := ha
    cases hthm : IsThm ci
    · rcases hty with (hA | hB) | hT
      · obtain ⟨T, ba, h1, h2, hyes, -⟩ := isErasable_of_not_thm hs hf hthm h
        obtain ⟨⟨n, u⟩, hn⟩ := Option.isSome_iff_exists.1 hA
        obtain ⟨m, has, -⟩ := inferType_constSpine_arity hf hn hs h1
        exact hyes (isArity_arityShape has h2)
      · exact isErasable_propShape hs hf hthm (hcx ▸ PropShape.of_evidentProp _ hB) h
      · rw [hthm] at hT; cases hT
    · obtain ⟨args, hspn⟩ := hs.spine_eq
      unfold Pure.isErasable at h
      rw [hspn] at h
      cases ci <;> simp [IsThm] at hthm
      simp only [hf] at h
      simpa [pure, Except.pure] using h.symm
  · cases ha

open OracleAtom in
/-- On a spine of a constructor whose declared type is an evident proposition (the constructor of
an inductive declared in `Prop`, with the type Lean's kernel gives constructors: `Π` binders around
the inductive applied to its parameters and indices), the oracle answers `true` or fails, never
`false`, for every list of locals and without a typing hypothesis: the spine's inferred type is an
evident proposition, whose sort is evidently zero. Reference: `isErasable` on propositional
constructors (`MR E/Extract.v:106 erases_tConstruct`, `~~ isPropositional`); DV-11. -/
theorem Pure.isErasable_ctorProp {cx : Pure.Ctx} {σ : EvalEnv} {c : Name} {cv : ConstructorVal}
    {us : List Level} {as : List Expr} {fuel : Nat} {ls : List Local} {b : Bool}
    (hcx : cx.decls = σ.decls) (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (hp : EvidentProp σ.decls cv.type = true)
    (h : Pure.isErasable cx fuel ls (mkAppN (.const c us) as.toArray) = .ok b) : b = true :=
  isErasable_propShape (ci := .ctorInfo cv) (ConstSpine.mkAppN c us as) (by rw [hcx]; exact hc) rfl
    (hcx ▸ PropShape.of_evidentProp _ hp) h

end EraseProof
