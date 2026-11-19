import EraseProof.Core.Collect

/-!
# What the fragment test's closure satisfies

`collectDeps_spec`: on a program con-leche accepts, read through a view that agrees with it, the
closure that a successful `Erasure.collectDeps` returns for a term con-leche types has distinct
kernames (`KernameInj`) and λ□ block names (`BlockNamesInj`), syntactic arities as inductive types
(`ArityTypes`), holds every constant of the term, and is closed under what the source semantics
and the traversal read (`DepClosed`), when every recursor of the program names the members of its
block in its type. The proof reads the checks of the shipping code: `exprConsts`, `declExclusion`
and `closureStep` on every scanned declaration, `dropKnown` on every read name, and
`findCollision` and `findBlockCollision` on the result. The run of the closure is described
without the program (`closure_ok`: every declaration it holds is the view's, scanned with its
read names in the result); the program enters through the recursors' types. Port of
`ML-V Core/CollectSpec.lean`. Reference: `L4 Core/Collect.lean:214`.
-/

open Lean Erasure

namespace EraseProof

namespace CollectSpec

open CollectSub Restrict

/-! ## Kernames -/

/-- The derived `BEq` of `ModPath` is reflexive. Port of `ML-V Core/CollectSpec.lean:33`. -/
theorem modPath_beq_self : ∀ m : ModPath, instBEqModPath.beq m m = true
  | .MPfile dp => by rw [instBEqModPath.beq.eq_1]; exact beq_self_eq_true dp
  | .MPdot mp id => by
    rw [instBEqModPath.beq.eq_2, modPath_beq_self mp, beq_self_eq_true id]; rfl

/-- The derived `BEq` of `Kername`, which `findCollision` uses, is reflexive. Port of
`ML-V Core/CollectSpec.lean:39`. -/
theorem kername_beq_self (k : Kername) : (k == k) = true := by
  obtain ⟨mp, id⟩ := k
  show instBEqKername.beq _ _ = true
  simp only [instBEqKername.beq]
  show (instBEqModPath.beq mp mp && id == id) = true
  rw [modPath_beq_self, beq_self_eq_true id]; rfl

/-- Without a collision, two declarations of the list with one kername have one name. Port of
`ML-V Core/CollectSpec.lean:48`. -/
theorem findCollision_eq_none : ∀ {decls : List ConstantInfo}, findCollision decls = none →
    ∀ a ∈ decls, ∀ b ∈ decls, toKername a.name = toKername b.name → a.name = b.name
  | [], _, _, ha, _, _, _ => nomatch ha
  | ci :: cs, h, a, ha, b, hb, hk => by
    rw [findCollision.eq_2] at h
    split at h
    · cases h
    · rename_i hfind
      have hne : ∀ d ∈ cs, toKername d.name ≠ toKername ci.name := fun d hd hdk =>
        List.find?_eq_none.mp hfind d hd (by rw [hdk]; exact kername_beq_self _)
      rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
      · rw [ha, hb]
      · rw [ha] at hk; exact absurd hk.symm (hne b hb)
      · rw [hb] at hk; exact absurd hk (hne a ha)
      · exact findCollision_eq_none h a ha b hb hk

/-- `findDecl` finds exactly the names of the list. Port of `ML-V Core/CollectSpec.lean:65`. -/
theorem findDecl_isSome_iff {decls : List ConstantInfo} {c : Name} :
    (findDecl decls c).isSome ↔ c ∈ decls.map (·.name) := by
  simp only [findDecl, List.find?_isSome, beq_iff_eq, List.mem_map]

/-- Declarations without a collision have distinct kernames (DV-14). Port of
`ML-V Core/CollectSpec.lean:70`. -/
theorem KernameInj.of_findCollision {decls : List ConstantInfo} (h : findCollision decls = none) :
    KernameInj decls := by
  intro c₁ c₂ h₁ h₂ hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₁)
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₂)
  exact findCollision_eq_none h a ha b hb hk

/-- Without a block collision, the λ□ block names are distinct and differ from the kernames of
the emitted constants. Port of `ML-V Core/CollectSpec.lean:846`. -/
theorem BlockNamesInj.of_findBlockCollision {decls : List ConstantInfo}
    (h : findBlockCollision decls = none) : BlockNamesInj decls := by
  unfold findBlockCollision at h
  rw [List.findSome?_eq_none_iff] at h
  rintro iv₁ iv₂ ⟨ci₁, hci₁, rfl⟩ ⟨ci₂, hci₂, rfl⟩
  have hn := h iv₁ (List.mem_filterMap.2 ⟨_, hci₁, rfl⟩)
  dsimp only at hn
  generalize hf : List.find? _ _ = o at hn
  cases o with
  | some _ => cases hn
  | none =>
    dsimp only at hn
    rw [Option.map_eq_none_iff] at hn
    rw [List.find?_eq_none] at hn
    refine ⟨fun hk => ?_, fun ci hci hem hk => ?_⟩
    · have := hf
      rw [List.find?_eq_none] at this
      have h2 := this iv₂ (List.mem_filterMap.2 ⟨_, hci₂, rfl⟩)
      rw [hk, kername_beq_self, Bool.true_and] at h2
      exact (by simpa using h2 : iv₂.all = iv₁.all).symm
    · have h3 := hn ci hci
      rw [hk, kername_beq_self, Bool.and_true] at h3
      apply h3
      cases ci <;> simp_all [EmitsConst]

/-! ## Expressions -/

/-- A successful `exprConsts` lists every constant of the term. Port of the first part of
`ML-V Core/CollectSpec.lean:81 exprConsts_ok`. -/
theorem exprConsts_consts {cfg : ErasureConfig} : ∀ {e : Expr} {cs : List Name},
    exprConsts cfg e = .ok cs → ConstsIn (· ∈ cs) e
  | .bvar _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .fvar _, _, h | .mvar _, _, h => by rw [exprConsts] at h; cases h
  | .const c _, cs, h => by
    rw [exprConsts] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h; exact List.mem_singleton_self c
      · cases h; exact List.mem_singleton_self c
  | .app f a, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, hf, h⟩ := ok_of_bind h
    obtain ⟨ys, ha, h⟩ := ok_of_bind h
    cases h
    exact ⟨ConstsIn_mono (fun _ h => List.mem_append_left _ h) (exprConsts_consts hf),
      ConstsIn_mono (fun _ h => List.mem_append_right _ h) (exprConsts_consts ha)⟩
  | .lam _ t b _, cs, h | .forallE _ t b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := ok_of_bind h
    obtain ⟨ys, hb, h⟩ := ok_of_bind h
    cases h
    exact ⟨ConstsIn_mono (fun _ h => List.mem_append_left _ h) (exprConsts_consts ht),
      ConstsIn_mono (fun _ h => List.mem_append_right _ h) (exprConsts_consts hb)⟩
  | .letE _ t v b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := ok_of_bind h
    obtain ⟨ys, hv, h⟩ := ok_of_bind h
    obtain ⟨zs, hb, h⟩ := ok_of_bind h
    cases h
    exact ⟨ConstsIn_mono (fun _ h => by simp [h]) (exprConsts_consts ht),
      ConstsIn_mono (fun _ h => by simp [h]) (exprConsts_consts hv),
      ConstsIn_mono (fun _ h => by simp [h]) (exprConsts_consts hb)⟩
  | .mdata _ e, cs, h => by
    rw [exprConsts] at h
    exact exprConsts_consts (e := e) h
  | .proj S _ e, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, he, h⟩ := ok_of_bind h
    cases h
    exact ⟨List.mem_cons_self, ConstsIn_mono (fun _ h => List.mem_cons_of_mem _ h)
      (exprConsts_consts he)⟩

/-- A name an expression mentions (`mentionsAny`) satisfies every predicate its constants
satisfy. -/
theorem mentionsAny_consts {p : Name → Prop} {n : Name} :
    ∀ {e : Expr}, mentionsAny [n] e = true → ConstsIn p e → p n
  | .const c _, h, hc => by
    simp only [mentionsAny, List.contains_cons, List.contains_nil, Bool.or_false,
      beq_iff_eq] at h
    exact h ▸ hc
  | .app f a, h, hc => by
    simp only [mentionsAny, Bool.or_eq_true] at h
    exact h.elim (mentionsAny_consts · hc.1) (mentionsAny_consts · hc.2)
  | .lam _ t b _, h, hc | .forallE _ t b _, h, hc => by
    simp only [mentionsAny, Bool.or_eq_true] at h
    exact h.elim (mentionsAny_consts · hc.1) (mentionsAny_consts · hc.2)
  | .letE _ t v b _, h, hc => by
    simp only [mentionsAny, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact mentionsAny_consts h hc.1
    · exact mentionsAny_consts h hc.2.1
    · exact mentionsAny_consts h hc.2.2
  | .mdata _ e, h, hc => mentionsAny_consts (e := e) h hc
  | .proj _ _ e, h, hc => mentionsAny_consts (e := e) h hc.2
  | .bvar _, h, _ | .fvar _, h, _ | .mvar _, h, _ | .sort _, h, _ | .lit _, h, _ => nomatch h

/-! ## One step of the closure -/

variable {view : EnvView} {cfg : ErasureConfig}

/-- A singleton lookup through the view. Port of `ML-V Core/CollectSpec.lean:889`. -/
theorem viewFind_of {n : Name} {y : ConstantInfo} (h : view.find? n = some y)
    (hn : y.name = n) : viewFind view n = [y] := by
  unfold viewFind; rw [h]; simp [Option.filter, hn]

/-- The list `recognizeCasesOn` checks. Port of `ML-V Core/CollectSpec.lean:766`. -/
def recogList (view : EnvView) (ci : ConstantInfo) (I : InductiveVal) (R : RecursorVal) :
    List ConstantInfo :=
  ci :: .inductInfo I :: .recInfo R :: I.ctors.flatMap (viewFind view) ++
    R.all.flatMap (viewFind view)

/-- What `recognizeCasesOn` checks: the view's `T` and `T.rec`, and `casesInfo?` on `recogList`.
Port of the forward direction of `ML-V Core/CollectSpec.lean:772 recognize_iff`. -/
theorem recognize_spec {ci : ConstantInfo} {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} (h : recognizeCasesOn view ci = some (I, R, ctors)) :
    ∃ T, ci.name = .str T "casesOn" ∧ viewFind view T = [.inductInfo I] ∧
      viewFind view (mkRecName T) = [.recInfo R] ∧
      ∃ c, casesInfo? (recogList view ci I R) ci.name = some c := by
  unfold recognizeCasesOn at h
  split at h
  next T hT =>
    split at h
    next I' R' hI hR =>
      obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.1 h
      cases heq
      exact ⟨T, hT, hI, hR, c, hc⟩
    next => cases h
  next => cases h

/-- What one step of the closure reads and adds, on a declaration it accepts: the constants of the
type; the block members (but the declaration's own name); a definition's value, unless the view
recognizes it as a `casesOn`, whose inductive is read instead and whose recursor is the companion;
an opaque's value; an inductive's constructors, its sort decided; a constructor's inductive; and
a companion that is the view's recursor. Port of `ML-V Core/CollectSpec.lean:342`, without the
checks on the constructors of a recognized `casesOn` and on the companion's kind. -/
theorem closureStep_spec {ci : ConstantInfo} {ns : List Name} {ro : Option ConstantInfo}
    (h : closureStep view cfg ci = .ok (ns, ro)) :
    (∃ ty, exprConsts cfg ci.type = .ok ty ∧ ∀ n ∈ ty, n ∈ ns) ∧
    (∀ n ∈ ci.all, n ∈ ns ∨ n = ci.name) ∧
    (∀ d, ci = .defnInfo d →
      (recognizeCasesOn view ci = none ∧
        ∃ vs, exprConsts cfg d.value = .ok vs ∧ ∀ n ∈ vs, n ∈ ns) ∨
      ∃ I R ctors, recognizeCasesOn view ci = some (I, R, ctors) ∧ I.name ∈ ns ∧
        ro = some (.recInfo R)) ∧
    (∀ o, ci = .opaqueInfo o → ∃ vs, exprConsts cfg o.value = .ok vs ∧ ∀ n ∈ vs, n ∈ ns) ∧
    (∀ iv, ci = .inductInfo iv → (∀ n ∈ iv.ctors, n ∈ ns) ∧ ∃ b, sortDecided iv = .ok b) ∧
    (∀ cv, ci = .ctorInfo cv → cv.induct ∈ ns) ∧
    (∀ r, ro = some r → ∃ R, r = .recInfo R ∧ view.find? r.name = some r) := by
  have thr : ∀ {α : Type} {e : EraseError} {f : Unit → Except EraseError α} (y : α),
      (throw e >>= f) ≠ .ok y := fun _ h => nomatch h
  unfold closureStep at h
  obtain ⟨u, hu, h⟩ := ok_of_bind h
  obtain ⟨ty, hty, h⟩ := ok_of_bind h
  cases ci with
  | defnInfo d =>
    dsimp only at h
    split at h
    · rename_i I R ctors hrec
      obtain ⟨_, -, h⟩ := ok_of_bind h
      cases h
      refine ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
        fun d' hd => .inr ⟨I, R, ctors, by cases hd; exact hrec, by simp, rfl⟩, nofun, nofun,
        nofun, fun r hr => ⟨R, by cases hr; rfl, ?_⟩⟩
      cases hr
      obtain ⟨T, -, -, hR, -⟩ := recognize_spec hrec
      obtain ⟨hf, hn⟩ := viewFind_eq hR
      exact hn ▸ hf
    · rename_i hrec
      obtain ⟨ps, h⟩ : ∃ ps, (exprConsts cfg d.value >>= fun vs =>
          pure (ty ++ vs ++ ps ++ d.all, none) : Except EraseError _) = .ok (ns, ro) := by
        rcases hp : preDef? view cfg (.defnInfo d) with _ | p <;> rw [hp] at h
        · exact ⟨[], h⟩
        · obtain ⟨ps, -, h⟩ := ok_of_bind h
          exact ⟨ps, h⟩
      obtain ⟨vs, hvs, h⟩ := ok_of_bind h
      cases h
      exact ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
        fun d' hd => .inl ⟨by cases hd; exact hrec, vs, by cases hd; exact hvs,
          fun n hn => by simp [hn]⟩, nofun, nofun, nofun, nofun⟩
  | thmInfo t =>
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
      nofun, nofun, nofun, nofun, nofun⟩
  | opaqueInfo o =>
    obtain ⟨vs, hvs, h⟩ := ok_of_bind h
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
      nofun, fun o' ho => ⟨vs, by cases ho; exact hvs, fun n hn => by simp [hn]⟩, nofun, nofun,
      nofun⟩
  | inductInfo iv =>
    cases h
    rw [declExclusion] at hu
    obtain ⟨-, hu⟩ := ite_ok_else hu thr
    dsimp only at hu
    obtain ⟨-, hu⟩ := ite_ok_else hu thr
    obtain ⟨b, hb, -⟩ := ok_of_bind hu
    refine ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
      nofun, nofun, fun iv' hiv => ⟨fun n hn => by cases hiv; simp [hn], b, by cases hiv; exact hb⟩,
      nofun, fun r hr => ?_⟩
    split at hr
    · rename_i c r' R hc hv
      cases hr
      obtain ⟨hf, hn⟩ := viewFind_eq hv
      exact ⟨R, rfl, hn ▸ hf⟩
    · cases hr
  | ctorInfo cv =>
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp [hn]⟩, fun n hn => .inr (by simpa [ConstantInfo.all] using hn),
      nofun, nofun, nofun,
      fun cv' hcv => by cases hcv; simp, nofun⟩
  | axiomInfo _ | quotInfo _ | recInfo _ =>
    cases h
    exact ⟨⟨_, hty, fun n hn => hn⟩, fun n hn => .inr (by simpa [ConstantInfo.all] using hn),
      nofun, nofun, nofun, nofun, nofun⟩

/-- The sort test on an inductive it accepts reads a syntactic arity. Part of
`ML-V Core/CollectSpec.lean:872 sortDecided_ok`. -/
theorem sortDecided_arity {iv : InductiveVal} {b : Bool} (h : sortDecided iv = .ok b) :
    (arityShape iv.type).isSome := by
  unfold sortDecided at h
  split at h <;> first | (rename_i hs; rw [hs]; rfl) | (rename_i hs _; rw [hs]; rfl) | cases h

/-! ## The closure -/

/-- How a declaration entered the closure: scanned by `closureStep`, with its read names in `C`
and its companion in `l`; or as a companion recursor, with the names of its type in `C`. Port of
`ML-V Core/CollectSpec.lean:452`, without the recognized names and the scanning declaration. -/
def Scanned (view : EnvView) (cfg : ErasureConfig) (C : Name → Prop) (l : List ConstantInfo)
    (ci : ConstantInfo) : Prop :=
  (∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, C n) ∧ ∀ r, ro = some r → r ∈ l) ∨
  ∃ R, ci = .recInfo R ∧ ∃ tys, exprConsts cfg R.type = .ok tys ∧ ∀ n ∈ tys, C n

/-- `Scanned` is monotone in the predicate and the list. Port of
`ML-V Core/CollectSpec.lean:460`. -/
theorem Scanned.mono {C C' : Name → Prop} {l l' : List ConstantInfo} {ci : ConstantInfo}
    (hC : ∀ n, C n → C' n) (hl : ∀ x ∈ l, x ∈ l') (h : Scanned view cfg C l ci) :
    Scanned view cfg C' l' ci := by
  rcases h with ⟨ns, ro, h1, h2, h3⟩ | ⟨R, h1, tys, h2, h3⟩
  · exact .inl ⟨ns, ro, h1, fun n hn => hC n (h2 n hn), fun r hr => hl r (h3 r hr)⟩
  · exact .inr ⟨R, h1, tys, h2, fun n hn => hC n (h3 n hn)⟩

/-- A name `findConst` finds is a name of the list. -/
theorem mem_names {l : List ConstantInfo} {n : Name} {y : ConstantInfo}
    (h : findConst l n = some y) : n ∈ l.map (·.name) :=
  (findDecl_eq_some (l := l) h).2 ▸ List.mem_map_of_mem (findDecl_eq_some (l := l) h).1

/-- `dropKnown` drops a prefix of names of the accumulator. Port of
`ML-V Core/CollectSpec.lean:471`, without the recursor checks. -/
theorem dropKnown_ok {acc : List ConstantInfo} :
    ∀ {todo rest : List Name}, dropKnown view cfg acc todo = .ok rest →
    ∃ pre, todo = pre ++ rest ∧ ∀ m ∈ pre, m ∈ acc.map (·.name)
  | [], rest, h => by rw [dropKnown] at h; cases h; exact ⟨[], rfl, nofun⟩
  | n :: todo, rest, h => by
    rw [dropKnown] at h
    have step : ∀ y, findConst acc n = some y → dropKnown view cfg acc todo = .ok rest →
        ∃ pre, n :: todo = pre ++ rest ∧ ∀ m ∈ pre, m ∈ acc.map (·.name) := by
      intro y hy h
      obtain ⟨pre, hpre, hcov⟩ := dropKnown_ok h
      refine ⟨n :: pre, by rw [hpre]; rfl, fun m hm => ?_⟩
      rcases List.mem_cons.1 hm with rfl | hm
      · exact mem_names hy
      · exact hcov m hm
    split at h
    · rename_i y R hy
      obtain ⟨_, -, h⟩ := ok_of_bind h
      exact step _ hy h
    · rename_i y _ hy
      exact step _ hy h
    · cases h
      exact ⟨[], rfl, nofun⟩

/-- **A run of the closure**, from an accumulator of the view's declarations scanned up to the
work list: its result holds the view's declarations, the accumulator and the work list's names,
and each of its declarations is scanned with its read names in it. Port of
`ML-V Core/CollectSpec.lean:510`, without the program: the view's answers replace the program's
declarations. -/
theorem closure_ok : ∀ {f : Nat} {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name} {res : List ConstantInfo × List Name},
    closure view cfg f todo acc cases = .ok res → (∀ y ∈ acc, view.find? y.name = some y) →
    (∀ ci ∈ acc, Scanned view cfg (fun n => n ∈ acc.map (·.name) ∨ n ∈ todo) acc ci) →
    (∀ y ∈ res.1, view.find? y.name = some y) ∧ (∀ ci ∈ acc, ci ∈ res.1) ∧
      (∀ n ∈ todo, n ∈ res.1.map (·.name)) ∧
      ∀ ci ∈ res.1, Scanned view cfg (· ∈ res.1.map (·.name)) res.1 ci
  | 0, todo, acc, cases, res, h, hvw, hsc => by
    rw [closure] at h
    obtain ⟨todo', hd, h⟩ := ok_of_bind h
    obtain ⟨pre, hpre, hcov⟩ := dropKnown_ok hd
    split at h
    · cases h
      rw [List.append_nil] at hpre
      subst hpre
      exact ⟨hvw, fun _ h => h, hcov, fun ci hci =>
        (hsc ci hci).mono (fun n hn => hn.elim id (hcov n)) (fun _ h => h)⟩
    · cases h
  | f + 1, todo, acc, cases, res, h0, hvw, hsc => by
    rw [closure] at h0
    obtain ⟨todo', hd, h⟩ := ok_of_bind h0
    clear h0
    obtain ⟨pre, hpre, hcov⟩ := dropKnown_ok hd
    cases todo' with
    | nil =>
      cases h
      rw [List.append_nil] at hpre
      subst hpre
      exact ⟨hvw, fun _ h => h, hcov, fun ci hci =>
        (hsc ci hci).mono (fun n hn => hn.elim id (hcov n)) (fun _ h => h)⟩
    | cons n todo'' =>
      subst hpre
      dsimp only at h
      cases hf : view.find? n with
      | none => rw [hf] at h; cases h
      | some ci =>
        rw [hf] at h
        dsimp only at h
        by_cases hname : (ci.name != n) = true
        · rw [ite_eq_left hname] at h; cases h
        rw [ite_eq_right hname] at h
        have hcn : ci.name = n := by simpa using hname
        obtain ⟨⟨ns, ro⟩, hcs, h⟩ := ok_of_bind h
        have hvw1 : ∀ y ∈ ci :: acc, view.find? y.name = some y := by
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · rw [hcn]; exact hf
          · exact hvw y hy
        have sub : ∀ {l : List ConstantInfo}, (∀ x ∈ ci :: acc, x ∈ l) →
            ∀ m ∈ acc.map (·.name), m ∈ l.map (·.name) :=
          fun hl => List.map_subset _ fun x hx => hl x (List.mem_cons_of_mem _ hx)
        have self : ∀ {l : List ConstantInfo}, (∀ x ∈ ci :: acc, x ∈ l) → n ∈ l.map (·.name) :=
          fun hl => hcn ▸ List.mem_map_of_mem (hl ci List.mem_cons_self)
        -- old declarations stay scanned
        have hold : ∀ (todo1 : List Name) (l : List ConstantInfo),
            (∀ m ∈ todo'', m ∈ todo1) → (∀ x ∈ ci :: acc, x ∈ l) →
            ∀ cj ∈ acc, Scanned view cfg (fun m => m ∈ l.map (·.name) ∨ m ∈ todo1) l cj := by
          intro todo1 l ht hl cj hcj
          refine (hsc cj hcj).mono (fun m hm => ?_) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          rcases hm with hm | hm
          · exact .inl (sub hl m hm)
          · simp only [List.mem_append, List.mem_cons] at hm
            rcases hm with hm | rfl | hm
            · exact .inl (sub hl m (hcov m hm))
            · exact .inl (self hl)
            · exact .inr (ht m hm)
        have hpost : ∀ (l : List ConstantInfo), (∀ x ∈ ci :: acc, x ∈ l) →
            (∀ m ∈ todo'', m ∈ l.map (·.name)) → ∀ m ∈ pre ++ n :: todo'', m ∈ l.map (·.name) := by
          intro l hl ht m hm
          simp only [List.mem_append, List.mem_cons] at hm
          rcases hm with hm | rfl | hm
          · exact sub hl m (hcov m hm)
          · exact self hl
          · exact ht m hm
        cases ro with
        | none =>
          obtain ⟨r1, r3, r5, r6⟩ := closure_ok h hvw1 (fun cj hcj => by
            rcases List.mem_cons.1 hcj with rfl | hcj
            · exact .inl ⟨ns, none, hcs, fun m hm => .inr (List.mem_append_left _ hm), nofun⟩
            · exact hold _ _ (fun m hm => List.mem_append_right _ hm) (fun _ h => h) cj hcj)
          exact ⟨r1, fun x hx => r3 x (List.mem_cons_of_mem _ hx),
            hpost _ r3 (fun m hm => r5 m (List.mem_append_right _ hm)), r6⟩
        | some r =>
          obtain ⟨R, rfl, hRv⟩ := (closureStep_spec hcs).2.2.2.2.2.2 _ rfl
          dsimp only at h
          by_cases hfa : (findConst acc (ConstantInfo.recInfo R).name).isSome = true
          · rw [ite_eq_left hfa] at h
            obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hfa
            obtain ⟨hy1, hy2⟩ := findDecl_eq_some (l := acc) hy
            have hyr : y = .recInfo R := by
              have := hvw y hy1
              rw [hy2, hRv] at this
              cases this; rfl
            subst hyr
            obtain ⟨r1, r3, r5, r6⟩ := closure_ok h hvw1 (fun cj hcj => by
              rcases List.mem_cons.1 hcj with rfl | hcj
              · exact .inl ⟨ns, some _, hcs, fun m hm => .inr (List.mem_append_left _ hm),
                  fun r hr => by cases hr; exact List.mem_cons_of_mem _ hy1⟩
              · exact hold _ _ (fun m hm => List.mem_append_right _ hm) (fun _ h => h) cj hcj)
            exact ⟨r1, fun x hx => r3 x (List.mem_cons_of_mem _ hx),
              hpost _ r3 (fun m hm => r5 m (List.mem_append_right _ hm)), r6⟩
          · rw [ite_eq_right hfa] at h
            obtain ⟨tys, htys, h⟩ := ok_of_bind h
            have hl2 : ∀ x ∈ ci :: acc, x ∈ ConstantInfo.recInfo R :: ci :: acc :=
              fun x hx => List.mem_cons_of_mem _ hx
            obtain ⟨r1, r3, r5, r6⟩ := closure_ok h
              (fun y hy => by
                rcases List.mem_cons.1 hy with rfl | hy
                · exact hRv
                · exact hvw1 y hy)
              (fun cj hcj => by
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact .inr ⟨R, rfl, tys, htys, fun m hm => .inr (by simp [hm])⟩
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact .inl ⟨ns, some _, hcs, fun m hm => .inr (by simp [hm]),
                    fun r hr => by cases hr; exact List.mem_cons_self⟩
                · exact hold _ _ (fun m hm => by simp [hm]) hl2 cj hcj)
            exact ⟨r1, fun x hx => r3 x (hl2 x (List.mem_cons_of_mem _ hx)),
              hpost _ (fun x hx => r3 x (hl2 x hx)) (fun m hm => r5 m (by simp [hm])), r6⟩

/-! ## The checks after the closure -/

/-- A successful fragment test ran the closure from the term's constants, and found no
collision. Port of `ML-V Core/CollectSpec.lean:802`, without `eliminatedUndecided`. -/
theorem collectDeps_ok {e : Expr} {decls : List ConstantInfo}
    (h : collectDeps view cfg e = .ok decls) :
    ∃ cs cases, exprConsts cfg e = .ok cs ∧
      closure view cfg collectFuel cs [] [] = .ok (decls, cases) ∧
      findCollision decls = none ∧ findBlockCollision decls = none := by
  unfold collectDeps at h
  obtain ⟨cs, hcs, h⟩ := ok_of_bind h
  obtain ⟨⟨ds, cases⟩, hcl, h⟩ := ok_of_bind h
  have key : ∀ x, (match findCollision ds with
      | some (a, b) => (throw (EraseError.nameCollision a b) : Except EraseError _)
      | none => match findBlockCollision ds with
        | some (a, b) => throw (EraseError.nameCollision a b)
        | none => pure ds) = .ok x →
      ∃ cs' cases', exprConsts cfg e = .ok cs' ∧
        closure view cfg collectFuel cs' [] [] = .ok (x, cases') ∧
        findCollision x = none ∧ findBlockCollision x = none := by
    intro x hx
    cases hc : findCollision ds with
    | some p => rw [hc] at hx; cases hx
    | none =>
      rw [hc] at hx
      cases hb : findBlockCollision ds with
      | some p => rw [hb] at hx; cases hx
      | none => rw [hb] at hx; cases hx; exact ⟨cs, cases, hcs, hcl, hc, hb⟩
  dsimp only at h
  cases he : eliminatedUndecided ds cases with
  | some n => rw [he] at h; cases h
  | none =>
    rw [he] at h
    dsimp only at h
    split at h
    · split at h
      · cases h
      · exact key _ h
    · exact key _ h

/-! ## The `casesOn` recognizer on the closure -/

/-- Two lists of the view's declarations agree on the names they both have. Port of
`ML-V Core/CollectSpec.lean:751`. -/
theorem findConst_agree {l₁ l₂ : List ConstantInfo}
    (h₁ : ∀ y ∈ l₁, view.find? y.name = some y) (h₂ : ∀ y ∈ l₂, view.find? y.name = some y)
    {x : Name} (hx₁ : x ∈ l₁.map (·.name)) (hx₂ : x ∈ l₂.map (·.name)) :
    findConst l₂ x = findConst l₁ x := by
  obtain ⟨y₁, hy₁⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 hx₁)
  obtain ⟨y₂, hy₂⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 hx₂)
  obtain ⟨m₁, n₁⟩ := findDecl_eq_some hy₁
  obtain ⟨m₂, n₂⟩ := findDecl_eq_some hy₂
  have e₁ := h₁ y₁ m₁
  have e₂ := h₂ y₂ m₂
  rw [n₁] at e₁; rw [n₂, e₁] at e₂
  cases e₂
  exact hy₂.trans hy₁.symm

/-- The declaration of a list of the view's declarations under a name of the list is the view's. -/
theorem mem_of_view {l : List ConstantInfo} (hvw : ∀ y ∈ l, view.find? y.name = some y)
    {n : Name} {y : ConstantInfo} (hn : n ∈ l.map (·.name)) (hf : view.find? n = some y) :
    y ∈ l := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hn
  rw [hvw z hz] at hf
  cases hf; exact hz

/-- **A `casesOn` the view recognizes is recognized on a list of the view's declarations** that
holds it, its inductive, its recursor, the inductive's constructors and the recursor's block: the
recognizer's lookups agree on the two lists. Part of `ML-V Core/CollectSpec.lean:1125
Run.recog_ds`. -/
theorem recog_cases {decls : List ConstantInfo} (hvw : ∀ y ∈ decls, view.find? y.name = some y)
    {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal} {ctors : List ConstantInfo}
    (hd : .defnInfo d ∈ decls) (hrec : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors))
    (hin : ∀ x, x = I.name ∨ x = R.name ∨ x ∈ I.ctors ∨ x ∈ R.all → x ∈ decls.map (·.name)) :
    (casesOnOf? decls d.name).isSome := by
  obtain ⟨T, hT, hI, hR, c, hc⟩ := recognize_spec hrec
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  have hdsv : ∀ y ∈ recogList view (.defnInfo d) I R, view.find? y.name = some y := by
    intro y hy
    simp only [recogList, List.cons_append, List.mem_cons, List.mem_append,
      List.mem_flatMap] at hy
    rcases hy with rfl | rfl | rfl | ⟨x, -, hx⟩ | ⟨x, -, hx⟩
    · exact hvw _ hd
    · rw [hIn]; exact hIf
    · rw [hRn]; exact hRf
    · rw [(viewFind_mem hx).2]; exact (viewFind_mem hx).1
    · rw [(viewFind_mem hx).2]; exact (viewFind_mem hx).1
  -- the names the recognizer reads are names of both lists
  have flat : ∀ {l : List Name} {x : Name}, x ∈ l → x ∈ decls.map (·.name) →
      ∃ y ∈ l.flatMap (viewFind view), y.name = x := by
    intro l x hx hxd
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxd
    exact ⟨y, List.mem_flatMap.2 ⟨_, hx, by
      rw [viewFind_of (hvw y hy) rfl]; exact List.mem_singleton_self _⟩, rfl⟩
  have both : ∀ x, x = d.name ∨ x = T ∨ x = mkRecName T ∨ x ∈ I.ctors ∨ x ∈ R.all →
      findDecl decls x = findDecl (recogList view (.defnInfo d) I R) x := by
    intro x hx
    have hxd : x ∈ decls.map (·.name) := by
      rcases hx with rfl | rfl | rfl | hx | hx
      · exact List.mem_map_of_mem (f := ConstantInfo.name) hd
      · exact hin _ (.inl hIn.symm)
      · exact hin _ (.inr (.inl hRn.symm))
      · exact hin _ (.inr (.inr (.inl hx)))
      · exact hin _ (.inr (.inr (.inr hx)))
    refine findConst_agree hdsv hvw ?_ hxd
    rcases hx with rfl | rfl | rfl | hx | hx
    · exact List.mem_map_of_mem (f := ConstantInfo.name) (a := .defnInfo d)
        (List.mem_append_left _ List.mem_cons_self)
    · exact hIn ▸ List.mem_map_of_mem (f := ConstantInfo.name) (a := .inductInfo I)
        (by simp [recogList])
    · exact hRn ▸ List.mem_map_of_mem (f := ConstantInfo.name) (a := .recInfo R)
        (by simp [recogList])
    · obtain ⟨y, hy, rfl⟩ := flat hx hxd
      exact List.mem_map_of_mem (f := ConstantInfo.name) (a := y) (by simp [recogList, hy])
    · obtain ⟨y, hy, rfl⟩ := flat hx hxd
      exact List.mem_map_of_mem (f := ConstantInfo.name) (a := y) (by simp [recogList, hy])
  have same : ∀ {n : Name} {y z : ConstantInfo},
      findDecl (recogList view (.defnInfo d) I R) n = some y → view.find? n = some z → y = z := by
    intro n y z hy hz
    obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
    rw [← hy2, hdsv y hy1] at hz
    cases hz; rfl
  have hT' : d.name = .str T "casesOn" := hT
  have hc' : casesInfo? decls d.name = some c := by
    rw [casesInfo?_congr (D := decls) (P := recogList view (.defnInfo d) I R)
      (both _ (.inl rfl)) fun T' hT'' => ?_]
    · exact hc
    rw [hT', Name.str.injEq] at hT''
    obtain ⟨rfl, -⟩ := hT''
    refine ⟨both _ (.inr (.inl rfl)), both _ (.inr (.inr (.inl rfl))),
      fun I'' R'' hI'' hR'' => ?_⟩
    cases same hI'' hIf
    cases same hR'' hRf
    exact ⟨fun x hx => both x (.inr (.inr (.inr (.inl hx)))),
      fun x hx => both x (.inr (.inr (.inr (.inr hx))))⟩
  obtain ⟨T₀, -, I₀, -, -, -, -, hn, hind, -, hI₀, -⟩ := casesInfo?_reads hc
  have hTT : T₀ = T := by
    have h2 : Name.str T "casesOn" = Name.str T₀ "casesOn" := hT'.symm.trans hn
    rw [Name.str.injEq] at h2
    exact h2.1.symm
  subst hTT
  unfold casesOnOf?
  rw [hc']
  dsimp only
  rw [hind, both _ (.inr (.inl rfl)), hI₀]
  rfl

end CollectSpec

open CollectSub CollectSpec Restrict in
/-- **What the fragment test's closure satisfies**: on a program con-leche accepts, read through a
view that agrees with it, the closure that a successful `Erasure.collectDeps` returns for a term
con-leche types has distinct kernames (DV-14) and λ□ block names, syntactic arities as inductive
types, holds the constants of the term and is closed under what the source semantics and the
traversal read (`DepClosed`). The hypothesis `hrecs`: the type of every recursor of the program
names each member of its block, as the recursors Lean's kernel generates do (each member is the
domain of a motive's major premise); `DeclsOf?` does not check it, and the fragment test reads a
recursor's block only through its type. Port of `ML-V Core/CollectSpec.lean:1422`
(`L4 Core/Collect.lean:214`), with con-leche's acceptance where that file has Metalean's
`ProgEnv`. Reference: the closure property of `MR E/ErasureFunction.v:1602 erase_global_deps`. -/
theorem collectDeps_spec {P decls : List ConstantInfo} {env : ConLeche.Env} {e : Expr}
    {view : EnvView} {cfg : ErasureConfig} (hP : ConLecheAccepts P env)
    (hview : ViewAgrees view P) (hty : CLTyped env e)
    (hrecs : ∀ R, .recInfo R ∈ P → ∀ n ∈ R.all, mentionsAny [n] R.type = true)
    (h : collectDeps view cfg e = .ok decls) :
    KernameInj decls ∧ DepClosed decls ∧ ConstsIn (fun c => (findDecl decls c).isSome) e ∧
      BlockNamesInj decls ∧ ArityTypes decls := by
  obtain ⟨cs, cases, hcs, hcl, hcol, hbc⟩ := CollectSpec.collectDeps_ok h
  have hsub : ∀ ci ∈ decls, ci ∈ P :=
    closure_sub hP hview hcl nofun (KnownIn.exprConsts (CLTyped.knownIn hP hty) hcs)
  obtain ⟨hvw, -, hcov, hscan⟩ := closure_ok hcl nofun nofun
  have inD : ∀ {n}, n ∈ decls.map (·.name) → (findDecl decls n).isSome = true :=
    fun h => findDecl_isSome_iff.2 h
  have htype : ∀ ci ∈ decls, ∃ tys, exprConsts cfg ci.type = .ok tys ∧
      ∀ n ∈ tys, n ∈ decls.map (·.name) := by
    intro ci hci
    rcases hscan ci hci with ⟨ns, ro, hcs', hns, -⟩ | ⟨R, rfl, tys, htys, hc⟩
    · obtain ⟨ty, hty', hsub'⟩ := (closureStep_spec hcs').1
      exact ⟨ty, hty', fun n hn => hns n (hsub' n hn)⟩
    · exact ⟨tys, htys, hc⟩
  have hscanned : ∀ ci ∈ decls, (∀ R, ci ≠ .recInfo R) → ∃ ns ro,
      closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, n ∈ decls.map (·.name)) ∧
      ∀ r, ro = some r → r ∈ decls := by
    intro ci hci hnr
    rcases hscan ci hci with h | ⟨R, rfl, -⟩
    · exact h
    · exact absurd rfl (hnr R)
  have hrall : ∀ R, .recInfo R ∈ decls → ∀ n ∈ R.all, n ∈ decls.map (·.name) := by
    intro R hR n hn
    obtain ⟨tys, htys, hc⟩ := htype _ hR
    exact hc n (mentionsAny_consts (hrecs R (hsub _ hR) n hn) (exprConsts_consts htys))
  have hind : ∀ iv, .inductInfo iv ∈ decls →
      (∀ n ∈ iv.ctors, n ∈ decls.map (·.name)) ∧ ∃ b, sortDecided iv = .ok b := by
    intro iv hiv
    obtain ⟨ns, ro, hcs', hns, -⟩ := hscanned _ hiv nofun
    obtain ⟨hc, b, hb⟩ := (closureStep_spec hcs').2.2.2.2.1 iv rfl
    exact ⟨fun n hn => hns n (hc n hn), b, hb⟩
  have hdep : DepClosed decls := by
    intro ci hci
    refine ⟨fun x hx => ?_, fun n hn => ?_, fun iv hiv n hn => ?_, fun cv hcv => ?_,
      fun R hR n hn => ?_⟩
    · rcases hx with rfl | ⟨d, rfl, rfl, hnone⟩ | ⟨o, rfl, rfl⟩
      · obtain ⟨tys, htys, hc⟩ := htype _ hci
        exact ConstsIn_mono (fun c h => inD (hc c h)) (exprConsts_consts htys)
      · obtain ⟨ns, ro, hcs', hns, hro⟩ := hscanned _ hci nofun
        rcases (closureStep_spec hcs').2.2.1 d rfl with ⟨-, vs, hvs, hsub'⟩ |
          ⟨I, R, ctors, hrec, hIns, hro'⟩
        · exact ConstsIn_mono (fun c h => inD (hns c (hsub' c h))) (exprConsts_consts hvs)
        · -- a `casesOn` the view recognizes is recognized on the closure, whose value is not read
          have hRd := hro _ hro'
          obtain ⟨T, -, hI, -⟩ := recognize_spec hrec
          obtain ⟨hIf, hIn⟩ := viewFind_eq hI
          have hId : .inductInfo I ∈ decls :=
            mem_of_view hvw (hns _ hIns) (by rw [← hIn] at hIf; exact hIf)
          have hrc := recog_cases hvw hci hrec fun x hx => by
            rcases hx with rfl | rfl | hx | hx
            · exact hns _ hIns
            · exact List.mem_map_of_mem (f := ConstantInfo.name) hRd
            · exact (hind _ hId).1 x hx
            · exact hrall _ hRd x hx
          rw [Option.isNone_iff_eq_none] at hnone
          rw [hnone] at hrc
          cases hrc
      · obtain ⟨ns, ro, hcs', hns, -⟩ := hscanned _ hci nofun
        obtain ⟨vs, hvs, hsub'⟩ := (closureStep_spec hcs').2.2.2.1 o rfl
        exact ConstsIn_mono (fun c h => inD (hns c (hsub' c h))) (exprConsts_consts hvs)
    · have hself : ci.name ∈ decls.map (·.name) := List.mem_map_of_mem hci
      rcases hscan ci hci with ⟨ns, ro, hcs', hns, -⟩ | ⟨R, rfl, -⟩
      · rcases (closureStep_spec hcs').2.1 n hn with h | h
        · exact inD (hns n h)
        · exact inD (h ▸ hself)
      · simp only [ConstantInfo.all, List.mem_singleton] at hn
        exact inD (hn ▸ hself)
    · subst hiv; exact inD ((hind _ hci).1 n hn)
    · subst hcv
      obtain ⟨ns, ro, hcs', hns, -⟩ := hscanned _ hci nofun
      exact inD (hns _ ((closureStep_spec hcs').2.2.2.2.2.1 cv rfl))
    · subst hR; exact inD (hrall _ hci n hn)
  exact ⟨KernameInj.of_findCollision hcol, hdep,
    ConstsIn_mono (fun c h => inD (hcov c h)) (exprConsts_consts hcs),
    BlockNamesInj.of_findBlockCollision hbc, fun iv ⟨ci, hci, he⟩ => by
      subst he
      obtain ⟨-, b, hb⟩ := hind _ hci
      exact sortDecided_arity hb⟩

end EraseProof
