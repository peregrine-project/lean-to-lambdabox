import EraseProof.Core.Collect
import EraseProof.Oracle.Agree

/-!
# What the fragment test guarantees

`collectDeps_spec`: on a program related to a Metalean environment and read through a view that
agrees with it, the closure that a successful `Erasure.collectDeps` returns has distinct names and
kernames, holds the view's declarations, is closed under what the pure traversal reads, reads only
closed expressions, holds every constant of the term, keeps every declaration inside the
first-phase fragment (`PhaseIDecl`), reads no recursor (`RecFree`), and its inductive blocks have
distinct λ□ names (`BlockNamesInj`) and syntactic arities as types (`ArityTypes`). The proof reads
the checks of the shipping code: `exprConsts`, `declExclusion` and `closureStep` on every scanned
declaration, `dropKnown` on every read name, and `eliminatedUndecided`, `findCollision` and
`findBlockCollision` on the result. Reference: `L4 Core/Collect.lean:214`.
-/

open Lean Erasure

namespace EraseProof

namespace CollectSpec

open NonRec Extend CasesShape CollectSub

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-! ## Kernames -/

theorem modPath_beq_self : ∀ m : ModPath, instBEqModPath.beq m m = true
  | .MPfile dp => by rw [instBEqModPath.beq.eq_1]; exact beq_self_eq_true dp
  | .MPdot mp id => by
    rw [instBEqModPath.beq.eq_2, modPath_beq_self mp, beq_self_eq_true id]; rfl

/-- The derived `BEq` of `Kername`, which `findCollision` uses, is reflexive. -/
theorem kername_beq_self (k : Kername) : (k == k) = true := by
  obtain ⟨mp, id⟩ := k
  show instBEqKername.beq _ _ = true
  simp only [instBEqKername.beq]
  show (instBEqModPath.beq mp mp && id == id) = true
  rw [modPath_beq_self, beq_self_eq_true id]; rfl

/-- Without a collision, two declarations of the list with one kername have one name (port of
`L4 Core/Collect.lean`). -/
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

/-- `findDecl` finds exactly the names of the list. -/
theorem findDecl_isSome_iff {decls : List ConstantInfo} {c : Name} :
    (findDecl decls c).isSome ↔ c ∈ decls.map (·.name) := by
  simp only [findDecl, List.find?_isSome, beq_iff_eq, List.mem_map]

/-- Declarations without a collision have distinct kernames (DV-14). -/
theorem KernameInj.of_findCollision {decls : List ConstantInfo} (h : findCollision decls = none) :
    KernameInj decls := by
  intro c₁ c₂ h₁ h₂ hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₁)
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₂)
  exact findCollision_eq_none h a ha b hb hk

/-! ## Expressions -/

/-- A successful `exprConsts` lists every constant of the term (and `Nat` for a Nat literal), and
the term has no free variable. -/
theorem exprConsts_ok {cfg : ErasureConfig} : ∀ {e : Expr} {cs : List Name},
    exprConsts cfg e = .ok cs →
    ConstsIn (· ∈ cs) e ∧ (HasNatLit e = true → ``Nat ∈ cs) ∧ FVarsIn (fun _ => False) e
  | .bvar _, cs, h => by rw [exprConsts] at h; cases h; exact ⟨trivial, by simp [HasNatLit], trivial⟩
  | .fvar _, _, h | .mvar _, _, h => by rw [exprConsts] at h; cases h
  | .sort _, cs, h => by
    rw [exprConsts] at h
    split at h
    · cases h
    · cases h; exact ⟨trivial, by simp [HasNatLit], trivial⟩
  | .const c _, cs, h => by
    rw [exprConsts] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h; exact ⟨List.mem_singleton_self c, by simp [HasNatLit], trivial⟩
      · cases h; exact ⟨List.mem_singleton_self c, by simp [HasNatLit], trivial⟩
  | .app f a, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, hf, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, ha, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    obtain ⟨c1, n1, f1⟩ := exprConsts_ok hf
    obtain ⟨c2, n2, f2⟩ := exprConsts_ok ha
    refine ⟨⟨ConstsIn_mono (fun _ h => List.mem_append_left _ h) c1,
      ConstsIn_mono (fun _ h => List.mem_append_right _ h) c2⟩, fun hn => ?_, f1, f2⟩
    simp only [HasNatLit, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact List.mem_append_left _ (n1 hn)
    · exact List.mem_append_right _ (n2 hn)
  | .lam _ t b _, cs, h | .forallE _ t b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hb, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    obtain ⟨c1, n1, f1⟩ := exprConsts_ok ht
    obtain ⟨c2, n2, f2⟩ := exprConsts_ok hb
    refine ⟨⟨ConstsIn_mono (fun _ h => List.mem_append_left _ h) c1,
      ConstsIn_mono (fun _ h => List.mem_append_right _ h) c2⟩, fun hn => ?_, f1, f2⟩
    simp only [HasNatLit, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact List.mem_append_left _ (n1 hn)
    · exact List.mem_append_right _ (n2 hn)
  | .letE _ t v b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hv, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨zs, hb, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    obtain ⟨c1, n1, f1⟩ := exprConsts_ok ht
    obtain ⟨c2, n2, f2⟩ := exprConsts_ok hv
    obtain ⟨c3, n3, f3⟩ := exprConsts_ok hb
    refine ⟨⟨ConstsIn_mono (fun _ h => by simp [h]) c1, ConstsIn_mono (fun _ h => by simp [h]) c2,
      ConstsIn_mono (fun _ h => by simp [h]) c3⟩, fun hn => ?_, f1, f2, f3⟩
    simp only [HasNatLit, Bool.or_eq_true] at hn
    rcases hn with (hn | hn) | hn
    · simp [n1 hn]
    · simp [n2 hn]
    · simp [n3 hn]
  | .lit (.natVal _), cs, h => by
    rw [exprConsts] at h
    split at h
    · cases h
    · cases h; exact ⟨trivial, fun _ => List.mem_singleton_self _, trivial⟩
  | .lit (.strVal _), _, h => by rw [exprConsts] at h; cases h
  | .mdata _ e, cs, h => by
    rw [exprConsts] at h
    exact exprConsts_ok (e := e) h
  | .proj S _ e, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, he, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    obtain ⟨c1, n1, f1⟩ := exprConsts_ok he
    exact ⟨⟨List.mem_cons_self, ConstsIn_mono (fun _ h => List.mem_cons_of_mem _ h) c1⟩,
      fun hn => List.mem_cons_of_mem _ (n1 hn), f1⟩

/-! ## One step of the closure -/

theorem ite_ok_then {ε α : Type} {c : Prop} [Decidable c] {a b : Except ε α} {x : α}
    (h : (if c then a else b) = .ok x) (hb : ∀ y, b ≠ .ok y) : c ∧ a = .ok x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h; exact absurd h (hb x)

/-- A successful `if` whose then branch fails took its else branch. -/
theorem ite_ok_else {ε α : Type} {c : Prop} [Decidable c] {a b : Except ε α} {x : α}
    (h : (if c then a else b) = .ok x) (ha : ∀ y, a ≠ .ok y) : ¬ c ∧ b = .ok x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact absurd h (ha x)
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

/-- An option that is not `some` is `none`. -/
theorem not_isSome {α : Type} {o : Option α} (h : ¬ o.isSome = true) : o = none := by
  cases o <;> simp_all

/-- The checks `declExclusion` makes, on a declaration it accepts. -/
theorem declExclusion_ok {view : EnvView} {cfg : ErasureConfig} {ci : ConstantInfo} {u : Unit}
    (h : declExclusion view cfg ci = .ok u) :
    (∀ R, ci ≠ .recInfo R) ∧ (∀ q, ci ≠ .quotInfo q) ∧
    (∀ d, ci = .defnInfo d → d.safety = .safe ∧
      view.find? (Compiler.mkUnsafeRecName d.name) = none ∧ view.implementedBy? d.name = none) ∧
    (∀ o, ci = .opaqueInfo o → o.isUnsafe = false ∧
      view.find? (Compiler.mkUnsafeRecName o.name) = none ∧ view.implementedBy? o.name = none) ∧
    (∀ a, ci = .axiomInfo a → a.isUnsafe = false ∧ view.implementedBy? a.name = none) ∧
    (∀ iv, ci = .inductInfo iv → iv.isUnsafe = false ∧ iv.numNested = 0 ∧
      ∃ b, sortDecided iv = .ok b) ∧
    (∀ cv, ci = .ctorInfo cv → cv.isUnsafe = false ∧
      (cfg.1 = .preferAxiom → view.isExtern cv.name = false)) := by
  have thr : ∀ {α : Type} {e : EraseError} {f : Unit → Except EraseError α} (y : α),
      (throw e >>= f) ≠ .ok y := fun _ h => nomatch h
  have thr' : ∀ {α : Type} {e : EraseError} (y : α), (throw e : Except EraseError α) ≠ .ok y :=
    fun _ h => nomatch h
  cases ci with
  | quotInfo q => rw [declExclusion] at h; cases h
  | recInfo r => rw [declExclusion] at h; cases h
  | thmInfo t => exact ⟨nofun, nofun, nofun, nofun, nofun, nofun, nofun⟩
  | defnInfo d =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, fun d' hd => ?_, nofun, nofun, nofun, nofun⟩
    cases hd
    obtain ⟨h1, h⟩ := ite_ok_then h thr
    dsimp only at h
    obtain ⟨h2, h⟩ := ite_ok_else h thr
    obtain ⟨h3, -⟩ := ite_ok_else h thr'
    refine ⟨?_, not_isSome h2, not_isSome h3⟩
    revert h1; cases d.safety <;> simp
  | opaqueInfo o =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, nofun, fun o' ho => ?_, nofun, nofun, nofun⟩
    cases ho
    obtain ⟨h1, h⟩ := ite_ok_else h thr
    dsimp only at h
    obtain ⟨h2, h⟩ := ite_ok_else h thr
    obtain ⟨h3, -⟩ := ite_ok_else h thr'
    exact ⟨by simpa using h1, not_isSome h2, not_isSome h3⟩
  | axiomInfo a =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, nofun, nofun, fun a' ha => ?_, nofun, nofun⟩
    cases ha
    obtain ⟨h1, h⟩ := ite_ok_else h thr
    dsimp only at h
    obtain ⟨h3, -⟩ := ite_ok_else h thr'
    exact ⟨by simpa using h1, not_isSome h3⟩
  | inductInfo iv =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, nofun, nofun, nofun, fun iv' hiv => ?_, nofun⟩
    cases hiv
    obtain ⟨h1, h⟩ := ite_ok_else h thr
    dsimp only at h
    obtain ⟨h2, h⟩ := ite_ok_else h thr
    obtain ⟨b, hb, -⟩ := OracleWhnf.ok_of_bind h
    exact ⟨by simpa using h1, by simpa using h2, b, hb⟩
  | ctorInfo cv =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, nofun, nofun, nofun, nofun, fun cv' hcv => ?_⟩
    cases hcv
    obtain ⟨h1, h⟩ := ite_ok_else h thr
    dsimp only at h
    obtain ⟨h2, -⟩ := ite_ok_else h thr'
    refine ⟨by simpa using h1, fun hp => ?_⟩
    simp only [Bool.and_eq_true, not_and] at h2
    exact Bool.eq_false_iff.2 (h2 (by rw [show cfg.1 = _ from hp]; rfl))

/-- A successful `forIn` whose body only yields ran the body successfully on every element. -/
theorem forIn_ok {ε α : Type} {f : α → Unit → Except ε (ForInStep Unit)}
    (hf : ∀ a s, f a () = .ok s → s = .yield ()) :
    ∀ {l : List α} {u : Unit}, forIn l () f = .ok u → ∀ a ∈ l, ∃ s, f a () = .ok s
  | [], _, _, a, ha => nomatch ha
  | b :: l, u, h, a, ha => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := OracleWhnf.ok_of_bind h
    have := hf b s hs
    subst this
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, hs⟩
    · exact forIn_ok hf h a ha

/-- What one step of the closure reads and adds, on a declaration it accepts. -/
theorem closureStep_spec {view : EnvView} {cfg : ErasureConfig} {ci : ConstantInfo}
    {ns : List Name} {ro : Option ConstantInfo} (h : closureStep view cfg ci = .ok (ns, ro)) :
    declExclusion view cfg ci = .ok () ∧
    (∃ ty, exprConsts cfg ci.type = .ok ty ∧ ∀ n ∈ ty, n ∈ ns) ∧
    (∀ n ∈ ci.all, n ∈ ns ∨ n = ci.name) ∧
    (∀ d, ci = .defnInfo d →
      (recognizeCasesOn view ci = none ∧ ro = none ∧
        ∃ vs, exprConsts cfg d.value = .ok vs ∧ ∀ n ∈ vs, n ∈ ns) ∨
      (∃ I R ctors, recognizeCasesOn view ci = some (I, R, ctors) ∧ I.name ∈ ns ∧
        ro = some (.recInfo R) ∧ ∀ c ∈ ctors, ∀ cv, c = .ctorInfo cv →
          (indexFields cv.numParams cv.type).all (·.isNone) = true)) ∧
    (∀ o, ci = .opaqueInfo o → ∃ vs, exprConsts cfg o.value = .ok vs ∧ ∀ n ∈ vs, n ∈ ns) ∧
    (∀ iv, ci = .inductInfo iv → (∀ n ∈ iv.ctors, n ∈ ns) ∧
      ∀ r, ro = some r → iv.ctors.length = 1 ∧ viewFind view (mkRecName iv.name) = [r] ∧
        ∃ R, r = .recInfo R) ∧
    (∀ cv, ci = .ctorInfo cv → cv.induct ∈ ns) ∧
    (∀ r, ro = some r → (∃ R, r = .recInfo R) ∧
      ((∃ d, ci = .defnInfo d) ∨ ∃ iv, ci = .inductInfo iv)) := by
  unfold closureStep at h
  obtain ⟨u, hu, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨ty, hty, h⟩ := OracleWhnf.ok_of_bind h
  refine ⟨hu, ?_⟩
  cases ci with
  | defnInfo d =>
    dsimp only at h
    split at h
    · rename_i I R ctors hrec
      obtain ⟨_, hfor, h⟩ := OracleWhnf.ok_of_bind h
      cases h
      refine ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
        fun d' hd => .inr ⟨I, R, ctors, by cases hd; exact hrec, by simp, rfl, ?_⟩, nofun, nofun,
        nofun, fun _ hr => ⟨⟨R, by cases hr; rfl⟩, .inl ⟨d, rfl⟩⟩⟩
      intro c hc cv hcv
      subst hcv
      obtain ⟨s, hs⟩ := forIn_ok (by
        intro a s hs
        split at hs
        · split at hs
          · cases hs; rfl
          · cases hs
        · cases hs; rfl) hfor _ hc
      dsimp only at hs
      exact (ite_ok_then hs fun _ h => nomatch h).1
    · obtain ⟨vs, hvs, h⟩ := OracleWhnf.ok_of_bind h
      cases h
      exact ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]),
        fun d' hd => .inl ⟨by cases hd; assumption, rfl, vs, by cases hd; exact hvs,
          fun n hn => by simp_all [ConstantInfo.all]⟩, nofun, nofun, nofun, nofun⟩
  | thmInfo t =>
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]), nofun, nofun,
      nofun, nofun, nofun⟩
  | opaqueInfo o =>
    obtain ⟨vs, hvs, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]), nofun,
      fun o' ho => ⟨vs, by cases ho; exact hvs, fun n hn => by simp_all [ConstantInfo.all]⟩, nofun, nofun, nofun⟩
  | inductInfo iv =>
    cases h
    refine ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩, fun n hn => .inl (by simp_all [ConstantInfo.all]), nofun, nofun,
      fun iv' hiv => ⟨fun n hn => by cases hiv; simp [hn], fun r hr => ?_⟩, nofun,
      fun r hr => ⟨?_, .inr ⟨iv, rfl⟩⟩⟩
    · cases hiv
      split at hr
      · rename_i c r' R hc hv
        cases hr
        exact ⟨by simp [hc], hv, R, rfl⟩
      · cases hr
    split at hr
    · rename_i c r' R hc hv
      cases hr
      exact ⟨R, rfl⟩
    · cases hr
  | ctorInfo cv =>
    cases h
    exact ⟨⟨ty, hty, fun n hn => by simp_all [ConstantInfo.all]⟩,
      fun n hn => .inr (by simpa [ConstantInfo.all] using hn), nofun, nofun, nofun,
      fun cv' hcv => by cases hcv; simp, nofun⟩
  | axiomInfo _ | quotInfo _ | recInfo _ =>
    cases h
    exact ⟨⟨_, hty, fun n hn => hn⟩, fun n hn => .inr (by simpa [ConstantInfo.all] using hn),
      nofun, nofun, nofun, nofun, nofun⟩

/-! ## The closure -/

/-- `n` names a declaration of `l` that is not a recursor. -/
def Covered (l : List ConstantInfo) (n : Name) : Prop :=
  ∃ y ∈ l, y.name = n ∧ ∀ R, y ≠ .recInfo R

/-- `Covered` is monotone in the list. -/
theorem Covered.mono {l l' : List ConstantInfo} (hl : ∀ x ∈ l, x ∈ l') {n : Name}
    (h : Covered l n) : Covered l' n :=
  let ⟨y, hy, hn, hr⟩ := h
  ⟨y, hl y hy, hn, hr⟩

/-- How a declaration entered the closure: scanned by `closureStep`, with its read names in `C`,
its companion in `l` and, for a recognized `casesOn`, its name in `cs`; or as the companion
recursor of a scanned declaration of `l`, with the names of its type in `C`. -/
def Scanned (view : EnvView) (cfg : ErasureConfig) (C : Name → Prop) (l : List ConstantInfo)
    (cs : List Name) (ci : ConstantInfo) : Prop :=
  (∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, C n) ∧
    (∀ r, ro = some r → r ∈ l) ∧ (∀ r d, ro = some r → ci = .defnInfo d → ci.name ∈ cs)) ∨
  (∃ R, ci = .recInfo R ∧ (∃ tys, exprConsts cfg R.type = .ok tys ∧ ∀ n ∈ tys, C n) ∧
    ∃ cj ∈ l, ∃ ns, closureStep view cfg cj = .ok (ns, some ci))

/-- `Scanned` is monotone in the predicate, the list and the recognized names. -/
theorem Scanned.mono {view : EnvView} {cfg : ErasureConfig} {C C' : Name → Prop}
    {l l' : List ConstantInfo} {cs cs' : List Name} {ci : ConstantInfo} (hC : ∀ n, C n → C' n)
    (hl : ∀ x ∈ l, x ∈ l') (hcs : ∀ m ∈ cs, m ∈ cs') (h : Scanned view cfg C l cs ci) :
    Scanned view cfg C' l' cs' ci := by
  rcases h with ⟨ns, ro, h1, h2, h3, h4⟩ | ⟨R, h1, ⟨tys, h2, h3⟩, cj, hcj, ns, h4⟩
  · exact .inl ⟨ns, ro, h1, fun n hn => hC n (h2 n hn), fun r hr => hl r (h3 r hr),
      fun r d hr hd => hcs _ (h4 r d hr hd)⟩
  · exact .inr ⟨R, h1, ⟨tys, h2, fun n hn => hC n (h3 n hn)⟩, cj, hl cj hcj, ns, h4⟩

/-- `dropKnown` drops names of non-recursor declarations of the accumulator and stops at a name the
accumulator does not have. -/
theorem dropKnown_ok {acc : List ConstantInfo} : ∀ {todo rest : List Name},
    dropKnown acc todo = .ok rest →
    (∃ pre, todo = pre ++ rest ∧ ∀ m ∈ pre, Covered acc m) ∧
    ∀ n rest', rest = n :: rest' → findConst acc n = none
  | [], rest, h => by
    rw [dropKnown] at h; cases h
    exact ⟨⟨[], rfl, nofun⟩, nofun⟩
  | n :: todo, rest, h => by
    rw [dropKnown] at h
    split at h
    · cases h
    · rename_i y hnr hy
      obtain ⟨⟨pre, hpre, hcov⟩, hnone⟩ := dropKnown_ok h
      refine ⟨⟨n :: pre, by rw [hpre]; rfl, fun m hm => ?_⟩, hnone⟩
      rcases List.mem_cons.1 hm with rfl | hm
      · obtain ⟨h1, h2⟩ := findDecl_eq_some (l := acc) hy
        exact ⟨y, h1, h2, fun R hR => hnr R hR⟩
      · exact hcov m hm
    · rename_i hn
      cases h
      exact ⟨⟨[], rfl, nofun⟩, fun m rest' he => by cases he; exact hn⟩

/-- Two declarations of the program with one name are equal. -/
theorem eq_of_name {view : EnvView} (hview : ViewAgrees view P) {x y : ConstantInfo}
    (hx : x ∈ P) (hy : y ∈ P) (hn : x.name = y.name) : x = y := by
  have h1 := findDecl_of_view hview hx
  have h2 := findDecl_of_view hview hy
  rw [hn, h2] at h1
  cases h1; rfl

/-- What a run of the closure returns, from an accumulator of the program whose declarations are
scanned up to the work list. -/
theorem closure_ok (hP : ProgEnv P ζ E B) {view : EnvView} (hview : ViewAgrees view P)
    {cfg : ErasureConfig} : ∀ {f : Nat} {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name} {res : List ConstantInfo × List Name},
    closure view cfg f todo acc cases = .ok res → (∀ ci ∈ acc, ci ∈ P) →
    (∀ n ∈ todo, n ∈ P.map (·.name)) → (acc.map (·.name)).Nodup →
    (∀ ci ∈ acc, Scanned view cfg (fun n => Covered acc n ∨ n ∈ todo) acc cases ci) →
    (∀ ci ∈ res.1, ci ∈ P) ∧ (res.1.map (·.name)).Nodup ∧ (∀ ci ∈ acc, ci ∈ res.1) ∧
      (∀ m ∈ cases, m ∈ res.2) ∧ (∀ n ∈ todo, Covered res.1 n) ∧
      ∀ ci ∈ res.1, Scanned view cfg (Covered res.1) res.1 res.2 ci
  | 0, todo, acc, cases, res, h, hacc, _, hnd, hsc => by
    rw [closure] at h
    obtain ⟨todo', hd, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨⟨pre, hpre, hcov⟩, -⟩ := dropKnown_ok hd
    split at h
    · cases h
      rw [List.append_nil] at hpre
      subst hpre
      exact ⟨hacc, hnd, fun _ h => h, fun _ h => h, hcov, fun ci hci =>
        (hsc ci hci).mono (fun n hn => hn.elim id (hcov n)) (fun _ h => h) (fun _ h => h)⟩
    · cases h
  | f + 1, todo, acc, cases, res, h0, hacc, htodo, hnd, hsc => by
    rw [closure] at h0
    obtain ⟨todo', hd, h⟩ := OracleWhnf.ok_of_bind h0
    clear h0
    obtain ⟨⟨pre, hpre, hcov⟩, hnone⟩ := dropKnown_ok hd
    cases todo' with
    | nil =>
      cases h
      rw [List.append_nil] at hpre
      subst hpre
      exact ⟨hacc, hnd, fun _ h => h, fun _ h => h, hcov, fun ci hci =>
        (hsc ci hci).mono (fun n hn => hn.elim id (hcov n)) (fun _ h => h) (fun _ h => h)⟩
    | cons n todo'' =>
      subst hpre
      have hn : n ∈ P.map (·.name) := htodo n (by simp)
      have htl : ∀ m ∈ todo'', m ∈ P.map (·.name) := fun m hm => htodo m (by simp [hm])
      have hnacc : findConst acc n = none := hnone n todo'' rfl
      dsimp only at h
      cases hf : view.find? n with
      | none => rw [hf] at h; cases h
      | some ci =>
        rw [hf] at h
        dsimp only at h
        have hciP : ci ∈ P := view_mem hview hn hf
        by_cases hname : (ci.name != n) = true
        · rw [ite_eq_left hname] at h; cases h
        rw [ite_eq_right hname] at h
        have hcn : ci.name = n := by simpa using hname
        obtain ⟨⟨ns, ro⟩, hcs, h⟩ := OracleWhnf.ok_of_bind h
        obtain ⟨hns, hro⟩ := closureStep_sub hP hview hciP hcs
        have hspec := closureStep_spec hcs
        have hcnr : ∀ R, ci ≠ .recInfo R := (declExclusion_ok hspec.1).1
        have hcovn : Covered (ci :: acc) n := ⟨ci, List.mem_cons_self, hcn, hcnr⟩
        have hnd1 : ((ci :: acc).map (·.name)).Nodup := by
          rw [List.map_cons, List.nodup_cons]
          exact ⟨hcn ▸ not_mem_of_findDecl_none hnacc, hnd⟩
        have hacc1 : ∀ cj ∈ ci :: acc, cj ∈ P := by
          intro cj hcj
          rcases List.mem_cons.1 hcj with rfl | hcj
          · exact hciP
          · exact hacc cj hcj
        -- the new `cases`
        have hcases : ∀ m ∈ cases,
            m ∈ (if (match ci with | .defnInfo _ => true | _ => false) = true then n :: cases
              else cases) := by
          intro m hm; split <;> simp [hm]
        have hcasesn : ∀ d, ci = .defnInfo d →
            n ∈ (if (match ci with | .defnInfo _ => true | _ => false) = true then n :: cases
              else cases) := by
          intro d hd; subst hd; simp
        -- old declarations stay scanned
        have hold : ∀ (todo1 : List Name) (l : List ConstantInfo) (cs : List Name),
            (∀ m ∈ todo'', m ∈ todo1) → (∀ x ∈ ci :: acc, x ∈ l) → (∀ m ∈ cases, m ∈ cs) →
            ∀ cj ∈ acc, Scanned view cfg (fun m => Covered l m ∨ m ∈ todo1) l cs cj := by
          intro todo1 l cs ht hl hcs' cj hcj
          refine (hsc cj hcj).mono (fun m hm => ?_) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
            hcs'
          rcases hm with hm | hm
          · exact .inl (hm.mono fun x hx => hl x (List.mem_cons_of_mem _ hx))
          · simp only [List.mem_append, List.mem_cons] at hm
            rcases hm with hm | rfl | hm
            · exact .inl ((hcov m hm).mono fun x hx => hl x (List.mem_cons_of_mem _ hx))
            · exact .inl (hcovn.mono hl)
            · exact .inr (ht m hm)
        have hpost : ∀ (l : List ConstantInfo) (cs : List Name), (∀ x ∈ ci :: acc, x ∈ l) →
            (∀ m ∈ todo'', Covered l m) → ∀ m ∈ pre ++ n :: todo'', Covered l m := by
          intro l cs hl ht m hm
          simp only [List.mem_append, List.mem_cons] at hm
          rcases hm with hm | rfl | hm
          · exact (hcov m hm).mono fun x hx => hl x (List.mem_cons_of_mem _ hx)
          · exact hcovn.mono hl
          · exact ht m hm
        cases ro with
        | none =>
          obtain ⟨r1, r2, r3, r4, r5, r6⟩ := closure_ok hP hview h hacc1
            (fun m hm => by
              rcases List.mem_append.1 hm with hm | hm
              · exact hns m hm
              · exact htl m hm) hnd1
            (fun cj hcj => by
              rcases List.mem_cons.1 hcj with rfl | hcj
              · exact .inl ⟨ns, none, hcs, fun m hm => .inr (List.mem_append_left _ hm), nofun,
                  nofun⟩
              · exact hold _ _ _ (fun m hm => List.mem_append_right _ hm) (fun _ h => h)
                  (fun _ h => h) cj hcj)
          exact ⟨r1, r2, fun x hx => r3 x (List.mem_cons_of_mem _ hx),
            fun m hm => r4 m hm,
            hpost _ cases r3 (fun m hm => r5 m (List.mem_append_right _ hm)), r6⟩
        | some r =>
          have hrP := hro r rfl
          obtain ⟨R, rfl⟩ := (hspec.2.2.2.2.2.2.2 _ rfl).1
          have hrn : (ConstantInfo.recInfo R).name ≠ ci.name := fun he =>
            hcnr R (eq_of_name hview hciP hrP he.symm)
          dsimp only at h
          by_cases hfa : (findConst acc (ConstantInfo.recInfo R).name).isSome = true
          · rw [ite_eq_left hfa] at h
            obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hfa
            obtain ⟨hy1, hy2⟩ := findDecl_eq_some (l := acc) hy
            have hyr : y = .recInfo R := eq_of_name hview (hacc y hy1) hrP hy2
            subst hyr
            obtain ⟨r1, r2, r3, r4, r5, r6⟩ := closure_ok hP hview h hacc1
              (fun m hm => by
                rcases List.mem_append.1 hm with hm | hm
                · exact hns m hm
                · exact htl m hm) hnd1
              (fun cj hcj => by
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact .inl ⟨ns, some _, hcs, fun m hm => .inr (List.mem_append_left _ hm),
                    fun r hr => by cases hr; exact List.mem_cons_of_mem _ hy1,
                    fun r d _ hd => hcn ▸ hcasesn d hd⟩
                · exact hold _ _ _ (fun m hm => List.mem_append_right _ hm) (fun _ h => h)
                    hcases cj hcj)
            exact ⟨r1, r2, fun x hx => r3 x (List.mem_cons_of_mem _ hx),
              fun m hm => r4 m (hcases m hm),
              hpost _ cases r3 (fun m hm => r5 m (List.mem_append_right _ hm)), r6⟩
          · rw [ite_eq_right hfa] at h
            obtain ⟨tys, htys, h⟩ := OracleWhnf.ok_of_bind h
            have htyP := (ProgEnv.names_closed hP _ hrP).type.exprConsts htys
            have hl2 : ∀ x ∈ ci :: acc, x ∈ ConstantInfo.recInfo R :: ci :: acc :=
              fun x hx => List.mem_cons_of_mem _ hx
            obtain ⟨r1, r2, r3, r4, r5, r6⟩ := closure_ok hP hview h
              (fun cj hcj => by
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact hrP
                · exact hacc1 cj hcj)
              (fun m hm => by
                simp only [List.mem_append] at hm
                rcases hm with (hm | hm) | hm
                · exact hns m hm
                · exact htyP m hm
                · exact htl m hm)
              (by
                rw [List.map_cons, List.nodup_cons]
                refine ⟨fun hm => ?_, hnd1⟩
                rw [List.map_cons, List.mem_cons] at hm
                rcases hm with hm | hm
                · exact hrn hm
                · exact hfa (findDecl_isSome_iff.2 hm))
              (fun cj hcj => by
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact .inr ⟨R, rfl, ⟨tys, htys, fun m hm => .inr (by simp [hm])⟩, ci,
                    List.mem_cons_of_mem _ List.mem_cons_self, ns, hcs⟩
                rcases List.mem_cons.1 hcj with rfl | hcj
                · exact .inl ⟨ns, some _, hcs, fun m hm => .inr (by simp [hm]),
                    fun r hr => by cases hr; exact List.mem_cons_self,
                    fun r d _ hd => hcn ▸ hcasesn d hd⟩
                · exact hold _ _ _ (fun m hm => by simp [hm]) hl2 hcases cj hcj)
            exact ⟨r1, r2, fun x hx => r3 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)),
              fun m hm => r4 m (hcases m hm),
              hpost _ cases (fun x hx => r3 x (hl2 x hx))
                (fun m hm => r5 m (by simp [hm])), r6⟩

/-! ## The `casesOn` recognizer reads only some lookups -/

theorem ctorAlts_congr {l₁ l₂ : List ConstantInfo} : ∀ {cs : List Name},
    (∀ x ∈ cs, findConst l₂ x = findConst l₁ x) → ctorAlts l₂ cs = ctorAlts l₁ cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [ctorAlts, h c List.mem_cons_self,
      ctorAlts_congr (cs := cs) fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `blockCtorCount` reads only the lookups of the block members. -/
theorem blockCtorCount_congr {l₁ l₂ : List ConstantInfo} : ∀ {ts : List Name},
    (∀ x ∈ ts, findConst l₂ x = findConst l₁ x) → blockCtorCount l₂ ts = blockCtorCount l₁ ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [blockCtorCount, h t List.mem_cons_self,
      blockCtorCount_congr (ts := ts) fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The names `casesInfo? l (T.casesOn)` looks up in `l`. -/
def CasesReads (l : List ConstantInfo) (T x : Name) : Prop :=
  x = .str T "casesOn" ∨ x = T ∨ x = mkRecName T ∨
    (∃ I, findConst l T = some (.inductInfo I) ∧ x ∈ I.ctors) ∨
    ∃ R, findConst l (mkRecName T) = some (.recInfo R) ∧ x ∈ R.all

/-- `casesInfo?` answers the same on two lists that agree on what it reads. -/
theorem casesInfo?_congr {l₁ l₂ : List ConstantInfo} {n : Name} {c : CasesInfo}
    (h : casesInfo? l₁ n = some c)
    (hag : ∀ T, n = .str T "casesOn" → ∀ x, CasesReads l₁ T x → findConst l₂ x = findConst l₁ x) :
    casesInfo? l₂ n = some c := by
  unfold casesInfo? at h ⊢
  split at h
  next T =>
    have hag := hag T rfl
    rw [hag _ (.inl rfl), hag T (.inr (.inl rfl)), hag (mkRecName T) (.inr (.inr (.inl rfl)))]
    split at h
    next d I R hd hI hR =>
      have e4 : ctorAlts l₂ I.ctors = ctorAlts l₁ I.ctors :=
        ctorAlts_congr fun x hx => hag x (.inr (.inr (.inr (.inl ⟨I, hI, hx⟩))))
      have e5 : ∀ k, blockCtorCount l₂ (R.all.take k) = blockCtorCount l₁ (R.all.take k) :=
        fun k => blockCtorCount_congr fun x hx =>
          hag x (.inr (.inr (.inr (.inr ⟨R, hR, List.mem_of_mem_take hx⟩))))
      simp only [hd, hI, hR, e4, e5]
      exact h
    next => cases h
  next => cases h

/-- What a recognized `casesOn` is named, and which inductive it eliminates. -/
theorem casesInfo?_name {l : List ConstantInfo} {n : Name} {c : CasesInfo}
    (h : casesInfo? l n = some c) : ∃ T I, n = .str T "casesOn" ∧ c.indName = T ∧
      findConst l T = some (.inductInfo I) ∧ (∃ d, findConst l n = some (.defnInfo d)) ∧
      ∃ R, findConst l (mkRecName T) = some (.recInfo R) := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next =>
        split at h
        next => cases h; exact ⟨T, I, rfl, rfl, hI, ⟨d, hd⟩, R, hR⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- Two lists of view declarations agree on the names they both have. -/
theorem findConst_agree {view : EnvView} {l₁ l₂ : List ConstantInfo}
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

/-- The list `recognizeCasesOn` checks. -/
def recogList (view : EnvView) (ci : ConstantInfo) (I : InductiveVal) (R : RecursorVal) :
    List ConstantInfo :=
  ci :: .inductInfo I :: .recInfo R :: I.ctors.flatMap (viewFind view) ++
    R.all.flatMap (viewFind view)

/-- What `recognizeCasesOn` checks: the view's `T` and `T.rec`, and `casesInfo?` on `recogList`. -/
theorem recognize_iff {view : EnvView} {ci : ConstantInfo} {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} :
    recognizeCasesOn view ci = some (I, R, ctors) ↔ ∃ T, ci.name = .str T "casesOn" ∧
      viewFind view T = [.inductInfo I] ∧ viewFind view (mkRecName T) = [.recInfo R] ∧
      ctors = I.ctors.flatMap (viewFind view) ∧
      (casesInfo? (recogList view ci I R) ci.name).isSome := by
  constructor
  · intro h
    unfold recognizeCasesOn at h
    split at h
    next T hT =>
      split at h
      next I' R' hI hR =>
        obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.1 h
        cases heq
        exact ⟨T, hT, hI, hR, rfl, by rw [recogList, hc]; rfl⟩
      next => cases h
    next => cases h
  · rintro ⟨T, hT, hI, hR, rfl, hc⟩
    unfold recognizeCasesOn
    rw [hT]
    simp only [hI, hR]
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hc
    rw [← hT]
    unfold recogList at hc
    rw [hc]
    rfl

/-! ## The checks after the closure -/

theorem collectDeps_ok {view : EnvView} {cfg : ErasureConfig} {e : Expr}
    {decls : List ConstantInfo} (h : collectDeps view cfg e = .ok decls) :
    ∃ cs cases, exprConsts cfg e = .ok cs ∧
      closure view cfg collectFuel cs [] [] = .ok (decls, cases) ∧
      eliminatedUndecided decls cases = none ∧ findCollision decls = none ∧
      findBlockCollision decls = none := by
  unfold collectDeps at h
  obtain ⟨cs, hcs, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨⟨ds, cases⟩, hcl, h⟩ := OracleWhnf.ok_of_bind h
  have key : ∀ x, (match findCollision ds with
      | some (a, b) => (throw (EraseError.nameCollision a b) : Except EraseError _)
      | none => match findBlockCollision ds with
        | some (a, b) => throw (EraseError.nameCollision a b)
        | none => pure ds) = .ok x →
      findCollision ds = none ∧ findBlockCollision ds = none ∧ x = ds := by
    intro x hx
    cases hc : findCollision ds with
    | some p => rw [hc] at hx; cases hx
    | none =>
      rw [hc] at hx
      cases hb : findBlockCollision ds with
      | some p => rw [hb] at hx; cases hx
      | none => rw [hb] at hx; cases hx; exact ⟨rfl, rfl, rfl⟩
  dsimp only at h
  cases he : eliminatedUndecided ds cases with
  | some n => rw [he] at h; cases h
  | none =>
    rw [he] at h
    dsimp only at h
    have fin : ∀ x, findCollision ds = none ∧ findBlockCollision ds = none ∧ x = ds →
        ∃ cs' cases', exprConsts cfg e = .ok cs' ∧
          closure view cfg collectFuel cs' [] [] = .ok (x, cases') ∧
          eliminatedUndecided x cases' = none ∧ findCollision x = none ∧
          findBlockCollision x = none := by
      rintro x ⟨h1, h2, rfl⟩
      exact ⟨cs, cases, hcs, hcl, he, h1, h2⟩
    split at h
    · split at h
      · cases h
      · exact fin _ (key _ h)
    · exact fin _ (key _ h)

/-- Without a block collision, the λ□ block names are distinct and differ from the kernames of the
emitted constants. -/
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

/-- The sort test on an inductive it accepts. -/
theorem sortDecided_ok {iv : InductiveVal} {b : Bool} (h : sortDecided iv = .ok b) :
    ∃ n u, arityShape iv.type = some (n, u) ∧
      (u = .zero ∨ u.isNeverZero = true ∨ (mayBeNonZero iv.levelParams u = true ∧ b = false)) := by
  unfold sortDecided at h
  split at h
  · rename_i n hs; exact ⟨n, .zero, hs, .inl rfl⟩
  · rename_i n u hs _
    refine ⟨n, u, by assumption, ?_⟩
    split at h
    · exact .inr (.inl ‹_›)
    · split at h
      · cases h; exact .inr (.inr ⟨‹_›, rfl⟩)
      · cases h
  · cases h

/-! ## The closure of a run -/

theorem viewFind_of {view : EnvView} {n : Name} {y : ConstantInfo} (h : view.find? n = some y)
    (hn : y.name = n) : viewFind view n = [y] := by
  unfold viewFind; rw [h]; simp [Option.filter, hn]

/-- A covered name is a name of the list. -/
theorem Covered.mem {l : List ConstantInfo} {n : Name} (h : Covered l n) : n ∈ l.map (·.name) :=
  let ⟨_, hy, hn, _⟩ := h
  hn ▸ List.mem_map_of_mem hy

/-- A declaration that `viewFind` returns is the view's, under that name. -/
theorem viewFind_mem {view : EnvView} {n : Name} {y : ConstantInfo} (h : y ∈ viewFind view n) :
    view.find? y.name = some y ∧ y.name = n := by
  unfold viewFind at h
  cases hf : view.find? n with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    by_cases hx : x.name = n
    · simp [Option.filter, hx] at h
      subst h
      exact ⟨hx ▸ hf, hx⟩
    · simp [Option.filter, hx] at h

/-- The declarations `recognizeCasesOn` checks are the view's. -/
theorem recog_view {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal} {T : Name}
    (hd : view.find? d.name = some (.defnInfo d))
    (hI : viewFind view T = [.inductInfo I]) (hR : viewFind view (mkRecName T) = [.recInfo R]) :
    ∀ y ∈ recogList view (.defnInfo d) I R, view.find? y.name = some y := by
  intro y hy
  simp only [recogList, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hy
  rcases hy with rfl | rfl | rfl | ⟨x, -, hx⟩ | ⟨x, -, hx⟩
  · exact hd
  · exact (viewFind_mem (hI ▸ List.mem_singleton_self _)).1
  · exact (viewFind_mem (hR ▸ List.mem_singleton_self _)).1
  · exact (viewFind_mem hx).1
  · exact (viewFind_mem hx).1

/-- What `eliminatedUndecided` answering `none` says about an inductive whose sort may be both zero
and not zero. -/
theorem eliminatedUndecided_none {decls : List ConstantInfo} {cases : List Name}
    (h : eliminatedUndecided decls cases = none) {iv : InductiveVal}
    (hiv : .inductInfo iv ∈ decls) (hb : sortDecided iv = .ok false) :
    ¬ cases.contains (.str iv.name "casesOn") = true ∧
      ∀ cn cv, iv.ctors = [cn] → findDecl decls cn = some (.ctorInfo cv) → ¬ 0 < cv.numFields := by
  rw [eliminatedUndecided, List.findSome?_eq_none_iff] at h
  have h0 := h _ hiv
  dsimp only at h0
  rw [hb] at h0
  refine ⟨fun hc => ?_, fun cn cv hc hf hpos => ?_⟩
  · simp at h0 hc
    exact h0.1 hc
  · rw [hc] at h0
    have hf' : findConst decls cn = some (.ctorInfo cv) := hf
    simp [hf', hpos] at h0

/-- A successful run of the closure on a program read through an agreeing view. -/
structure Run (P : List ConstantInfo) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (cases : List Name) : Prop where
  closed : ∀ ci ∈ P, NamesClosed P ci
  hview : ViewAgrees view P
  sub : ∀ ci ∈ decls, ci ∈ P
  scan : ∀ ci ∈ decls, Scanned view cfg (Covered decls) decls cases ci

namespace Run

variable {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo} {cases : List Name}
  (hr : Run P view cfg decls cases)
include hr

/-- A declaration of the closure is the first of its name. -/
theorem fd {y : ConstantInfo} (hy : y ∈ decls) : findDecl decls y.name = some y := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 (List.mem_map_of_mem hy))
  obtain ⟨hz1, hz2⟩ := findDecl_eq_some hz
  rw [hz, eq_of_name hr.hview (hr.sub z hz1) (hr.sub y hy) hz2]

/-- A covered name is found in the closure, as a declaration that is not a recursor. -/
theorem cov {n : Name} (h : Covered decls n) :
    ∃ y, findDecl decls n = some y ∧ y ∈ decls ∧ ∀ R, y ≠ .recInfo R := by
  obtain ⟨y, hy, rfl, hr'⟩ := h
  exact ⟨y, hr.fd hy, hy, hr'⟩

/-- The view returns the closure's declarations. -/
theorem vw {y : ConstantInfo} (hy : y ∈ decls) : view.find? y.name = some y :=
  hr.hview y (hr.sub y hy)

/-- A declaration of the closure that is not a recursor was scanned by `closureStep`. -/
theorem scanned {ci : ConstantInfo} (hci : ci ∈ decls) (hnr : ∀ R, ci ≠ .recInfo R) :
    ∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, Covered decls n) ∧
      (∀ r, ro = some r → r ∈ decls) ∧ (∀ r d, ro = some r → ci = .defnInfo d → ci.name ∈ cases) := by
  rcases hr.scan ci hci with h | ⟨R, rfl, -⟩
  · exact h
  · exact absurd rfl (hnr R)

/-- A name of the program is found through the view. -/
theorem in_view {n : Name} (hn : n ∈ P.map (·.name)) :
    ∃ y ∈ P, y.name = n ∧ viewFind view n = [y] := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
  exact ⟨y, hy, rfl, viewFind_of (hr.hview y hy) rfl⟩

/-- The constructors and block members of an inductive of the closure are covered. -/
theorem ind_reads {iv : InductiveVal} (hiv : .inductInfo iv ∈ decls) :
    (∀ n ∈ iv.ctors, Covered decls n) ∧ ∀ n ∈ iv.all, Covered decls n := by
  obtain ⟨ns, ro, hcs, hns, -, -⟩ := hr.scanned hiv nofun
  have spec := closureStep_spec hcs
  refine ⟨fun n hn => hns n ((spec.2.2.2.2.2.1 iv rfl).1 n hn), fun n hn => ?_⟩
  rcases spec.2.2.1 n hn with h | h
  · exact hns n h
  · exact ⟨_, hiv, h.symm, nofun⟩

/-- An inductive of the program named like a covered name is the closure's. -/
theorem ind_of_view {T : Name} {I : InductiveVal} (hI : view.find? T = some (.inductInfo I))
    (hT : Covered decls T) : .inductInfo I ∈ decls := by
  obtain ⟨y, hy, hyn, -⟩ := hT
  have h := hr.vw hy
  rw [hyn, hI] at h
  cases h
  exact hy

/-- A name of the program in `l` is the name of a declaration of `l.flatMap (viewFind view)`. -/
theorem recog_flat {l : List Name} {x : Name} (hx : x ∈ l) (hxP : x ∈ P.map (·.name)) :
    ∃ y ∈ l.flatMap (viewFind view), y.name = x := by
  obtain ⟨y, -, hyn, hvf⟩ := hr.in_view hxP
  exact ⟨y, List.mem_flatMap.2 ⟨x, hx, by rw [hvf]; exact List.mem_singleton_self _⟩, hyn⟩

/-- On the two lists, the recognizer's reads agree when the inductive and the recursor are the
closure's. -/
theorem reads_agree {d : DefinitionVal} {iv : InductiveVal} {R : RecursorVal} {T : Name}
    (hd : .defnInfo d ∈ decls) (hT : d.name = .str T "casesOn")
    (hI : viewFind view T = [.inductInfo iv]) (hR : viewFind view (mkRecName T) = [.recInfo R])
    (hIdecl : .inductInfo iv ∈ decls) (hRdecl : .recInfo R ∈ decls) :
    ∀ x, (CasesReads (recogList view (.defnInfo d) iv R) T x ∨ CasesReads decls T x) →
      x ∈ (recogList view (.defnInfo d) iv R).map (·.name) ∧ x ∈ decls.map (·.name) := by
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  have hl₁ := recog_view (hr.vw hd) hI hR
  obtain ⟨iv', hiv'P, hiv'n, hiv'all⟩ := (hr.closed _ (hr.sub _ hRdecl)).recr R rfl
  have hiv'T : iv'.name = T := mkRecName_inj (hiv'n.symm.trans hRn)
  have hiv' : iv' = iv := by
    have := eq_of_name hr.hview hiv'P (hr.sub _ hIdecl) (hiv'T.trans hIn.symm)
    cases this; rfl
  subst hiv'
  obtain ⟨hctc, hallc⟩ := hr.ind_reads hIdecl
  have hIP := hr.closed _ (hr.sub _ hIdecl)
  have hrl : ∀ x, x ∈ iv'.ctors ∨ x ∈ iv'.all →
      x ∈ (recogList view (.defnInfo d) iv' R).map (·.name) ∧ x ∈ decls.map (·.name) := by
    intro x hx
    rcases hx with hx | hx
    · refine ⟨?_, (hctc x hx).mem⟩
      obtain ⟨y, hy, hyn⟩ := hr.recog_flat hx ((hIP.induct iv' rfl).1 x hx)
      exact List.mem_map.2 ⟨y, List.mem_append_left _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))), hyn⟩
    · refine ⟨?_, (hallc x hx).mem⟩
      obtain ⟨y, hy, hyn⟩ := hr.recog_flat (l := R.all) (hiv'all ▸ hx) (hIP.all x hx)
      exact List.mem_map.2 ⟨y, List.mem_append_right _ hy, hyn⟩
  have hview_eq : ∀ (l : List ConstantInfo), (∀ y ∈ l, view.find? y.name = some y) →
      ∀ n z, findConst l n = some z → view.find? n = some z := by
    intro l hl n z hz
    obtain ⟨hz1, hz2⟩ := findDecl_eq_some (l := l) hz
    exact hz2 ▸ hl z hz1
  intro x hx
  have base : ∀ l, (∀ y ∈ l, view.find? y.name = some y) → CasesReads l T x →
      x ∈ (recogList view (.defnInfo d) iv' R).map (·.name) ∧ x ∈ decls.map (·.name) := by
    intro l hl hx
    rcases hx with rfl | rfl | rfl | ⟨I', hI', hx⟩ | ⟨R', hR', hx⟩
    · exact ⟨List.mem_map.2 ⟨_, List.mem_append_left _ List.mem_cons_self, hT⟩,
        hT ▸ List.mem_map_of_mem hd⟩
    · exact ⟨List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self),
        hIn⟩, hIn ▸ List.mem_map_of_mem hIdecl⟩
    · exact ⟨List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)), hRn⟩, hRn ▸ List.mem_map_of_mem hRdecl⟩
    · have := hview_eq l hl _ _ hI'
      rw [hIf] at this; cases this
      exact hrl x (.inl hx)
    · have := hview_eq l hl _ _ hR'
      rw [hRf] at this; cases this
      exact hrl x (.inr (hiv'all ▸ hx))
  rcases hx with hx | hx
  · exact base _ hl₁ hx
  · exact base _ (fun y hy => hr.vw hy) hx

/-- A `casesOn` that the view recognizes is recognized on the closure. -/
theorem recog_ds {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} (hd : .defnInfo d ∈ decls)
    (hrec : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors)) (ax : ConstantInfo → Bool) :
    EvalEnv.casesOn? ⟨decls, ax⟩ d.name = some I ∧ .inductInfo I ∈ decls ∧
      .recInfo R ∈ decls ∧ ∃ T, d.name = .str T "casesOn" ∧ R.name = mkRecName T ∧
      ctors = I.ctors.flatMap (viewFind view) := by
  obtain ⟨T, hT, hI, hR, hct, hc⟩ := recognize_iff.1 hrec
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  obtain ⟨ns, ro, hcs, hns, hro, -⟩ := hr.scanned hd nofun
  have spec := closureStep_spec hcs
  rcases spec.2.2.2.1 d rfl with ⟨hnone, -, -⟩ | ⟨I', R', ctors', hrec', hIns, hro', -⟩
  · rw [hnone] at hrec; cases hrec
  rw [hrec] at hrec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
  obtain ⟨rfl, rfl, rfl⟩ := hrec'
  have hIdecl : .inductInfo I ∈ decls := hr.ind_of_view hIf (hIn ▸ hns _ hIns)
  have hRdecl : .recInfo R ∈ decls := hro _ hro'
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hc
  have hc' : casesInfo? decls d.name = some c := by
    refine casesInfo?_congr hc fun T' hT' x hx => ?_
    have hTT : T' = T := by
      have h2 : Name.str T "casesOn" = Name.str T' "casesOn" := hT.symm.trans hT'
      injection h2 with h; exact h.symm
    subst hTT
    obtain ⟨h1, h2⟩ := hr.reads_agree hd hT hI hR hIdecl hRdecl x (.inl hx)
    exact findConst_agree (recog_view (hr.vw hd) hI hR) (fun y hy => hr.vw hy) h1 h2
  obtain ⟨T', I'', hn, hind, -, -, -⟩ := casesInfo?_name hc'
  have hTT : T' = T := by
    have h2 : Name.str T "casesOn" = Name.str T' "casesOn" := hT.symm.trans hn
    injection h2 with h; exact h.symm
  subst hTT
  refine ⟨?_, hIdecl, hRdecl, T', hT, hRn, hct⟩
  unfold EvalEnv.casesOn?
  simp only [hc', hind]
  rw [← hIn, hr.fd hIdecl]

/-- A `casesOn` recognized on the closure is recognized by the view. -/
theorem recog_of_ds {d : DefinitionVal} {iv : InductiveVal} (hd : .defnInfo d ∈ decls)
    {ax : ConstantInfo → Bool} (hcs : EvalEnv.casesOn? ⟨decls, ax⟩ d.name = some iv) :
    .inductInfo iv ∈ decls ∧ ∃ R ctors, recognizeCasesOn view (.defnInfo d) = some (iv, R, ctors) := by
  unfold EvalEnv.casesOn? at hcs
  split at hcs
  next c hc =>
    split at hcs
    next iv' hiv =>
      cases hcs
      obtain ⟨T, I, hn, hind, hI, -, R, hR⟩ := casesInfo?_name hc
      rw [hind] at hiv
      obtain ⟨hIdecl, hIn⟩ := findDecl_eq_some hiv
      obtain ⟨hRdecl, hRn⟩ := findDecl_eq_some (l := decls) hR
      have hIv : viewFind view T = [.inductInfo iv] := viewFind_of (hIn ▸ hr.vw hIdecl) hIn
      have hRv : viewFind view (mkRecName T) = [.recInfo R] := viewFind_of (hRn ▸ hr.vw hRdecl) hRn
      refine ⟨hIdecl, R, _, recognize_iff.2 ⟨T, hn, hIv, hRv, rfl, ?_⟩⟩
      have : casesInfo? (recogList view (.defnInfo d) iv R) d.name = some c := by
        refine casesInfo?_congr hc fun T' hT' x hx => ?_
        have hTT : T' = T := by
          have h2 : Name.str T "casesOn" = Name.str T' "casesOn" := hn.symm.trans hT'
          injection h2 with h; exact h.symm
        subst hTT
        obtain ⟨h1, h2⟩ := hr.reads_agree hd hn hIv hRv hIdecl hRdecl x (.inr hx)
        exact findConst_agree (fun y hy => hr.vw hy) (recog_view (hr.vw hd) hIv hRv) h2 h1
      exact Option.isSome_iff_exists.2 ⟨c, this⟩
    next => cases hcs
  next => cases hcs

/-- Every expression the traversal reads from the closure was scanned, with its names covered. -/
theorem read {ci : ConstantInfo} (hci : ci ∈ decls) {x : Expr} (hx : ReadExpr decls ci x) :
    ∃ xs, exprConsts cfg x = .ok xs ∧ ∀ n ∈ xs, Covered decls n := by
  rcases hr.scan ci hci with ⟨ns, ro, hcs, hns, -, -⟩ | ⟨R, rfl, ⟨tys, htys, htc⟩, -⟩
  · have spec := closureStep_spec hcs
    rcases hx with rfl | ⟨d, rfl, rfl, hnone⟩ | ⟨o, rfl, rfl⟩
    · obtain ⟨ty, hty, hsub⟩ := spec.2.1
      exact ⟨ty, hty, fun n hn => hns n (hsub n hn)⟩
    · rcases spec.2.2.2.1 d rfl with ⟨-, -, vs, hvs, hsub⟩ | ⟨I, R, ctors, hrec, -⟩
      · exact ⟨vs, hvs, fun n hn => hns n (hsub n hn)⟩
      · rw [(hr.recog_ds hci hrec _).1] at hnone; cases hnone
    · obtain ⟨vs, hvs, hsub⟩ := spec.2.2.2.2.1 o rfl
      exact ⟨vs, hvs, fun n hn => hns n (hsub n hn)⟩
  · rcases hx with rfl | ⟨d, h, -⟩ | ⟨o, h, -⟩
    · exact ⟨tys, htys, htc⟩
    · cases h
    · cases h

/-- The inductive block of a recursor of the closure is in the closure. -/
theorem recr_all {R : RecursorVal} (hR : .recInfo R ∈ decls) :
    ∀ n ∈ R.all, Covered decls n := by
  rcases hr.scan _ hR with ⟨ns, ro, hcs, -, -, -⟩ | ⟨R', hR', -, cj, hcj, ns, hcs⟩
  · exact absurd rfl ((declExclusion_ok (closureStep_spec hcs).1).1 R)
  cases hR'
  obtain ⟨iv, hivP, hivn, hivall⟩ := (hr.closed _ (hr.sub _ hR)).recr R rfl
  have spec := closureStep_spec hcs
  obtain ⟨-, hkind⟩ := spec.2.2.2.2.2.2.2 _ rfl
  obtain ⟨ns', ro', hcs', hns', hro', -⟩ := hr.scanned hcj
    ((declExclusion_ok spec.1).1)
  rw [hcs] at hcs'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hcs'
  obtain ⟨rfl, rfl⟩ := hcs'
  -- the inductive `T` with `T.rec = R`
  have key : ∀ T I, R.name = mkRecName T → .inductInfo I ∈ decls → I.name = T →
      ∀ n ∈ R.all, Covered decls n := by
    intro T I hRT hI hIT
    have hiv : iv = I := by
      have := eq_of_name hr.hview hivP (hr.sub _ hI)
        ((mkRecName_inj (hivn.symm.trans hRT)).trans hIT.symm)
      cases this; rfl
    subst hiv
    rw [hivall]
    exact (hr.ind_reads hI).2
  rcases hkind with ⟨d, rfl⟩ | ⟨iv', rfl⟩
  · rcases spec.2.2.2.1 d rfl with ⟨-, hnone, -⟩ | ⟨I, R', ctors, hrec, -, hro, -⟩
    · cases hnone
    · cases hro
      obtain ⟨-, hIdecl, -, T, hTd, hRT, -⟩ := hr.recog_ds hcj hrec (fun _ => false)
      obtain ⟨T', hT', hI, -, -, -⟩ := recognize_iff.1 hrec
      obtain ⟨-, hIn⟩ := viewFind_eq hI
      have hTT : T' = T := by
        have h2 : Name.str T' "casesOn" = Name.str T "casesOn" := hT'.symm.trans hTd
        injection h2
      exact key T I hRT hIdecl (hIn.trans hTT)
  · obtain ⟨-, hvf, -⟩ := (spec.2.2.2.2.2.1 iv' rfl).2 _ rfl
    obtain ⟨-, hRn⟩ := viewFind_eq hvf
    exact key iv'.name iv' hRn hcj rfl

/-- The definition behind a `casesOn` recognized on the closure. -/
theorem defn_of_casesOn {n : Name} {iv : InductiveVal} {ax : ConstantInfo → Bool}
    (h : EvalEnv.casesOn? ⟨decls, ax⟩ n = some iv) :
    ∃ d, .defnInfo d ∈ decls ∧ d.name = n := by
  unfold EvalEnv.casesOn? at h
  split at h
  next c hc =>
    obtain ⟨-, -, -, -, -, ⟨d, hd⟩, -⟩ := casesInfo?_name hc
    obtain ⟨h1, h2⟩ := findDecl_eq_some (l := decls) hd
    exact ⟨d, h1, h2⟩
  next => cases h

/-- Every declaration of the closure is inside the first-phase fragment. -/
theorem phase (hel : eliminatedUndecided decls cases = none) {ci : ConstantInfo}
    (hci : ci ∈ decls) : PhaseIDecl view cfg decls ci := by
  rcases hr.scan ci hci with ⟨ns, ro, hcs, hns, hro, hcas⟩ | ⟨R, rfl, -, cj, hcj, ns, hcs⟩
  · have spec := closureStep_spec hcs
    have dex := declExclusion_ok spec.1
    cases ci with
    | quotInfo q => exact absurd rfl (dex.2.1 q)
    | recInfo r => exact absurd rfl (dex.1 r)
    | defnInfo d => exact dex.2.2.1 d rfl
    | opaqueInfo o => exact dex.2.2.2.1 o rfl
    | axiomInfo a => exact dex.2.2.2.2.1 a rfl
    | thmInfo _ => trivial
    | ctorInfo cv => exact dex.2.2.2.2.2.2 cv rfl
    | inductInfo iv =>
      obtain ⟨hu, hnn, b, hb⟩ := dex.2.2.2.2.2.1 iv rfl
      obtain ⟨n, u, hsh, hu'⟩ := sortDecided_ok hb
      -- the `casesOn` of `iv`, when recognized on the closure, was recognized by the view
      have hrecog : ∀ iv', EvalEnv.casesOn? ⟨decls, fun _ => false⟩ (.str iv.name "casesOn") =
          some iv' → ∃ d R ctors, .defnInfo d ∈ decls ∧ d.name = .str iv.name "casesOn" ∧
            recognizeCasesOn view (.defnInfo d) = some (iv, R, ctors) := by
        intro iv' hiv'
        obtain ⟨d, hd, hdn⟩ := hr.defn_of_casesOn hiv'
        obtain ⟨-, R, ctors, hrec⟩ := hr.recog_of_ds hd (hdn ▸ hiv')
        obtain ⟨T, hT, hI, -, -, -⟩ := recognize_iff.1 hrec
        have hTT : T = iv.name := by
          have h2 : Name.str T "casesOn" = Name.str iv.name "casesOn" := hT.symm.trans hdn
          injection h2
        subst hTT
        obtain ⟨hIf, -⟩ := viewFind_eq hI
        have this : view.find? iv.name = some (.inductInfo iv) := hr.vw hci
        rw [hIf] at this
        cases this
        exact ⟨d, R, ctors, hd, hdn, hrec⟩
      refine ⟨hu, hnn, ⟨n, u, hsh, ?_⟩, ?_⟩
      · rcases hu' with h | h | ⟨hm, rfl⟩
        · exact .inl h
        · exact .inr (.inl h)
        · refine .inr (.inr ⟨hm, fun hel' => ?_⟩)
          obtain ⟨hno1, hno2⟩ := eliminatedUndecided_none hel hci hb
          unfold Eliminated at hel'
          rcases hel' with hc | ⟨cn, cv, hcs1, hcv1, hnf⟩
          · obtain ⟨iv', hiv'⟩ := Option.isSome_iff_exists.1 hc
            obtain ⟨d, R, ctors, hd, hdn, hrec⟩ := hrecog iv' hiv'
            obtain ⟨ns', ro', hcs', -, -, hcas'⟩ := hr.scanned hd nofun
            rcases (closureStep_spec hcs').2.2.2.1 d rfl with ⟨hnone, -, -⟩ |
              ⟨I', R', ctors', hrec', -, hro', -⟩
            · rw [hnone] at hrec; cases hrec
            · have hmem := hcas' _ d hro' rfl
              rw [show (ConstantInfo.defnInfo d).name = d.name from rfl, hdn] at hmem
              exact hno1 (by simp [hmem])
          · exact hno2 cn cv hcs1 hcv1 hnf
      · intro hcase cn hcn cv hcv
        obtain ⟨iv', hiv'⟩ := Option.isSome_iff_exists.1 hcase
        obtain ⟨d, R, ctors, hd, -, hrec⟩ := hrecog iv' hiv'
        obtain ⟨ns', ro', hcs', -, -, -⟩ := hr.scanned hd nofun
        rcases (closureStep_spec hcs').2.2.2.1 d rfl with ⟨hnone, -, -⟩ |
          ⟨I', R', ctors', hrec', -, -, hidx⟩
        · rw [hnone] at hrec; cases hrec
        rw [hrec] at hrec'
        simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
        obtain ⟨rfl, rfl, rfl⟩ := hrec'
        obtain ⟨-, -, -, -, -, -, hct⟩ := hr.recog_ds hd hrec (fun _ => false)
        obtain ⟨hcvd, hcvn⟩ := findDecl_eq_some hcv
        refine hidx _ ?_ cv rfl
        rw [hct]
        exact List.mem_flatMap.2 ⟨cn, hcn, by
          rw [viewFind_of (hcvn ▸ hr.vw hcvd) hcvn]; exact List.mem_singleton_self _⟩
  · have spec := closureStep_spec hcs
    obtain ⟨-, hkind⟩ := spec.2.2.2.2.2.2.2 _ rfl
    rcases hkind with ⟨d, rfl⟩ | ⟨iv, rfl⟩
    · rcases spec.2.2.2.1 d rfl with ⟨-, hnone, -⟩ | ⟨I, R', ctors, hrec, -, hro, -⟩
      · cases hnone
      · cases hro
        obtain ⟨hcas, -, -, T, hTd, hRT, -⟩ := hr.recog_ds hcj hrec (fun _ => false)
        refine .inl ⟨T, I, hRT, hTd ▸ hcas, ?_⟩
        rw [← hTd, show d.name = (ConstantInfo.defnInfo d).name from rfl, hr.fd hcj]
        rfl
    · obtain ⟨hlen, hvf, -⟩ := (spec.2.2.2.2.2.1 iv rfl).2 _ rfl
      obtain ⟨-, hRn⟩ := viewFind_eq hvf
      exact .inr ⟨iv.name, iv, hRn, hr.fd hcj, hlen⟩

end Run

end CollectSpec

open CollectSub CollectSpec NonRec in
/-- What the fragment test's closure satisfies on a program read through a view that agrees with
it: distinct names and kernames, the view's declarations, closed under what the traversal reads,
closed expressions, the constants of `e`, every declaration in the first-phase fragment
(`PhaseIDecl`), no recursor read (`RecFree`), distinct λ□ block names (`BlockNamesInj`) and
syntactic arities as inductive types (`ArityTypes`) (port of `L4 Core/Collect.lean:214`). -/
theorem collectDeps_spec {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P decls : List ConstantInfo} {lps : List Name} {e : Expr} {t : Metalean.Expr ζ lps.length 0}
    {view : EnvView} {cfg : ErasureConfig} (henv : ProgEnv P ζ E B)
    (hview : ViewAgrees view P) (he : TrM E B lps .nil [] e t)
    (h : collectDeps view cfg e = .ok decls) :
    KernameInj decls ∧ (∀ ci ∈ decls, view.find? ci.name = some ci) ∧
      (decls.map (·.name)).Nodup ∧ DepClosed decls ∧ ClosedDecls decls ∧
      ConstsIn (fun c => (findDecl decls c).isSome) e ∧
      (∀ ci ∈ decls, PhaseIDecl view cfg decls ci) ∧
      (RecFree decls e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecFree decls x) ∧
      BlockNamesInj decls ∧ ArityTypes decls := by
  obtain ⟨cs, cases, hcs, hcl, hel, hcol, hbc⟩ := CollectSpec.collectDeps_ok h
  obtain ⟨hsub, hnd, -, -, hcov, hscan⟩ := closure_ok henv hview hcl nofun
    ((TrM.namesIn henv he).exprConsts hcs) List.nodup_nil nofun
  have hr : Run P view cfg decls cases := ⟨ProgEnv.names_closed henv, hview, hsub, hscan⟩
  have covIn : ∀ n, Covered decls n → (findDecl decls n).isSome = true :=
    fun n h => findDecl_isSome_iff.2 h.mem
  have covRec : ∀ n, Covered decls n → IsRecursorIn decls n = false := by
    intro n h
    obtain ⟨y, hy, -, hnr⟩ := hr.cov h
    unfold IsRecursorIn
    rw [hy]
    cases y with
    | recInfo R => exact absurd rfl (hnr R)
    | _ => rfl
  have hcsC := exprConsts_ok hcs
  refine ⟨KernameInj.of_findCollision hcol, fun ci hci => hr.vw hci, hnd, fun ci hci => ?_,
    fun ci hci x hx => ?_, ConstsIn_mono (fun c hc => covIn c (hcov c hc)) hcsC.1,
    fun ci hci => hr.phase hel hci,
    ⟨ConstsIn_mono (fun c hc => covRec c (hcov c hc)) hcsC.1, fun ci hci x hx => ?_⟩,
    BlockNamesInj.of_findBlockCollision hbc, ?_⟩
  · refine ⟨fun x hx => ?_, fun n hn => ?_, fun iv hiv n hn => ?_, fun cv hcv => ?_,
      fun R hR n hn => ?_⟩
    · obtain ⟨xs, hxs, hxc⟩ := hr.read hci hx
      exact ConstsIn_mono (fun c hc => covIn c (hxc c hc)) (exprConsts_ok hxs).1
    · rcases hr.scan ci hci with ⟨ns, ro, hcs', hns, -⟩ | ⟨R, rfl, -⟩
      · rcases (closureStep_spec hcs').2.2.1 n hn with h | h
        · exact covIn n (hns n h)
        · rw [h, hr.fd hci]; rfl
      · simp only [ConstantInfo.all, List.mem_singleton] at hn
        rw [hn, hr.fd hci]; rfl
    · subst hiv
      exact covIn n ((hr.ind_reads hci).1 n hn)
    · subst hcv
      obtain ⟨ns, ro, hcs', hns, -⟩ := hr.scanned hci nofun
      exact covIn _ (hns _ ((closureStep_spec hcs').2.2.2.2.2.2.1 cv rfl))
    · subst hR
      exact covIn n (hr.recr_all hci n hn)
  · obtain ⟨xs, hxs, -⟩ := hr.read hci hx
    exact (exprConsts_ok hxs).2.2
  · obtain ⟨xs, hxs, hxc⟩ := hr.read hci hx
    exact ConstsIn_mono (fun c hc => covRec c (hxc c hc)) (exprConsts_ok hxs).1
  · rintro iv ⟨ci, hci, rfl⟩
    obtain ⟨ns, ro, hcs', -⟩ := hr.scanned hci nofun
    obtain ⟨-, -, b, hb⟩ := (declExclusion_ok (closureStep_spec hcs').1).2.2.2.2.2.1 iv rfl
    obtain ⟨n, u, hsh, -⟩ := sortDecided_ok hb
    rw [hsh]; rfl

end EraseProof
