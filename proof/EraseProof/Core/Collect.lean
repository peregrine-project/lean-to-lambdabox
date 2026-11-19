import EraseProof.Bridge.CLNames
import EraseProof.Source.Decls
import EraseProof.Statements

/-!
# The closure of the fragment test is a sub-environment of the program

`collectDeps_sub`: on a program con-leche accepts (`ConLecheAccepts`), read through a view that
agrees with it (`ViewAgrees`), the closure that a successful `Erasure.collectDeps` returns for a
term con-leche types consists of declarations of the program. Every name the closure reads is a
name of the program: the constants of the term (`CLTyped.knownIn`), the names each scanned
declaration reads (`ConLecheAccepts.namesClosed`), and the constants of the compiled
pre-definitions, which `ViewAgrees` puts in the program. Port of `ML-V Core/Collect.lean`, with
con-leche's acceptance where that file has Metalean's `ProgEnv`. Reference: `L4 Core/Scope.lean:279`.
-/

open Lean Erasure

namespace EraseProof

namespace CollectSub

open Decls

/-- A successful `Except` bind ran its first part successfully. Port of
`ML-V Oracle/Whnf.lean:71`. -/
theorem ok_of_bind {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

/-- Every name a successful `exprConsts` lists is a constant of the term, a projection's
structure, or `Nat` for a Nat literal. Port of `ML-V Core/Collect.lean:68`. -/
theorem exprConsts_mem {cfg : ErasureConfig} {p : Name → Prop} :
    ∀ {e : Expr} {cs : List Name}, exprConsts cfg e = .ok cs → ConstsIn p e →
      (HasNatLit e = true → p ``Nat) → ∀ c ∈ cs, p c
  | .bvar _, cs, h, _, _ => by rw [exprConsts] at h; cases h; simp
  | .fvar _, _, h, _, _ | .mvar _, _, h, _, _ => by rw [exprConsts] at h; cases h
  | .sort _, cs, h, _, _ => by
    rw [exprConsts] at h
    split at h
    · cases h
    · cases h; simp
  | .const c _, cs, h, hc, _ => by
    rw [exprConsts] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h; intro c' hm; rw [List.mem_singleton.1 hm]; exact hc
      · cases h; intro c' hm; rw [List.mem_singleton.1 hm]; exact hc
  | .app f a, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, hf, h⟩ := ok_of_bind h
    obtain ⟨ys, ha, h⟩ := ok_of_bind h
    cases h
    simp only [HasNatLit, Bool.or_eq_true] at hn
    intro c hm
    rcases List.mem_append.1 hm with hm | hm
    · exact exprConsts_mem hf hc.1 (fun h => hn (.inl h)) c hm
    · exact exprConsts_mem ha hc.2 (fun h => hn (.inr h)) c hm
  | .lam _ t b _, cs, h, hc, hn | .forallE _ t b _, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := ok_of_bind h
    obtain ⟨ys, hb, h⟩ := ok_of_bind h
    cases h
    simp only [HasNatLit, Bool.or_eq_true] at hn
    intro c hm
    rcases List.mem_append.1 hm with hm | hm
    · exact exprConsts_mem ht hc.1 (fun h => hn (.inl h)) c hm
    · exact exprConsts_mem hb hc.2 (fun h => hn (.inr h)) c hm
  | .letE _ t v b _, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := ok_of_bind h
    obtain ⟨ys, hv, h⟩ := ok_of_bind h
    obtain ⟨zs, hb, h⟩ := ok_of_bind h
    cases h
    simp only [HasNatLit, Bool.or_eq_true] at hn
    intro c hm
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact exprConsts_mem ht hc.1 (fun h => hn (.inl (.inl h))) c hm
    · exact exprConsts_mem hv hc.2.1 (fun h => hn (.inl (.inr h))) c hm
    · exact exprConsts_mem hb hc.2.2 (fun h => hn (.inr h)) c hm
  | .lit (.natVal _), cs, h, _, hn => by
    rw [exprConsts] at h
    split at h
    · cases h
    · cases h; simpa using hn rfl
  | .lit (.strVal _), _, h, _, _ => by rw [exprConsts] at h; cases h
  | .mdata _ e, cs, h, hc, hn => by
    rw [exprConsts] at h
    exact exprConsts_mem h hc hn
  | .proj S _ e, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, he, h⟩ := ok_of_bind h
    cases h
    intro c hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hc.1
    · exact exprConsts_mem he hc.2 hn c hm

/-- The names a successful `exprConsts` lists, on an expression whose names are in `P`. -/
theorem KnownIn.exprConsts {P : List ConstantInfo} {cfg : ErasureConfig} {x : Expr}
    {cs : List Name} (hx : KnownIn P x) (h : Erasure.exprConsts cfg x = .ok cs) :
    ∀ c ∈ cs, (findDecl P c).isSome = true :=
  exprConsts_mem h hx.1 hx.2

/-! ## The view on the program -/

variable {P : List ConstantInfo} {env : ConLeche.Env} {view : EnvView}

/-- The declaration the view returns for a name of the program is a declaration of the program.
Port of `ML-V Core/Collect.lean:342`. -/
theorem view_mem (hview : ViewAgrees view P) {n : Name} {ci : ConstantInfo}
    (hn : (findDecl P n).isSome = true) (hf : view.find? n = some ci) : ci ∈ P := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨hxP, rfl⟩ := findDecl_mem hx
  rw [(hview x hxP).1] at hf
  cases hf
  exact hxP

/-- A singleton lookup through the view is the view's declaration of that name. Port of
`ML-V Core/Collect.lean:363`. -/
theorem viewFind_eq {n : Name} {ci : ConstantInfo}
    (h : viewFind view n = [ci]) : view.find? n = some ci ∧ ci.name = n := by
  unfold viewFind at h
  cases hf : view.find? n with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    by_cases hx : x.name = n
    · simp [Option.filter, hx] at h
      subst h
      exact ⟨rfl, hx⟩
    · simp [Option.filter, hx] at h

/-- A declaration a lookup through the view returns is the view's, under that name. Port of
`ML-V Core/CollectSpec.lean:900`. -/
theorem viewFind_mem {n : Name} {y : ConstantInfo} (h : y ∈ viewFind view n) :
    view.find? n = some y ∧ y.name = n := by
  unfold viewFind at h
  cases hf : view.find? n with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    by_cases hx : x.name = n
    · simp [Option.filter, hx] at h
      subst h
      exact ⟨rfl, hx⟩
    · simp [Option.filter, hx] at h

/-- A `casesOn` recognized through the view, on a definition of the program whose value has its
constants in the program, has its recursor and its inductive in the program: the value's head is
the recursor (`casesInfo?_reads`), whose block, which holds the inductive, is in the program
(`NamesClosed.recr`). Port of `ML-V Core/Collect.lean:381`. -/
theorem recognize_mem (hP : ConLecheAccepts P env) (hview : ViewAgrees view P)
    {d : DefinitionVal} (hv : KnownIn P d.value) {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} (h : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors)) :
    .recInfo R ∈ P ∧ .inductInfo I ∈ P := by
  unfold recognizeCasesOn at h
  split at h
  next T hT =>
    split at h
    next I' R' hI hR =>
      obtain ⟨ci', hc, heq⟩ := Option.map_eq_some_iff.1 h
      cases heq
      obtain ⟨hIf, hIn⟩ := viewFind_eq hI
      obtain ⟨hRf, hRn⟩ := viewFind_eq hR
      obtain ⟨T', d', I'', R'', k, body, us, hn, -, hd', -, hR'', hTR, hb, hhd⟩ :=
        casesInfo?_reads hc
      have hTT : T' = T := by rw [hT] at hn; injection hn with h; exact h.symm
      rw [hTT] at hR'' hTR
      -- the definition the recognizer reads is `d`
      have hdd : d' = d := by
        simp [findDecl] at hd'
        subst hd'; rfl
      subst hdd
      -- the recursor named `T.rec` in the recognizer's list is the view's `T.rec`
      obtain ⟨hR''m, hR''n⟩ := findDecl_mem hR''
      have hRR : R'' = R := by
        rcases List.mem_cons.mp hR''m with he | he
        · cases he
        rcases List.mem_cons.mp he with he | he
        · cases he
        rcases List.mem_cons.mp he with he | he
        · cases he; rfl
        have hv' : ∃ n', ConstantInfo.recInfo R'' ∈ viewFind view n' := by
          rcases List.mem_append.mp he with he | he
          · obtain ⟨n', -, hn'⟩ := List.mem_flatMap.mp he; exact ⟨n', hn'⟩
          · obtain ⟨n', -, hn'⟩ := List.mem_flatMap.mp he; exact ⟨n', hn'⟩
        obtain ⟨n', hn'⟩ := hv'
        obtain ⟨hf', hn''⟩ := viewFind_mem hn'
        rw [← hn'', hR''n, hRf] at hf'
        cases hf'; rfl
      subst hRR
      have hbody := ConstsIn_spine (ConstsIn_peelLams hb hv.1)
      rw [hhd] at hbody
      have hRP : .recInfo R'' ∈ P := view_mem hview (hR''n ▸ hbody) hRf
      have hrc := (hP.namesClosed hRP nofun nofun nofun).recr R'' rfl T hTR
      exact ⟨hRP, view_mem hview hrc (hIn ▸ hIf)⟩
    next => cases h
  next => cases h

/-! ## The closure -/

/-- A successful `if` whose else branch fails took its then branch. Port of
`ML-V Core/CollectSpec.lean:202`. -/
theorem ite_ok_then {ε α : Type} {c : Prop} [Decidable c] {a b : Except ε α} {x : α}
    (h : (if c then a else b) = .ok x) (hb : ∀ y, b ≠ .ok y) : c ∧ a = .ok x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h; exact absurd h (hb x)

/-- A successful `if` whose then branch fails took its else branch. Port of
`ML-V Core/CollectSpec.lean:209`. -/
theorem ite_ok_else {ε α : Type} {c : Prop} [Decidable c] {a b : Except ε α} {x : α}
    (h : (if c then a else b) = .ok x) (ha : ∀ y, a ≠ .ok y) : ¬ c ∧ b = .ok x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact absurd h (ha x)
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

/-- The safety and block checks `declExclusion` makes, on a declaration it accepts. Part of
`ML-V Core/CollectSpec.lean:232 declExclusion_ok`. -/
theorem declExclusion_flags {cfg : ErasureConfig} {ci : ConstantInfo} {u : Unit}
    (h : declExclusion view cfg ci = .ok u) :
    (∀ d, ci = .defnInfo d → d.safety = .safe ∧ d.all = [d.name]) ∧
    (∀ t, ci = .thmInfo t → t.all = [t.name]) ∧
    (∀ o, ci = .opaqueInfo o → o.isUnsafe = false ∧ o.all = [o.name]) ∧
    (∀ a, ci = .axiomInfo a → a.isUnsafe = false) := by
  have thr : ∀ {α : Type} {e : EraseError} {f : Unit → Except EraseError α} (y : α),
      (throw e >>= f) ≠ .ok y := fun _ h => nomatch h
  have thr' : ∀ {α : Type} {e : EraseError} (y : α), (throw e : Except EraseError α) ≠ .ok y :=
    fun _ h => nomatch h
  cases ci with
  | defnInfo d =>
    rw [declExclusion] at h
    refine ⟨fun d' hd => ?_, nofun, nofun, nofun⟩
    cases hd
    obtain ⟨h1, h⟩ := ite_ok_then h thr
    dsimp only at h
    obtain ⟨-, h⟩ := ite_ok_else h thr
    obtain ⟨-, h⟩ := ite_ok_else h thr
    obtain ⟨h4, -⟩ := ite_ok_then h thr'
    exact ⟨by revert h1; cases d.safety <;> simp, by simpa using h4⟩
  | thmInfo t =>
    rw [declExclusion] at h
    exact ⟨nofun, fun t' ht => by cases ht; simpa using (ite_ok_then h thr').1, nofun, nofun⟩
  | opaqueInfo o =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, fun o' ho => ?_, nofun⟩
    cases ho
    obtain ⟨h1, h⟩ := ite_ok_else h thr
    dsimp only at h
    obtain ⟨-, h⟩ := ite_ok_else h thr
    obtain ⟨-, h⟩ := ite_ok_else h thr
    obtain ⟨h4, -⟩ := ite_ok_then h thr'
    exact ⟨by simpa using h1, by simpa using h4⟩
  | axiomInfo a =>
    rw [declExclusion] at h
    refine ⟨nofun, nofun, nofun, fun a' ha => ?_⟩
    cases ha
    obtain ⟨h1, -⟩ := ite_ok_else h thr
    simpa using h1
  | quotInfo _ | inductInfo _ | ctorInfo _ | recInfo _ => exact ⟨nofun, nofun, nofun, nofun⟩

/-- On a declaration of the program, a step of the closure reads names of the program and adds a
recursor of the program as companion. Port of `ML-V Core/Collect.lean:463`. -/
theorem closureStep_sub (hP : ConLecheAccepts P env) (hview : ViewAgrees view P)
    {cfg : ErasureConfig} {ci : ConstantInfo} (hci : ci ∈ P) {ns : List Name}
    {ro : Option ConstantInfo} (h : closureStep view cfg ci = .ok (ns, ro)) :
    (∀ n ∈ ns, (findDecl P n).isSome = true) ∧ ∀ r, ro = some r → r ∈ P ∧ ∃ R, r = .recInfo R := by
  obtain ⟨ds, hds, -⟩ := id hP
  have hself : (findDecl P ci.name).isSome = true := by
    rw [findDecl_self (DeclsOf?.nodup hds) hci]; rfl
  unfold closureStep at h
  obtain ⟨_, hex, h⟩ := ok_of_bind h
  obtain ⟨hdef, hthm, hopq, hax⟩ := declExclusion_flags hex
  have hc := hP.namesClosed hci (fun d hd => (hdef d hd).1) hax (fun o ho => (hopq o ho).1)
  obtain ⟨ty, hty, h⟩ := ok_of_bind h
  have hty' := KnownIn.exprConsts hc.type hty
  cases ci with
  | defnInfo d =>
    have hall := (hdef d rfl).2
    dsimp only at h
    split at h
    · rename_i I R ctors hrec
      obtain ⟨_, -, h⟩ := ok_of_bind h
      cases h
      obtain ⟨hR, hI⟩ := recognize_mem hP hview (hc.defn d rfl) hrec
      refine ⟨fun n hn => ?_, fun r hr => ?_⟩
      · simp only [List.mem_append, List.mem_cons] at hn
        rcases hn with hn | rfl | hn
        · exact hty' n hn
        · rw [show findDecl P I.name = some (.inductInfo I) from
            findDecl_self (DeclsOf?.nodup hds) hI]; rfl
        · rw [hall, List.mem_singleton] at hn; rw [hn]; exact hself
      · cases hr; exact ⟨hR, _, rfl⟩
    · obtain ⟨ps, hps, h⟩ : ∃ ps, (∀ n ∈ ps, (findDecl P n).isSome = true) ∧
          (do let __do_lift ← exprConsts cfg d.value
              pure (ty ++ __do_lift ++ ps ++ d.all, none) : Except EraseError _) = .ok (ns, ro) := by
        rcases hp : preDef? view cfg (.defnInfo d) with _ | p <;> rw [hp] at h
        · exact ⟨[], nofun, h⟩
        · obtain ⟨ps, hps, h⟩ := ok_of_bind h
          exact ⟨ps, KnownIn.exprConsts ((hview _ hci).2 cfg p hp) hps, h⟩
      obtain ⟨vs, hvs, h⟩ := ok_of_bind h
      cases h
      have hv' := KnownIn.exprConsts (hc.defn d rfl) hvs
      refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
      simp only [List.mem_append] at hn
      rcases hn with ((hn | hn) | hn) | hn
      · exact hty' n hn
      · exact hv' n hn
      · exact hps n hn
      · rw [hall, List.mem_singleton] at hn; rw [hn]; exact hself
  | thmInfo t =>
    cases h
    refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact hty' n hn
    · rw [hthm t rfl, List.mem_singleton] at hn; rw [hn]; exact hself
  | opaqueInfo o =>
    obtain ⟨vs, hvs, h⟩ := ok_of_bind h
    cases h
    have hv' := KnownIn.exprConsts (hc.opq o rfl) hvs
    refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
    simp only [List.mem_append] at hn
    rcases hn with (hn | hn) | hn
    · exact hty' n hn
    · exact hv' n hn
    · rw [(hopq o rfl).2, List.mem_singleton] at hn; rw [hn]; exact hself
  | inductInfo iv =>
    cases h
    obtain ⟨hall, hctors, hrec⟩ := hc.ind iv rfl
    refine ⟨fun n hn => ?_, fun r hr => ?_⟩
    · simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact hty' n hn
      · exact hall n hn
      · exact hctors n hn
    · split at hr
      · rename_i r' hv
        cases hr
        obtain ⟨hf, -⟩ := viewFind_eq hv
        exact ⟨view_mem hview hrec hf, _, rfl⟩
      · cases hr
  | ctorInfo cv =>
    cases h
    refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact hty' n hn
    · rw [List.mem_singleton.1 hn]; exact hc.ctor cv rfl
  | axiomInfo _ | quotInfo _ | recInfo _ =>
    cases h
    exact ⟨hty', fun r hr => nomatch hr⟩

/-- `dropKnown` returns a suffix of its work list. Port of `ML-V Core/Collect.lean:561`. -/
theorem dropKnown_sub {cfg : ErasureConfig} {acc : List ConstantInfo} :
    ∀ {todo todo' : List Name}, dropKnown view cfg acc todo = .ok todo' → ∀ n ∈ todo', n ∈ todo
  | [], _, h => by rw [dropKnown] at h; cases h; exact fun _ h => h
  | n :: todo, todo', h => by
    rw [dropKnown] at h
    split at h
    · obtain ⟨_, -, h⟩ := ok_of_bind h
      exact fun m hm => List.mem_cons_of_mem _ (dropKnown_sub h m hm)
    · exact fun m hm => List.mem_cons_of_mem _ (dropKnown_sub h m hm)
    · cases h; exact fun _ h => h

/-- A run of the closure from declarations and names of the program returns declarations of the
program. Port of `ML-V Core/Collect.lean:575`. -/
theorem closure_sub (hP : ConLecheAccepts P env) (hview : ViewAgrees view P)
    {cfg : ErasureConfig} :
    ∀ {f : Nat} {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name} {res : List ConstantInfo × List Name},
    closure view cfg f todo acc cases = .ok res → (∀ ci ∈ acc, ci ∈ P) →
    (∀ n ∈ todo, (findDecl P n).isSome = true) → ∀ ci ∈ res.1, ci ∈ P
  | 0, todo, acc, cases, res, h, hacc, _ => by
    rw [closure] at h
    obtain ⟨todo', -, h⟩ := ok_of_bind h
    split at h
    · cases h; exact hacc
    · cases h
  | f + 1, todo, acc, cases, res, h, hacc, htodo => by
    rw [closure] at h
    obtain ⟨todo', hd, h⟩ := ok_of_bind h
    have hsub := dropKnown_sub hd
    cases todo' with
    | nil => cases h; exact hacc
    | cons n todo'' =>
      have hn : (findDecl P n).isSome = true := htodo n (hsub n List.mem_cons_self)
      have htl : ∀ m ∈ todo'', (findDecl P m).isSome = true :=
        fun m hm => htodo m (hsub m (List.mem_cons_of_mem _ hm))
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
        obtain ⟨⟨ns, ro⟩, hcs, h⟩ := ok_of_bind h
        obtain ⟨hns, hro⟩ := closureStep_sub hP hview hciP hcs
        have hacc' : ∀ cj ∈ ci :: acc, cj ∈ P := by
          intro cj hcj
          rcases List.mem_cons.1 hcj with rfl | hcj
          · exact hciP
          · exact hacc cj hcj
        have hnt : ∀ m ∈ ns ++ todo'', (findDecl P m).isSome = true := by
          intro m hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hns m hm
          · exact htl m hm
        cases ro with
        | none => exact closure_sub hP hview h hacc' hnt
        | some r =>
          obtain ⟨hrP, R, rfl⟩ := hro r rfl
          dsimp only at h
          by_cases hfa : (findConst acc (ConstantInfo.recInfo R).name).isSome = true
          · rw [ite_eq_left hfa] at h
            exact closure_sub hP hview h hacc' hnt
          · rw [ite_eq_right hfa] at h
            obtain ⟨tys, htys, h⟩ := ok_of_bind h
            have hty' := KnownIn.exprConsts (hP.namesClosed hrP nofun nofun nofun).type htys
            refine closure_sub hP hview h ?_ fun m hm => ?_
            · intro cj hcj
              rcases List.mem_cons.1 hcj with rfl | hcj
              · exact hrP
              · exact hacc' cj hcj
            · simp only [List.mem_append] at hm
              rcases hm with (hm | hm) | hm
              · exact hns m hm
              · exact hty' m hm
              · exact htl m hm

end CollectSub

open CollectSub in
/-- **The closure of the fragment test is part of the program**: on a program con-leche accepts,
read through a view that agrees with it, the closure a successful `Erasure.collectDeps` returns
for a term con-leche types consists of declarations of the program, each the program's
declaration of its name. Port of `ML-V Core/Collect.lean:640` (`L4 Core/Scope.lean:279`).
Reference: `erase_global_deps` keeps a sub-environment (`MR E/ErasureFunction.v:1602`); DV-3. -/
theorem collectDeps_sub : collectDeps_sub_statement := by
  intro P decls env e view cfg hP hview hty h _
  obtain ⟨ds₀, hds₀, -⟩ := id hP
  unfold collectDeps at h
  obtain ⟨cs, hcs, h⟩ := ok_of_bind h
  obtain ⟨⟨ds, cases⟩, hcl, h⟩ := ok_of_bind h
  have hds : ∀ ci ∈ ds, ci ∈ P :=
    closure_sub hP hview hcl nofun (KnownIn.exprConsts (CLTyped.knownIn hP hty) hcs)
  have hdecls : decls = ds := by
    dsimp only at h
    repeat' (first | (cases h; rfl) | cases h | split at h)
  subst hdecls
  exact fun ci hci => findDecl_self (DeclsOf?.nodup hds₀) (hds ci hci)

end EraseProof
