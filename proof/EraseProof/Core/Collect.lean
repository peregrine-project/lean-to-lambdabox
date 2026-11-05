import EraseProof.Core.NonRec
import EraseProof.Oracle.Whnf

/-!
# The closure of the fragment test is a sub-environment of the program

`collectDeps_sub`: on a program related to a Metalean environment (`ProgEnv`) and read through a
view that agrees with it (`ViewAgrees`), the closure that a successful `Erasure.collectDeps`
returns for a translated term consists of declarations of the program. Every name the closure
reads is a name of the program: the constants of a translated expression are bound in the table
(`TrM.consts`), which binds only names of the program (`ProgEnv.bound`); the block members,
constructors, inductives and recursors the closure adds are declarations of the program's
inductive blocks (`CollectSub.ProgEnv.names_closed`). Reference: `L4 Core/Scope.lean:279`.
-/

open Lean Erasure

namespace EraseProof

namespace CollectSub

open NonRec Extend CasesShape

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-! ## Names of expressions -/

/-- A Nat literal of an application spine is one of the head or of an argument. -/
theorem HasNatLit_foldl : ∀ {f : Expr} {as : List Expr}, HasNatLit (as.foldl .app f) = true →
    HasNatLit f = true ∨ ∃ a ∈ as, HasNatLit a = true
  | _, [], h => .inl h
  | f, a :: as, h => by
    rcases HasNatLit_foldl (f := .app f a) (as := as) h with h | ⟨b, hb, h⟩
    · simp only [HasNatLit, Bool.or_eq_true] at h
      exact h.elim .inl fun h => .inr ⟨a, List.mem_cons_self, h⟩
    · exact .inr ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- A Nat literal of a translated term needs `Nat` in the table. -/
theorem TrM.natLit {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ e t) : HasNatLit e = true → B ``Nat ≠ none := by
  induction h with
  | special _ _ hlen _ _ ih =>
    intro hn
    rw [mkAppN_toArray] at hn
    rcases HasNatLit_foldl hn with hn | ⟨a, ha, hn⟩
    · simp [HasNatLit] at hn
    · exact forall_mem_of_rel (Q := fun a => HasNatLit a = true → B ``Nat ≠ none) hlen ih a ha hn
  | lit hN => intro _; simp [hN]
  | app _ _ _ ihf iha =>
    intro hn
    simp only [HasNatLit, Bool.or_eq_true] at hn
    exact hn.elim ihf iha
  | lam _ _ ihA ihb | forallE _ _ ihA ihb =>
    intro hn
    simp only [HasNatLit, Bool.or_eq_true] at hn
    exact hn.elim ihA ihb
  | letE _ _ _ ihT ihv ihb =>
    intro hn
    simp only [HasNatLit, Bool.or_eq_true] at hn
    exact hn.elim (fun h => h.elim ihT ihv) ihb
  | mdata _ ih => exact ih
  | projStruct _ _ _ _ _ ih => exact ih
  | projProof _ _ _ _ _ _ _ _ _ ih => exact ih
  | bvar | fvar | sort | const => intro hn; simp [HasNatLit] at hn

/-- Every name a successful `exprConsts` lists is a constant of the term, a projection's
structure, or `Nat` for a Nat literal. -/
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
    obtain ⟨xs, hf, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, ha, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    simp only [HasNatLit, Bool.or_eq_true] at hn
    intro c hm
    rcases List.mem_append.1 hm with hm | hm
    · exact exprConsts_mem hf hc.1 (fun h => hn (.inl h)) c hm
    · exact exprConsts_mem ha hc.2 (fun h => hn (.inr h)) c hm
  | .lam _ t b _, cs, h, hc, hn | .forallE _ t b _, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hb, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    simp only [HasNatLit, Bool.or_eq_true] at hn
    intro c hm
    rcases List.mem_append.1 hm with hm | hm
    · exact exprConsts_mem ht hc.1 (fun h => hn (.inl h)) c hm
    · exact exprConsts_mem hb hc.2 (fun h => hn (.inr h)) c hm
  | .letE _ t v b _, cs, h, hc, hn => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hv, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨zs, hb, h⟩ := OracleWhnf.ok_of_bind h
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
    obtain ⟨xs, he, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    intro c hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hc.1
    · exact exprConsts_mem he hc.2 hn c hm

/-! ## The names a program's declarations read -/

/-- The constants of `x` and `Nat` if `x` has a Nat literal are names of `P`. -/
def NamesIn (P : List ConstantInfo) (x : Expr) : Prop :=
  ConstsIn (· ∈ P.map (·.name)) x ∧ (HasNatLit x = true → ``Nat ∈ P.map (·.name))

/-- What the closure reads from a declaration of the program is a name of the program: the names of
its type, of a definition's or an opaque's value, its block members, the constructors and the
recursor of an inductive, the inductive of a constructor, and the inductive of a recursor. -/
structure NamesClosed (P : List ConstantInfo) (ci : ConstantInfo) : Prop where
  type : NamesIn P ci.type
  defn : ∀ d, ci = .defnInfo d → NamesIn P d.value
  opq : ∀ o, ci = .opaqueInfo o → NamesIn P o.value
  all : ∀ n ∈ ci.all, n ∈ P.map (·.name)
  induct : ∀ iv, ci = .inductInfo iv → (∀ n ∈ iv.ctors, n ∈ P.map (·.name)) ∧
    ∃ R, .recInfo R ∈ P ∧ R.name = mkRecName iv.name
  ctor : ∀ cv, ci = .ctorInfo cv → cv.induct ∈ P.map (·.name)
  recr : ∀ R, ci = .recInfo R → ∃ iv, .inductInfo iv ∈ P ∧ R.name = mkRecName iv.name

theorem names_mono {P P' : List ConstantInfo} (hs : ∀ x ∈ P, x ∈ P') {c : Name}
    (h : c ∈ P.map (·.name)) : c ∈ P'.map (·.name) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact List.mem_map_of_mem (hs x hx)

theorem NamesIn.mono {P P' : List ConstantInfo} (hs : ∀ x ∈ P, x ∈ P') {x : Expr}
    (h : NamesIn P x) : NamesIn P' x :=
  ⟨ConstsIn_mono (fun _ hc => names_mono hs hc) h.1, fun hn => names_mono hs (h.2 hn)⟩

theorem NamesClosed.mono {P P' : List ConstantInfo} (hs : ∀ x ∈ P, x ∈ P') {ci : ConstantInfo}
    (h : NamesClosed P ci) : NamesClosed P' ci := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.mono hs, fun d hd => (h2 d hd).mono hs, fun o ho => (h3 o ho).mono hs,
    fun n hn => names_mono hs (h4 n hn), fun iv hiv => ?_, fun cv hcv => names_mono hs (h6 cv hcv),
    fun R hR => ?_⟩
  · obtain ⟨hc, R, hR, hn⟩ := h5 iv hiv
    exact ⟨fun n hn => names_mono hs (hc n hn), R, hs _ hR, hn⟩
  · obtain ⟨iv, hiv, hn⟩ := h7 R hR
    exact ⟨iv, hs _ hiv, hn⟩

/-- The names of a translated term are names of the program. -/
theorem TrM.namesIn (hP : ProgEnv P ζ E B) {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) : NamesIn P e :=
  ⟨ConstsIn_mono (fun _ hc => hP.bound hc) (TrM.consts h), fun hn => hP.bound (TrM.natLit h hn)⟩

theorem sub_cons {x : ConstantInfo} {P : List ConstantInfo} : ∀ y ∈ P, y ∈ x :: P :=
  fun _ h => List.mem_cons_of_mem _ h

theorem sub_append {l P : List ConstantInfo} : ∀ y ∈ P, y ∈ l ++ P :=
  fun _ h => List.mem_append_right _ h

theorem block_mem {ι : Metalean.IndSig} {Is : Fin ι.nsorts → InductiveVal}
    {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal} {Rs : Fin ι.nsorts → RecursorVal} :
    (∀ s, ConstantInfo.recInfo (Rs s) ∈ IndBlock.decls Is Cs Rs) ∧
    (∀ s c, ConstantInfo.ctorInfo (Cs s c) ∈ IndBlock.decls Is Cs Rs) ∧
    (∀ s, ConstantInfo.inductInfo (Is s) ∈ IndBlock.decls Is Cs Rs) := by
  refine ⟨fun s => ?_, fun s c => ?_, fun s => ?_⟩ <;>
    simp [IndBlock.decls, List.mem_ofFn, List.mem_flatten]
  exact ⟨s, c, rfl⟩

/-- Every declaration of a program reads only names of the program. -/
theorem ProgEnv.names_closed (h : ProgEnv P ζ E B) : ∀ ci ∈ P, NamesClosed P ci := by
  induction h with
  | nil => intro ci hci; cases hci
  | «axiom» hP _ _ _ ht ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨(TrM.namesIn hP ht).mono sub_cons, nofun, nofun,
        fun n hn => ?_, nofun, nofun, nofun⟩
      simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn; exact List.mem_map_of_mem List.mem_cons_self
    · exact (ih ci hci).mono sub_cons
  | defn hP _ _ _ hall ht hv ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨(TrM.namesIn hP ht).mono sub_cons, fun d hd => ?_, nofun,
        fun n hn => ?_, nofun, nofun, nofun⟩
      · cases hd; exact (TrM.namesIn hP hv).mono sub_cons
      · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
        subst hn; exact List.mem_map_of_mem List.mem_cons_self
    · exact (ih ci hci).mono sub_cons
  | thm hP _ _ hall _ ht _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨(TrM.namesIn hP ht).mono sub_cons, nofun, nofun,
        fun n hn => ?_, nofun, nofun, nofun⟩
      simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn; exact List.mem_map_of_mem List.mem_cons_self
    · exact (ih ci hci).mono sub_cons
  | «opaque» hP _ _ _ hall ht hv _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨(TrM.namesIn hP ht).mono sub_cons, nofun, fun o ho => ?_,
        fun n hn => ?_, nofun, nofun, nofun⟩
      · cases ho; exact (TrM.namesIn hP hv).mono sub_cons
      · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
        subst hn; exact List.mem_map_of_mem List.mem_cons_self
    · exact (ih ci hci).mono sub_cons
  | @induct _ P _ _ _ _ _ _ Is Cs Rs _ hP hnd hfr hlp hext hblk hct ih =>
    have hfull := ProgEnv.induct hP hnd hfr hlp hext hblk hct
    intro ci hci
    have nm : ∀ x, x ∈ IndBlock.decls Is Cs Rs → x.name ∈ (IndBlock.decls Is Cs Rs ++ P).map (·.name) :=
      fun x hx => List.mem_map_of_mem (List.mem_append_left _ hx)
    rcases List.mem_append.1 hci with hm | hci
    · obtain ⟨T, t₀, hT, -, -⟩ := hct ci hm
      rcases IndBlock.mem_decls hm with ⟨s, rfl⟩ | ⟨s, k, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨TrM.namesIn hfull hT, nofun, nofun, fun n hn => ?_, nofun,
          nofun, fun R hR => ?_⟩
        · simp only [ConstantInfo.all, List.mem_singleton] at hn
          subst hn; exact nm _ hm
        · cases hR
          exact ⟨_, List.mem_append_left _ (block_mem.2.2 s), (hblk.recr s).1⟩
      · refine ⟨TrM.namesIn hfull hT, nofun, nofun, fun n hn => ?_, nofun,
          fun cv hcv => ?_, nofun⟩
        · simp only [ConstantInfo.all, List.mem_singleton] at hn
          subst hn; exact nm _ hm
        · cases hcv
          rw [(hblk.ctor s k).2.2.1]
          exact nm _ (block_mem.2.2 s)
      · refine ⟨TrM.namesIn hfull hT, nofun, nofun, fun n hn => ?_, fun iv hiv => ?_,
          nofun, nofun⟩
        · simp only [ConstantInfo.all, (hblk.ind s).2.2.1, List.mem_ofFn] at hn
          obtain ⟨t, rfl⟩ := hn
          exact nm _ (block_mem.2.2 t)
        · cases hiv
          refine ⟨fun n hn => ?_, _, List.mem_append_left _ (block_mem.1 s), (hblk.recr s).1⟩
          rw [(hblk.ind s).2.2.2.2.2.1, List.mem_ofFn] at hn
          obtain ⟨c, rfl⟩ := hn
          exact nm _ (block_mem.2.1 s c)
    · exact (ih ci hci).mono sub_append
  | quot hP hEq hqn hfr hlp hext hq ih =>
    have hfull := ProgEnv.quot hP hEq hqn hfr hlp hext hq
    intro ci hci
    rcases List.mem_append.1 hci with hm | hci
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hm
      obtain ⟨T, t₀, hT, -, -⟩ := (hq q (List.mem_reverse.1 hq')).2
      refine ⟨TrM.namesIn hfull hT, nofun, nofun, fun n hn => ?_,
        nofun, nofun, nofun⟩
      simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn; exact List.mem_map_of_mem hci
    · exact (ih ci hci).mono sub_append

/-! ## The view on the program -/

/-- The declaration the view returns for a name of the program is a declaration of the program. -/
theorem view_mem {view : EnvView} (hview : ViewAgrees view P) {n : Name} {ci : ConstantInfo}
    (hn : n ∈ P.map (·.name)) (hf : view.find? n = some ci) : ci ∈ P := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
  rw [hview x hx] at hf
  cases hf
  exact hx

/-- A declaration of the program is the first of its name. -/
theorem findDecl_of_view {view : EnvView} (hview : ViewAgrees view P) {ci : ConstantInfo}
    (hci : ci ∈ P) : findDecl P ci.name = some ci := by
  cases hy : findDecl P ci.name with
  | none => exact absurd (List.mem_map_of_mem hci) (not_mem_of_findDecl_none hy)
  | some y =>
    obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
    have h1 := hview y hy1
    rw [hy2, hview ci hci] at h1
    cases h1
    rfl

/-- A singleton lookup through the view is the view's declaration of that name. -/
theorem viewFind_eq {view : EnvView} {n : Name} {ci : ConstantInfo}
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

theorem mkRecName_inj {a b : Name} (h : mkRecName a = mkRecName b) : a = b := by
  unfold mkRecName at h
  injection h

/-- A `casesOn` recognized through the view, on a definition of the program, has its inductive and
its recursor in the program. -/
theorem recognize_mem (hP : ProgEnv P ζ E B) {view : EnvView} (hview : ViewAgrees view P)
    {d : DefinitionVal} (hd : .defnInfo d ∈ P) {I : InductiveVal} {R : RecursorVal}
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
      have hrec : mkRecName T ∈ P.map (·.name) := by
        rw [hT] at hc
        unfold casesInfo? at hc
        split at hc
        next T₁ hT₁ =>
          have hTT : T₁ = T := by injection hT₁ with h; exact h.symm
          subst hTT
          split at hc
          next d' I'' R'' hd' hI'' hR'' =>
            dsimp only at hc
            split at hc
            next j body alts before hj hb ha hbe =>
              split at hc
              next hok =>
                simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
                  List.mem_range] at hok
                obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hhd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
                have hdd : d' = d := by
                  rw [← hT] at hd'
                  simp only [findConst, List.cons_append, List.find?_cons, beq_self_eq_true,
                    Option.some.injEq, ConstantInfo.defnInfo.injEq] at hd'
                  exact hd'.symm
                subst hdd
                have hRn'' : R''.name = mkRecName T₁ := (findDecl_eq_some (l := _) hR'').2
                have hv := ((ProgEnv.names_closed hP _ hd).defn _ rfl).1
                have hbody := ConstsIn_peelLams hb hv
                rw [← spine_mkAppN body] at hbody
                have hhd' := (ConstsIn_mkAppN.1 hbody).1
                rw [isConstAt_iff hhd] at hhd'
                exact hRn'' ▸ hhd'
              next => cases hc
            next => cases hc
          next => cases hc
        next => cases hc
      have hRP : .recInfo R ∈ P := view_mem hview hrec hRf
      obtain ⟨iv, hiv, hivn⟩ := (ProgEnv.names_closed hP _ hRP).recr R rfl
      have hT' : iv.name = T := mkRecName_inj (hivn.symm.trans hRn)
      exact ⟨hRP, view_mem hview (hT' ▸ List.mem_map_of_mem hiv) hIf⟩
    next => cases h
  next => cases h

/-! ## The closure -/

/-- The names a successful `exprConsts` lists, on an expression whose names are in `P`. -/
theorem NamesIn.exprConsts {cfg : ErasureConfig} {x : Expr} {cs : List Name} (hx : NamesIn P x)
    (h : exprConsts cfg x = .ok cs) : ∀ c ∈ cs, c ∈ P.map (·.name) :=
  exprConsts_mem h hx.1 hx.2

/-- On a declaration of the program, a step of the closure reads names of the program and adds a
companion of the program. -/
theorem closureStep_sub (hP : ProgEnv P ζ E B) {view : EnvView} (hview : ViewAgrees view P)
    {cfg : ErasureConfig} {ci : ConstantInfo} (hci : ci ∈ P) {ns : List Name}
    {ro : Option ConstantInfo} (h : closureStep view cfg ci = .ok (ns, ro)) :
    (∀ n ∈ ns, n ∈ P.map (·.name)) ∧ ∀ r, ro = some r → r ∈ P := by
  have hc := ProgEnv.names_closed hP ci hci
  unfold closureStep at h
  obtain ⟨_, -, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨ty, hty, h⟩ := OracleWhnf.ok_of_bind h
  have hty' := hc.type.exprConsts hty
  cases ci with
  | defnInfo d =>
    dsimp only at h
    split at h
    · rename_i I R ctors hrec
      obtain ⟨_, -, h⟩ := OracleWhnf.ok_of_bind h
      cases h
      obtain ⟨hR, hI⟩ := recognize_mem hP hview hci hrec
      refine ⟨fun n hn => ?_, fun r hr => ?_⟩
      · simp only [List.mem_append, List.mem_cons] at hn
        rcases hn with hn | rfl | hn
        · exact hty' n hn
        · exact List.mem_map_of_mem hI
        · exact hc.all n hn
      · cases hr; exact hR
    · obtain ⟨vs, hvs, h⟩ := OracleWhnf.ok_of_bind h
      cases h
      have hv' := (hc.defn d rfl).exprConsts hvs
      refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
      simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact hty' n hn
      · exact hv' n hn
      · exact hc.all n hn
  | thmInfo t =>
    cases h
    refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact hty' n hn
    · exact hc.all n hn
  | opaqueInfo o =>
    obtain ⟨vs, hvs, h⟩ := OracleWhnf.ok_of_bind h
    cases h
    have hv' := (hc.opq o rfl).exprConsts hvs
    refine ⟨fun n hn => ?_, fun r hr => nomatch hr⟩
    simp only [List.mem_append] at hn
    rcases hn with (hn | hn) | hn
    · exact hty' n hn
    · exact hv' n hn
    · exact hc.all n hn
  | inductInfo iv =>
    cases h
    obtain ⟨hctors, R, hR, hRn⟩ := hc.induct iv rfl
    refine ⟨fun n hn => ?_, fun r hr => ?_⟩
    · simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact hty' n hn
      · exact hc.all n hn
      · exact hctors n hn
    · split at hr
      · rename_i r' hv
        cases hr
        obtain ⟨hf, -⟩ := viewFind_eq hv
        exact view_mem hview (hRn ▸ List.mem_map_of_mem hR) hf
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

/-- `dropKnown` returns a suffix of its work list. -/
theorem dropKnown_sub {acc : List ConstantInfo} :
    ∀ {todo todo' : List Name}, dropKnown acc todo = .ok todo' → ∀ n ∈ todo', n ∈ todo
  | [], _, h => by rw [dropKnown] at h; cases h; exact fun _ h => h
  | n :: todo, todo', h => by
    rw [dropKnown] at h
    split at h
    · cases h
    · exact fun m hm => List.mem_cons_of_mem _ (dropKnown_sub h m hm)
    · cases h; exact fun _ h => h

/-- A run of the closure from declarations and names of the program returns declarations of the
program. -/
theorem closure_sub (hP : ProgEnv P ζ E B) {view : EnvView} (hview : ViewAgrees view P)
    {cfg : ErasureConfig} : ∀ {f : Nat} {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name} {res : List ConstantInfo × List Name},
    closure view cfg f todo acc cases = .ok res → (∀ ci ∈ acc, ci ∈ P) →
    (∀ n ∈ todo, n ∈ P.map (·.name)) → ∀ ci ∈ res.1, ci ∈ P
  | 0, todo, acc, cases, res, h, hacc, _ => by
    rw [closure] at h
    obtain ⟨todo', -, h⟩ := OracleWhnf.ok_of_bind h
    split at h
    · cases h; exact hacc
    · cases h
  | f + 1, todo, acc, cases, res, h, hacc, htodo => by
    rw [closure] at h
    obtain ⟨todo', hd, h⟩ := OracleWhnf.ok_of_bind h
    have hsub := dropKnown_sub hd
    cases todo' with
    | nil => cases h; exact hacc
    | cons n todo'' =>
      have hn : n ∈ P.map (·.name) := htodo n (hsub n List.mem_cons_self)
      have htl : ∀ m ∈ todo'', m ∈ P.map (·.name) :=
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
        obtain ⟨⟨ns, ro⟩, hcs, h⟩ := OracleWhnf.ok_of_bind h
        obtain ⟨hns, hro⟩ := closureStep_sub hP hview hciP hcs
        have hacc' : ∀ cj ∈ ci :: acc, cj ∈ P := by
          intro cj hcj
          rcases List.mem_cons.1 hcj with rfl | hcj
          · exact hciP
          · exact hacc cj hcj
        have hnt : ∀ m ∈ ns ++ todo'', m ∈ P.map (·.name) := by
          intro m hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hns m hm
          · exact htl m hm
        cases ro with
        | none => exact closure_sub hP hview h hacc' hnt
        | some r =>
          have hrP := hro r rfl
          dsimp only at h
          by_cases hfa : (findConst acc r.name).isSome = true
          · rw [ite_eq_left hfa] at h
            exact closure_sub hP hview h hacc' hnt
          · rw [ite_eq_right hfa] at h
            obtain ⟨tys, htys, h⟩ := OracleWhnf.ok_of_bind h
            have hty' := (ProgEnv.names_closed hP r hrP).type.exprConsts htys
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
/-- The closure of a translated term is a sub-environment of the program (port of
`L4 Core/Scope.lean:279`). -/
theorem collectDeps_sub {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P decls : List ConstantInfo} {lps : List Name} {e : Expr}
    {t : Metalean.Expr ζ lps.length 0} {view : EnvView} {cfg : ErasureConfig}
    (henv : ProgEnv P ζ E B) (hview : ViewAgrees view P) (he : TrM E B lps .nil [] e t)
    (h : collectDeps view cfg e = .ok decls) : SubEnv decls P := by
  unfold collectDeps at h
  obtain ⟨cs, hcs, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨⟨ds, cases⟩, hcl, h⟩ := OracleWhnf.ok_of_bind h
  have hds : ∀ ci ∈ ds, ci ∈ P :=
    closure_sub henv hview hcl nofun ((TrM.namesIn henv he).exprConsts hcs)
  have hdecls : decls = ds := by
    dsimp only at h
    repeat' (first | (cases h; rfl) | cases h | split at h)
  subst hdecls
  exact fun ci hci => findDecl_of_view hview (hds ci hci)

end EraseProof
