import EraseProof.Core.CollectSpec
import EraseProof.Core.State
import EraseProof.Statements

/-!
# The fragment test accepts the fragment

`collectDeps_ok_of`: on a program related to a Metalean environment and read through a view that
agrees with it, `Erasure.collectDeps` succeeds on a translated term whose read closure lies inside
the first-phase fragment: a sub-environment `decls` of the program that holds what the traversal
reads (`ReadClosed`), whose declarations are in the fragment (`PhaseIDecl`), whose read expressions
are plain (`PlainExpr`) and mention no recursor (`RecFree`), without name collisions, within the
fuel. The closure the code computes stays inside `decls`: every name it reads is a declaration of
`decls` that is not a recursor, every check `closureStep` makes holds there, and the fuel exceeds
the number of declarations of `decls`; the checks after the closure hold on any sub-list of `decls`.
Reference: none (DV-26).
-/

open Lean Erasure

namespace EraseProof

namespace CollectOk

open NonRec Extend CasesShape CollectSub CollectSpec

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-! ## Kinds of the names a declaration reads -/

/-- The block members of a declaration that is not a recursor, the constructors of an inductive and
the inductive of a constructor are declarations of `P` that are not recursors. -/
structure KindsClosed (P : List ConstantInfo) (ci : ConstantInfo) : Prop where
  all : (∀ R, ci ≠ .recInfo R) → ∀ n ∈ ci.all, Covered P n
  ctors : ∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, Covered P n
  induct : ∀ cv, ci = .ctorInfo cv → Covered P cv.induct

/-- `KindsClosed` is monotone in the program. -/
theorem KindsClosed.mono {P P' : List ConstantInfo} (hs : ∀ x ∈ P, x ∈ P') {ci : ConstantInfo}
    (h : KindsClosed P ci) : KindsClosed P' ci :=
  ⟨fun hr n hn => (h.all hr n hn).mono hs, fun iv hiv n hn => (h.ctors iv hiv n hn).mono hs,
    fun cv hcv => (h.induct cv hcv).mono hs⟩

/-- Every declaration of a program reads block members, constructors and inductives that are no
recursors: definitions, theorems and opaques are their own block, and an inductive block's members,
constructors and inductives are its inductive types and constructors. -/
theorem ProgEnv.kinds_closed (h : ProgEnv P ζ E B) : ∀ ci ∈ P, KindsClosed P ci := by
  induction h with
  | nil => intro ci hci; cases hci
  | «axiom» _ _ _ _ _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨fun _ n hn => ?_, nofun, nofun⟩
      simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn; exact ⟨_, List.mem_cons_self, rfl, nofun⟩
    · exact (ih ci hci).mono sub_cons
  | defn _ _ _ _ hall _ _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨fun _ n hn => ?_, nofun, nofun⟩
      simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn; exact ⟨_, List.mem_cons_self, rfl, nofun⟩
    · exact (ih ci hci).mono sub_cons
  | thm _ _ _ hall _ _ _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨fun _ n hn => ?_, nofun, nofun⟩
      simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn; exact ⟨_, List.mem_cons_self, rfl, nofun⟩
    · exact (ih ci hci).mono sub_cons
  | «opaque» _ _ _ _ hall _ _ _ ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨fun _ n hn => ?_, nofun, nofun⟩
      simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn; exact ⟨_, List.mem_cons_self, rfl, nofun⟩
    · exact (ih ci hci).mono sub_cons
  | @induct _ P _ _ _ _ _ _ Is Cs Rs _ _ _ _ _ _ hblk _ ih =>
    intro ci hci
    have mem : ∀ x, x ∈ IndBlock.decls Is Cs Rs → x ∈ IndBlock.decls Is Cs Rs ++ P :=
      fun x hx => List.mem_append_left _ hx
    rcases List.mem_append.1 hci with hm | hci
    · rcases IndBlock.mem_decls hm with ⟨s, rfl⟩ | ⟨s, k, rfl⟩ | ⟨s, rfl⟩
      · exact ⟨fun hr => absurd rfl (hr _), nofun, nofun⟩
      · refine ⟨fun _ n hn => ?_, nofun, fun cv hcv => ?_⟩
        · simp only [ConstantInfo.all, List.mem_singleton] at hn
          subst hn; exact ⟨_, hci, rfl, nofun⟩
        · cases hcv
          rw [(hblk.ctor s k).2.2.1]
          exact ⟨_, mem _ (block_mem.2.2 s), rfl, nofun⟩
      · refine ⟨fun _ n hn => ?_, fun iv hiv n hn => ?_, nofun⟩
        · simp only [ConstantInfo.all, (hblk.ind s).2.2.1, List.mem_ofFn] at hn
          obtain ⟨t, rfl⟩ := hn
          exact ⟨_, mem _ (block_mem.2.2 t), rfl, nofun⟩
        · cases hiv
          rw [(hblk.ind s).2.2.2.2.2.1, List.mem_ofFn] at hn
          obtain ⟨c, rfl⟩ := hn
          exact ⟨_, mem _ (block_mem.2.1 s c), rfl, nofun⟩
    · exact (ih ci hci).mono sub_append
  | quot _ _ _ _ _ _ _ ih =>
    intro ci hci
    rcases List.mem_append.1 hci with hm | hci
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
      refine ⟨fun _ n hn => ?_, nofun, nofun⟩
      simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn; exact ⟨_, hci, rfl, nofun⟩
    · exact (ih ci hci).mono sub_append

/-! ## Expressions -/

/-- `ConstsIn` of two predicates is `ConstsIn` of their conjunction. -/
theorem ConstsIn_and {p q : Name → Prop} :
    ∀ {e : Expr}, ConstsIn p e → ConstsIn q e → ConstsIn (fun c => p c ∧ q c) e
  | .const _ _, h, h' => ⟨h, h'⟩
  | .app f a, h, h' => ⟨ConstsIn_and (e := f) h.1 h'.1, ConstsIn_and (e := a) h.2 h'.2⟩
  | .lam _ t b _, h, h' | .forallE _ t b _, h, h' =>
    ⟨ConstsIn_and (e := t) h.1 h'.1, ConstsIn_and (e := b) h.2 h'.2⟩
  | .letE _ t v b _, h, h' =>
    ⟨ConstsIn_and (e := t) h.1 h'.1, ConstsIn_and (e := v) h.2.1 h'.2.1,
      ConstsIn_and (e := b) h.2.2 h'.2.2⟩
  | .mdata _ e, h, h' => ConstsIn_and (e := e) h h'
  | .proj _ _ e, h, h' => ⟨⟨h.1, h'.1⟩, ConstsIn_and (e := e) h.2 h'.2⟩
  | .bvar _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial

/-- A level without metavariables passes the level test of `exprConsts`. -/
theorem hasMVar'_of_plain : ∀ {u : Level}, LevelPlain u = true → u.hasMVar' = false
  | .zero, _ | .param _, _ => rfl
  | .succ u, h => hasMVar'_of_plain (u := u) h
  | .max a b, h | .imax a b, h => by
    simp only [LevelPlain, Bool.and_eq_true] at h
    simp only [Level.hasMVar', hasMVar'_of_plain h.1, hasMVar'_of_plain h.2, Bool.or_self]
  | .mvar _, h => nomatch h

/-- `exprConsts` succeeds on a plain expression. -/
theorem exprConsts_of_plain {cfg : ErasureConfig} :
    ∀ {e : Expr}, PlainExpr cfg e → ∃ cs, exprConsts cfg e = .ok cs
  | .bvar _, _ => ⟨[], rfl⟩
  | .fvar _, h | .mvar _, h => nomatch h
  | .sort u, h => ⟨[], by rw [exprConsts, hasMVar'_of_plain (u := u) h]; rfl⟩
  | .const c us, h => by
    obtain ⟨hus, hm⟩ := h
    have hany : us.any (·.hasMVar') = false := by
      rw [List.any_eq_false]
      intro u hu
      simp [hasMVar'_of_plain (hus u hu)]
    unfold exprConsts
    rw [hany]
    cases hn : cfg.nat with
    | peano => exact ⟨[c], rfl⟩
    | machine =>
      refine ⟨[c], ?_⟩
      have : ([``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc, ``Nat.casesOn,
          ``Int.casesOn].contains c) = false := by
        simpa using hm hn
      dsimp only
      rw [this]
      rfl
  | .app f a, h => by
    obtain ⟨xs, hf⟩ := exprConsts_of_plain (e := f) h.1
    obtain ⟨ys, ha⟩ := exprConsts_of_plain (e := a) h.2
    exact ⟨xs ++ ys, by rw [exprConsts, hf, ha]; rfl⟩
  | .lam _ t b _, h => by
    obtain ⟨xs, ht⟩ := exprConsts_of_plain (e := t) h.1
    obtain ⟨ys, hb⟩ := exprConsts_of_plain (e := b) h.2
    exact ⟨xs ++ ys, by rw [exprConsts, ht, hb]; rfl⟩
  | .forallE _ t b _, h => by
    obtain ⟨xs, ht⟩ := exprConsts_of_plain (e := t) h.1
    obtain ⟨ys, hb⟩ := exprConsts_of_plain (e := b) h.2
    exact ⟨xs ++ ys, by rw [exprConsts, ht, hb]; rfl⟩
  | .letE _ t v b _, h => by
    obtain ⟨xs, ht⟩ := exprConsts_of_plain (e := t) h.1
    obtain ⟨ys, hv⟩ := exprConsts_of_plain (e := v) h.2.1
    obtain ⟨zs, hb⟩ := exprConsts_of_plain (e := b) h.2.2
    exact ⟨xs ++ ys ++ zs, by rw [exprConsts, ht, hv, hb]; rfl⟩
  | .lit (.natVal _), h => ⟨[``Nat], by
    rw [exprConsts]
    rw [show cfg.nat = .peano from h]
    rfl⟩
  | .lit (.strVal _), h => nomatch h
  | .mdata _ e, h => by
    obtain ⟨xs, he⟩ := exprConsts_of_plain (e := e) h
    exact ⟨xs, by rw [exprConsts]; exact he⟩
  | .proj S _ e, h => by
    obtain ⟨xs, he⟩ := exprConsts_of_plain (e := e) h
    exact ⟨S :: xs, by rw [exprConsts, he]; rfl⟩

/-- A successful first computation of a bind passes its value on. -/
theorem bind_ok_eq {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} (h : x = .ok a) :
    (x >>= f) = f a := by
  rw [h]; rfl

/-- The recognizer finds the recursor as a constant of the `casesOn`'s value. -/
theorem casesInfo?_recConst {l : List ConstantInfo} {n : Name} {c : CasesInfo}
    (h : casesInfo? l n = some c) : ∃ d R, findConst l n = some (.defnInfo d) ∧
      findConst l (mkRecName (c.indName)) = some (.recInfo R) ∧
      ∀ p : Name → Prop, ConstsIn p d.value → p R.name := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body alts before hj hb ha hbe =>
        split at h
        next hok =>
          cases h
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
            List.mem_range] at hok
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hhd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
          refine ⟨d, R, hd, hR, fun p hv => ?_⟩
          have hbody := ConstsIn_peelLams hb hv
          rw [← spine_mkAppN body] at hbody
          have hhd' := (ConstsIn_mkAppN.1 hbody).1
          rw [isConstAt_iff hhd] at hhd'
          exact hhd'
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- The sort test answers `false` only on an arity whose sort is neither zero nor never zero. -/
theorem sortDecided_false {iv : InductiveVal} (h : sortDecided iv = .ok false) :
    ∃ n u, arityShape iv.type = some (n, u) ∧ u ≠ .zero ∧ u.isNeverZero = false := by
  unfold sortDecided at h
  split at h
  · cases h
  · rename_i n u hz hs
    refine ⟨n, u, hs, hz, ?_⟩
    split at h
    · cases h
    · rename_i hnz
      exact Bool.eq_false_iff.2 hnz
  · cases h

/-- The sort test accepts an arity whose sort is zero, never zero, or may be not zero. -/
theorem sortDecided_ok_of {iv : InductiveVal} {n : Nat} {u : Level}
    (hs : arityShape iv.type = some (n, u))
    (hu : u = .zero ∨ u.isNeverZero = true ∨ mayBeNonZero iv.levelParams u = true) :
    ∃ b, sortDecided iv = .ok b := by
  cases u with
  | zero => exact ⟨true, by unfold sortDecided; rw [hs]; rfl⟩
  | _ =>
    unfold sortDecided
    rw [hs]
    dsimp only
    split
    · exact ⟨true, rfl⟩
    · rename_i hnz
      split
      · exact ⟨false, rfl⟩
      · rename_i hm
        rcases hu with h | h | h
        · cases h
        · exact absurd h hnz
        · exact absurd h hm

/-- A `for` loop whose body yields on every element succeeds. -/
theorem forIn_ok_of {ε α : Type} {f : α → Unit → Except ε (ForInStep Unit)} :
    ∀ {l : List α}, (∀ a ∈ l, f a () = .ok (.yield ())) → forIn l () f = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons, h a List.mem_cons_self]
    exact forIn_ok_of (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)

/-! ## The premises, on the declarations of `decls` -/

/-- The premises of `collectDeps_ok_of`, with the facts of the program they are used with. -/
structure Frag (P : List ConstantInfo) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (e : Expr) : Prop where
  closed : ∀ ci ∈ P, NamesClosed P ci
  kinds : ∀ ci ∈ P, KindsClosed P ci
  hview : ViewAgrees view P
  sub : ∀ ci ∈ decls, ci ∈ P
  rc : ReadClosed decls e
  phase : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci
  plainE : PlainExpr cfg e
  plain : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → PlainExpr cfg x
  recFreeE : RecFree decls e
  recFree : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecFree decls x

namespace Frag

variable {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo} {e : Expr}
  (hf : Frag P view cfg decls e)
include hf

/-- A declaration of `decls` is the first of its name. -/
theorem fd {y : ConstantInfo} (hy : y ∈ decls) : findDecl decls y.name = some y := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 (List.mem_map_of_mem hy))
  obtain ⟨hz1, hz2⟩ := findDecl_eq_some hz
  rw [hz, eq_of_name hf.hview (hf.sub z hz1) (hf.sub y hy) hz2]

/-- The view returns the declarations of `decls`. -/
theorem vw {y : ConstantInfo} (hy : y ∈ decls) : view.find? y.name = some y :=
  hf.hview y (hf.sub y hy)

/-- What `ReadClosed` asks of each declaration. -/
theorem rcd {ci : ConstantInfo} (hci : ci ∈ decls) :
    let inD := fun c => (findDecl decls c).isSome = true
    (∀ x, ReadExpr decls ci x → ConstsIn inD x ∧ (HasNatLit x → inD ``Nat)) ∧
    (∀ n ∈ ci.all, inD n) ∧ (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, inD n) ∧
    (∀ cv, ci = .ctorInfo cv → inD cv.induct) ∧
    (∀ iv, EvalEnv.casesOn? ⟨decls, fun _ => false⟩ ci.name = some iv →
      inD iv.name ∧ inD (mkRecName iv.name)) ∧
    (∀ iv, ci = .inductInfo iv → iv.ctors.length = 1 → inD (mkRecName iv.name)) :=
  hf.rc.2.2 ci hci

omit hf in
/-- A name of `decls` that is no recursor of `decls` is covered. -/
theorem covered {n : Name} (hin : (findDecl decls n).isSome = true)
    (hnr : IsRecursorIn decls n = false) : Covered decls n := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  refine ⟨y, hy1, hy2, fun R hR => ?_⟩
  subst hR
  unfold IsRecursorIn at hnr
  rw [hy] at hnr
  cases hnr

/-- A name of `decls` that the program covers is covered by `decls`. -/
theorem covered_of_P {n : Name} (hin : (findDecl decls n).isSome = true) (hP : Covered P n) :
    Covered decls n := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  obtain ⟨z, hz, hzn, hzr⟩ := hP
  have := eq_of_name hf.hview (hf.sub y hy1) hz (hy2.trans hzn.symm)
  subst this
  exact ⟨y, hy1, hy2, hzr⟩

/-- `Nat`, when in `decls`, is no recursor of `decls`: the recursors of `decls` are named
`T.rec`. -/
theorem nat_covered (hin : (findDecl decls ``Nat).isSome = true) : Covered decls ``Nat := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  refine ⟨y, hy1, hy2, fun R hR => ?_⟩
  subst hR
  have hph := hf.phase _ hy1
  have hn : ∃ T, R.name = mkRecName T := by
    rcases hph with ⟨T, -, hT, -⟩ | ⟨T, -, hT, -⟩ <;> exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hn
  have h2 : (ConstantInfo.recInfo R).name = R.name := rfl
  rw [h2, hT] at hy2
  unfold mkRecName at hy2
  injection hy2 with _ h
  exact absurd h (by decide)

/-- The names `exprConsts` lists on an expression whose constants are in `decls` and no recursors
of it are covered. -/
theorem names_of {x : Expr} (hc : ConstsIn (fun c => (findDecl decls c).isSome = true) x)
    (hnl : HasNatLit x = true → (findDecl decls ``Nat).isSome = true) (hr : RecFree decls x)
    (hpl : PlainExpr cfg x) : ∃ cs, exprConsts cfg x = .ok cs ∧ ∀ n ∈ cs, Covered decls n := by
  obtain ⟨cs, hcs⟩ := exprConsts_of_plain hpl
  exact ⟨cs, hcs, exprConsts_mem hcs
    (ConstsIn_mono (fun c hc => covered hc.1 hc.2) (ConstsIn_and hc hr))
    (fun h => hf.nat_covered (hnl h))⟩

/-- The names of a read expression are covered. -/
theorem read_names {ci : ConstantInfo} (hci : ci ∈ decls) {x : Expr} (hx : ReadExpr decls ci x) :
    ∃ cs, exprConsts cfg x = .ok cs ∧ ∀ n ∈ cs, Covered decls n :=
  hf.names_of ((hf.rcd hci).1 x hx).1 ((hf.rcd hci).1 x hx).2 (hf.recFree ci hci x hx)
    (hf.plain ci hci x hx)

/-- The names of the term are covered. -/
theorem term_names : ∃ cs, exprConsts cfg e = .ok cs ∧ ∀ n ∈ cs, Covered decls n :=
  hf.names_of hf.rc.1 hf.rc.2.1 hf.recFreeE hf.plainE

/-- The constructors and block members of an inductive of `decls` are names of `decls`. -/
theorem inds : ∀ iv, .inductInfo iv ∈ decls →
    (∀ n ∈ iv.ctors, n ∈ decls.map (·.name)) ∧ ∀ n ∈ iv.all, n ∈ decls.map (·.name) :=
  fun iv hiv => ⟨fun n hn => findDecl_isSome_iff.1 ((hf.rcd hiv).2.2.1 iv rfl n hn),
    fun n hn => findDecl_isSome_iff.1 ((hf.rcd hiv).2.1 n hn)⟩

/-- A `casesOn` that the view recognizes is recognized on `decls`, with its inductive and its
recursor in `decls`: otherwise its value is read, and the recursor at its head is a recursor of
`decls` (`ReadClosed`) that it mentions, against `RecFree`. -/
theorem recog_dec {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} (hd : .defnInfo d ∈ decls)
    (hrec : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors)) :
    (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isSome ∧ .inductInfo I ∈ decls ∧
      .recInfo R ∈ decls ∧ d.name = .str I.name "casesOn" ∧
      ctors = I.ctors.flatMap (viewFind view) := by
  obtain ⟨T, hT, hI, hR, hct, hc⟩ := recognize_iff.1 hrec
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  have hl := recog_view (hf.vw hd) hI hR
  have hcs : (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isSome := by
    by_contra hnone
    have hx : ReadExpr decls (.defnInfo d) d.value :=
      .inr (.inl ⟨d, rfl, rfl, by simpa using hnone⟩)
    have hcv := ConstsIn_and ((hf.rcd hd).1 _ hx).1 (hf.recFree _ hd _ hx)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hc
    obtain ⟨d', R', hd', hR', hcon⟩ := casesInfo?_recConst hc
    obtain ⟨hd'1, hd'2⟩ := findDecl_eq_some (l := recogList view (.defnInfo d) I R) hd'
    have hdd : ConstantInfo.defnInfo d' = .defnInfo d := by
      have h1 := hl _ hd'1
      rw [hd'2, hf.vw hd] at h1
      cases h1; rfl
    cases hdd
    obtain ⟨hin, hnr⟩ := hcon _ hcv
    obtain ⟨hR'1, hR'2⟩ := findDecl_eq_some (l := recogList view (.defnInfo d) I R) hR'
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
    obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
    have h1 := hf.vw hy1
    have h2 : view.find? R'.name = some (.recInfo R') := hl _ hR'1
    rw [hy2, h2] at h1
    cases h1
    unfold IsRecursorIn at hnr
    rw [hy] at hnr
    cases hnr
  obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.1 hcs
  unfold EvalEnv.casesOn? at hiv
  split at hiv
  next c hc' =>
    obtain ⟨T', I', hn, hind, hI', -, R', hR'⟩ := casesInfo?_name hc'
    have hTT : T' = T := by
      have h2 : Name.str T "casesOn" = Name.str T' "casesOn" := hT.symm.trans hn
      injection h2 with h; exact h.symm
    subst hTT
    obtain ⟨hI'1, hI'2⟩ := findDecl_eq_some (l := decls) hI'
    obtain ⟨hR'1, hR'2⟩ := findDecl_eq_some (l := decls) hR'
    have e1 := hf.vw hI'1
    rw [hI'2, hIf] at e1
    cases e1
    have e2 := hf.vw hR'1
    rw [hR'2, hRf] at e2
    cases e2
    exact ⟨hcs, hI'1, hR'1, by rw [show d.name = _ from hT, ← hIn]; rfl, hct⟩
  next => cases hiv

/-- A `casesOn` recognized on `decls` is recognized by the view. -/
theorem recog_of_dec {d : DefinitionVal} (hd : .defnInfo d ∈ decls)
    (hcs : (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isSome) :
    ∃ I R ctors, recognizeCasesOn view (.defnInfo d) = some (I, R, ctors) := by
  obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.1 hcs
  obtain ⟨-, R, ctors, h⟩ := recog_of_ds_of hf.closed hf.hview hf.sub hf.inds hd hiv
  exact ⟨iv, R, ctors, h⟩

/-- `declExclusion` accepts a declaration of `decls` that is not a recursor. -/
theorem dex {ci : ConstantInfo} (hci : ci ∈ decls) (hnr : ∀ R, ci ≠ .recInfo R) :
    declExclusion view cfg ci = .ok () := by
  have hph := hf.phase ci hci
  cases ci with
  | recInfo r => exact absurd rfl (hnr r)
  | thmInfo _ | quotInfo _ => rfl
  | defnInfo d =>
    obtain ⟨h1, h2, h3⟩ := hph
    simp [declExclusion, h1, h2, h3]; rfl
  | opaqueInfo o =>
    obtain ⟨h1, h2, h3⟩ := hph
    simp [declExclusion, h1, h2, h3]; rfl
  | axiomInfo a =>
    obtain ⟨h1, h3⟩ := hph
    simp [declExclusion, h1, h3]; rfl
  | inductInfo iv =>
    obtain ⟨h1, h2, ⟨n, u, hs, hu⟩, -⟩ := hph
    obtain ⟨b, hb⟩ := sortDecided_ok_of hs (by
      rcases hu with h | h | ⟨h, -⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h))
    simp [declExclusion, h1, h2, hb]
    rfl
  | ctorInfo cv =>
    obtain ⟨h1, h2⟩ := hph
    have h3 : (cfg.1 == .preferAxiom && view.isExtern cv.name) = false := by
      cases hx : cfg.1 with
      | preferAxiom => simp [h2 hx]
      | _ => rfl
    simp [declExclusion, h1, h3]; rfl

/-- One step of the closure succeeds on a declaration of `decls` that is not a recursor, reads
covered names, and adds a companion recursor of `decls` whose type's names are covered and, for a
definition, only for a `casesOn` recognized on `decls`. -/
theorem step {ci : ConstantInfo} (hci : ci ∈ decls) (hnr : ∀ R, ci ≠ .recInfo R) :
    ∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, Covered decls n) ∧
      (∀ r, ro = some r → r ∈ decls ∧ r.name ≠ ci.name ∧
        ∃ tys, exprConsts cfg r.type = .ok tys ∧ ∀ n ∈ tys, Covered decls n) ∧
      (∀ r d, ro = some r → ci = .defnInfo d →
        (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ ci.name).isSome) := by
  have hdex := hf.dex hci hnr
  obtain ⟨ty, hty, htyc⟩ := hf.read_names hci (x := ci.type) (.inl rfl)
  have hall : ∀ n ∈ ci.all, Covered decls n := fun n hn =>
    hf.covered_of_P ((hf.rcd hci).2.1 n hn) ((hf.kinds _ (hf.sub _ hci)).all hnr n hn)
  -- a companion of `decls` that is a recursor
  have comp : ∀ R, .recInfo R ∈ decls → (ConstantInfo.recInfo R).name ≠ ci.name ∧
      ∃ tys, exprConsts cfg R.type = .ok tys ∧ ∀ n ∈ tys, Covered decls n := by
    intro R hR
    refine ⟨fun he => hnr R ?_, hf.read_names hR (.inl rfl)⟩
    have := hf.fd hR
    rw [he, hf.fd hci] at this
    cases this; rfl
  unfold closureStep
  rw [bind_ok_eq hdex, bind_ok_eq hty]
  cases ci with
  | recInfo r => exact absurd rfl (hnr r)
  | defnInfo d =>
    cases hrec : recognizeCasesOn view (.defnInfo d) with
    | some x =>
      obtain ⟨I, R, ctors⟩ := x
      obtain ⟨hcs, hI, hR, hdn, hct⟩ := hf.recog_dec hci hrec
      refine ⟨ty ++ I.name :: d.all, some (.recInfo R), ?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [bind_ok_eq (forIn_ok_of fun c hc => ?_)]
        · rfl
        rw [hct] at hc
        obtain ⟨cn, hcn, hc⟩ := List.mem_flatMap.1 hc
        obtain ⟨hcv, hcn'⟩ := viewFind_mem hc
        cases c with
        | ctorInfo cv =>
          have hph := hf.phase _ hI
          obtain ⟨-, -, -, hidx⟩ := hph
          have hin := (hf.rcd hI).2.2.1 I rfl cn hcn
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
          obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
          have e1 := hf.vw hy1
          rw [hy2, ← hcn', hcv] at e1
          cases e1
          have hk := hidx (by rw [← hdn]; exact hcs) cn hcn cv (hcn' ▸ hy)
          simp [hk]; rfl
        | _ => rfl
      · intro n hn
        simp only [List.mem_append, List.mem_cons] at hn
        rcases hn with hn | rfl | hn
        · exact htyc n hn
        · exact ⟨_, hI, rfl, nofun⟩
        · exact hall n hn
      · intro r hr
        cases hr
        exact ⟨hR, comp R hR⟩
      · intro _ _ _ _
        exact hcs
    | none =>
      have hnone : (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isNone := by
        cases h : EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name with
        | none => rfl
        | some iv =>
          obtain ⟨I, R, ctors, h'⟩ := hf.recog_of_dec hci (by rw [h]; rfl)
          rw [hrec] at h'; cases h'
      obtain ⟨vs, hvs, hvsc⟩ := hf.read_names hci (x := d.value) (.inr (.inl ⟨d, rfl, rfl, hnone⟩))
      refine ⟨ty ++ vs ++ d.all, none, ?_, ?_, nofun, nofun⟩
      · dsimp only
        rw [bind_ok_eq hvs]
        rfl
      · intro n hn
        simp only [List.mem_append] at hn
        rcases hn with (hn | hn) | hn
        · exact htyc n hn
        · exact hvsc n hn
        · exact hall n hn
  | thmInfo t =>
    refine ⟨ty ++ t.all, none, rfl, fun n hn => ?_, nofun, nofun⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact htyc n hn
    · exact hall n hn
  | opaqueInfo o =>
    obtain ⟨vs, hvs, hvsc⟩ := hf.read_names hci (x := o.value) (.inr (.inr ⟨o, rfl, rfl⟩))
    refine ⟨ty ++ vs ++ o.all, none, ?_, fun n hn => ?_, nofun, nofun⟩
    · dsimp only
      rw [bind_ok_eq hvs]
      rfl
    · simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact htyc n hn
      · exact hvsc n hn
      · exact hall n hn
  | inductInfo iv =>
    refine ⟨ty ++ iv.all ++ iv.ctors, _, rfl, fun n hn => ?_, fun r hr => ?_, nofun⟩
    · simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact htyc n hn
      · exact hall n hn
      · exact hf.covered_of_P ((hf.rcd hci).2.2.1 iv rfl n hn)
          ((hf.kinds _ (hf.sub _ hci)).ctors iv rfl n hn)
    · split at hr
      · rename_i c r' R hc hv
        cases hr
        obtain ⟨hvf, hvn⟩ := viewFind_eq hv
        have hin := (hf.rcd hci).2.2.2.2.2 iv rfl (by simp [hc])
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
        obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
        have e1 := hf.vw hy1
        rw [hy2, hvf] at e1
        cases e1
        exact ⟨hy1, comp R hy1⟩
      · cases hr
  | ctorInfo cv =>
    refine ⟨ty ++ [cv.induct], none, rfl, fun n hn => ?_, nofun, nofun⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact htyc n hn
    · rw [List.mem_singleton.1 hn]
      exact hf.covered_of_P ((hf.rcd hci).2.2.2.1 cv rfl)
        ((hf.kinds _ (hf.sub _ hci)).induct cv rfl)
  | axiomInfo a => exact ⟨ty, none, rfl, htyc, nofun, nofun⟩
  | quotInfo q => exact ⟨ty, none, rfl, htyc, nofun, nofun⟩

/-- `dropKnown` succeeds on covered names: it drops the names the accumulator has (none of them a
recursor) and stops at one it does not have. -/
theorem dropKnown_ok_of {acc : List ConstantInfo} (hacc : ∀ y ∈ acc, y ∈ decls) :
    ∀ {todo : List Name}, (∀ n ∈ todo, Covered decls n) →
    ∃ rest, dropKnown acc todo = .ok rest ∧ (∀ n ∈ rest, n ∈ todo) ∧
      ∀ n rest', rest = n :: rest' → findConst acc n = none
  | [], _ => ⟨[], rfl, nofun, nofun⟩
  | n :: todo, h => by
    cases hfc : findConst acc n with
    | none =>
      exact ⟨n :: todo, by rw [dropKnown, hfc]; rfl, fun _ h => h,
        fun m rest' he => by cases he; exact hfc⟩
    | some y =>
      obtain ⟨hy1, hy2⟩ := findDecl_eq_some (l := acc) hfc
      obtain ⟨z, hz, hzn, hzr⟩ := h n List.mem_cons_self
      have hyz : y = z := by
        have := hf.fd (hacc y hy1)
        rw [hy2, ← hzn, hf.fd hz] at this
        cases this; rfl
      subst hyz
      obtain ⟨rest, hrest, hsub, hnone⟩ := dropKnown_ok_of hacc (todo := todo)
        fun m hm => h m (List.mem_cons_of_mem _ hm)
      refine ⟨rest, ?_, fun m hm => List.mem_cons_of_mem _ (hsub m hm), hnone⟩
      rw [dropKnown, hfc]
      cases y with
      | recInfo R => exact absurd rfl (hzr R)
      | _ => exact hrest

omit hf in
/-- A list of declarations of `decls` with distinct names, at least as long as `decls`, has every
name of `decls`. -/
theorem full {acc : List ConstantInfo} (hacc : ∀ y ∈ acc, y ∈ decls)
    (hnd : (acc.map (·.name)).Nodup) (hlen : decls.length ≤ acc.length) {n : Name}
    (hn : n ∈ decls.map (·.name)) : n ∈ acc.map (·.name) := by
  by_contra hna
  have hsub : acc.map (·.name) ⊆ (decls.map (·.name)).erase n := by
    intro m hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    exact (List.mem_erase_of_ne fun he => hna (by rw [← he]; exact List.mem_map_of_mem hy)).2
      (List.mem_map_of_mem (hacc y hy))
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem hn, List.length_map, List.length_map] at this
  have hpos : 0 < decls.length := List.length_pos_of_mem (List.mem_map.1 hn).choose_spec.1
  omega

/-- The closure succeeds from an accumulator of `decls` and a work list of covered names, with fuel
for the declarations of `decls` the accumulator lacks; its result is a sub-list of `decls` with
distinct names, and its recognized `casesOn` are recognized on `decls`. -/
theorem closure_ok_of : ∀ (f : Nat) {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name}, (∀ y ∈ acc, y ∈ decls) → (acc.map (·.name)).Nodup →
    (∀ n ∈ todo, Covered decls n) →
    (∀ m ∈ cases, (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ m).isSome) →
    decls.length ≤ f + acc.length →
    ∃ res, closure view cfg f todo acc cases = .ok res ∧ (∀ y ∈ res.1, y ∈ decls) ∧
      (res.1.map (·.name)).Nodup ∧
      ∀ m ∈ res.2, (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ m).isSome
  | 0, todo, acc, cases, hacc, hnd, htodo, hcases, hlen => by
    obtain ⟨rest, hrest, hsub, hnone⟩ := hf.dropKnown_ok_of hacc htodo
    cases rest with
    | nil =>
      refine ⟨(acc, cases), ?_, hacc, hnd, hcases⟩
      rw [closure, bind_ok_eq hrest]
      rfl
    | cons n rest' =>
      have hn := hnone n rest' rfl
      have hin := full hacc hnd (by simpa using hlen) (htodo n (hsub n List.mem_cons_self)).mem
      exact absurd (findDecl_isSome_iff.2 hin) (by rw [show findDecl acc n = findConst acc n from rfl, hn]; simp)
  | f + 1, todo, acc, cases, hacc, hnd, htodo, hcases, hlen => by
    obtain ⟨rest, hrest, hsub, hnone⟩ := hf.dropKnown_ok_of hacc htodo
    cases rest with
    | nil =>
      refine ⟨(acc, cases), ?_, hacc, hnd, hcases⟩
      rw [closure, bind_ok_eq hrest]
      rfl
    | cons n rest' =>
      have hnacc := hnone n rest' rfl
      obtain ⟨y, hy, hyn, hyr⟩ := htodo n (hsub n List.mem_cons_self)
      subst hyn
      have htl : ∀ m ∈ rest', Covered decls m :=
        fun m hm => htodo m (hsub m (List.mem_cons_of_mem _ hm))
      obtain ⟨ns, ro, hstep, hns, hro, hcas⟩ := hf.step hy hyr
      have hnd1 : ((y :: acc).map (·.name)).Nodup := by
        rw [List.map_cons, List.nodup_cons]
        exact ⟨not_mem_of_findDecl_none hnacc, hnd⟩
      have hacc1 : ∀ z ∈ y :: acc, z ∈ decls := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hy
        · exact hacc z hz
      have hlen1 : decls.length ≤ f + (y :: acc).length := by
        rw [List.length_cons]; omega
      have htodo1 : ∀ m ∈ ns ++ rest', Covered decls m := by
        intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hns m hm
        · exact htl m hm
      rw [closure, bind_ok_eq hrest]
      dsimp only
      rw [hf.vw hy]
      dsimp only
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [bind_ok_eq hstep]
      cases ro with
      | none =>
        exact closure_ok_of f hacc1 hnd1 htodo1 hcases hlen1
      | some r =>
        obtain ⟨hr, hrn, tys, htys, htysc⟩ := hro r rfl
        have hcases1 : ∀ m ∈ (if y matches .defnInfo _ then y.name :: cases else cases),
            (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ m).isSome := by
          intro m hm
          cases y with
          | defnInfo d =>
            rcases List.mem_cons.1 hm with rfl | hm
            · exact hcas r d rfl rfl
            · exact hcases m hm
          | _ => exact hcases m hm
        dsimp only
        by_cases hfa : (findConst acc r.name).isSome = true
        · rw [ite_eq_left hfa]
          exact closure_ok_of f hacc1 hnd1 htodo1 hcases1 hlen1
        · rw [ite_eq_right hfa, bind_ok_eq htys]
          refine closure_ok_of f ?_ ?_ ?_ hcases1 (by rw [List.length_cons]; omega)
          · intro z hz
            rcases List.mem_cons.1 hz with rfl | hz
            · exact hr
            · exact hacc1 z hz
          · rw [List.map_cons, List.nodup_cons]
            refine ⟨fun hm => ?_, hnd1⟩
            rw [List.map_cons, List.mem_cons] at hm
            rcases hm with hm | hm
            · exact hrn hm
            · exact hfa (findDecl_isSome_iff.2 hm)
          · intro m hm
            simp only [List.mem_append] at hm
            rcases hm with (hm | hm) | hm
            · exact hns m hm
            · exact htysc m hm
            · exact htl m hm

end Frag

/-! ## The checks after the closure -/

/-- No collision among declarations with distinct names and kernames. -/
theorem findCollision_none {l : List ConstantInfo} (hnd : (l.map (·.name)).Nodup)
    (hk : ∀ a ∈ l, ∀ b ∈ l, toKername a.name = toKername b.name → a.name = b.name) :
    findCollision l = none := by
  induction l with
  | nil => rfl
  | cons ci cs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [findCollision.eq_2]
    have hf : cs.find? (fun cj => toKername cj.name == toKername ci.name) = none := by
      rw [List.find?_eq_none]
      intro cj hcj hb
      have := hk cj (List.mem_cons_of_mem _ hcj) ci List.mem_cons_self (StateLemmas.kername_eq_of_beq hb)
      exact hnd.1 (this ▸ List.mem_map_of_mem hcj)
    rw [hf]
    exact ih hnd.2 fun a ha b hb => hk a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)

/-- No block collision on a sub-list of declarations whose block names are distinct. -/
theorem findBlockCollision_none {l decls : List ConstantInfo} (hs : ∀ y ∈ l, y ∈ decls)
    (hb : BlockNamesInj decls) : findBlockCollision l = none := by
  unfold findBlockCollision
  rw [List.findSome?_eq_none_iff]
  intro iv₁ hiv₁
  obtain ⟨ci₁, hci₁, he₁⟩ := List.mem_filterMap.1 hiv₁
  have hd₁ : ∃ ci ∈ decls, ci = .inductInfo iv₁ := by
    refine ⟨ci₁, hs _ hci₁, ?_⟩
    cases ci₁ <;> first | (cases he₁; rfl) | cases he₁
  dsimp only
  split
  · rename_i iv₂ hfind
    exfalso
    have hc := List.find?_some hfind
    obtain ⟨ci₂, hci₂, he₂⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hfind)
    have hd₂ : ∃ ci ∈ decls, ci = .inductInfo iv₂ := by
      refine ⟨ci₂, hs _ hci₂, ?_⟩
      cases ci₂ <;> first | (cases he₂; rfl) | cases he₂
    rw [Bool.and_eq_true] at hc
    have := (hb iv₂ iv₁ hd₂ hd₁).1 (StateLemmas.kername_eq_of_beq hc.1)
    simp [this] at hc
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro ci hci hc
  rw [Bool.and_eq_true] at hc
  have hem : EmitsConst ci = true := by
    cases ci <;> simp_all [EmitsConst]
  exact (hb iv₁ iv₁ hd₁ hd₁).2 ci (hs _ hci) hem (StateLemmas.kername_eq_of_beq hc.2)

/-- `eliminatedUndecided` answers `none` on a sub-list of `decls` whose recognized `casesOn` are
recognized on `decls`, when every inductive of `decls` is in the first-phase fragment. -/
theorem eliminatedUndecided_none_of {view : EnvView} {cfg : ErasureConfig}
    {l decls : List ConstantInfo} {cases : List Name} (hs : ∀ y ∈ l, y ∈ decls)
    (hfd : ∀ y ∈ decls, findDecl decls y.name = some y)
    (hph : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci)
    (hcases : ∀ m ∈ cases, (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ m).isSome) :
    eliminatedUndecided l cases = none := by
  unfold eliminatedUndecided
  rw [List.findSome?_eq_none_iff]
  intro ci hci
  cases ci with
  | inductInfo iv =>
    dsimp only
    cases hsd : sortDecided iv with
    | error _ => simp
    | «ok» b =>
      cases b with
      | true => simp
      | false =>
          obtain ⟨n, u, hsh, hz, hnz⟩ := sortDecided_false hsd
          obtain ⟨-, -, ⟨n', u', hsh', hu⟩, -⟩ := hph _ (hs _ hci)
          rw [hsh] at hsh'
          cases hsh'
          have hne : ¬ Eliminated decls iv := by
            rcases hu with h | h | ⟨-, h⟩
            · exact absurd h hz
            · rw [hnz] at h; cases h
            · exact h
          simp only [Bool.and_true, ite_eq_right_iff, reduceCtorEq, imp_false, Bool.or_eq_true]
          rintro (hc | hc)
          · exact hne (.inl (hcases _ (List.contains_iff_mem.1 hc)))
          · split at hc
            · rename_i c hc1
              split at hc
              · rename_i cv hcv
                obtain ⟨hcv1, hcv2⟩ := findDecl_eq_some (l := l) hcv
                have := hfd _ (hs _ hcv1)
                rw [hcv2] at this
                exact hne (.inr ⟨c, cv, hc1, this, by simpa using hc⟩)
              · cases hc
            · cases hc
  | _ => rfl

end CollectOk

open CollectSub CollectSpec CollectOk in
/-- The fragment test accepts every typed program whose read closure lies inside the first-phase
fragment: on a program related to a Metalean environment and read through a view that agrees with
it, a translated term with a sub-environment `decls` that holds what the traversal reads
(`ReadClosed`), keeps every declaration inside the fragment (`PhaseIDecl`), reads only plain
expressions (`PlainExpr`) without recursors (`RecFree`), has distinct kernames and λ□ block names
and fewer declarations than the fuel, `Erasure.collectDeps` succeeds. Its closure is a sub-list of
`decls`. Reference: none (DV-26). -/
theorem collectDeps_ok_of : collectDeps_ok_of_statement := by
  intro ζ E B P decls lps e t view cfg henv hview he _ hrm hsub hrc hph hpl hrf hki hbi hlen
  have hf : Frag P view cfg decls e :=
    ⟨ProgEnv.names_closed henv, ProgEnv.kinds_closed henv, hview,
      fun ci hci => (findDecl_eq_some (hsub ci hci)).1, hrc, hph, hpl.1, hpl.2, hrf.1, hrf.2⟩
  obtain ⟨cs, hcs, hcsc⟩ := hf.term_names
  obtain ⟨⟨decls', cases⟩, hcl, hs, hnd, hcases⟩ :=
    hf.closure_ok_of collectFuel (todo := cs) (acc := []) (cases := []) nofun List.nodup_nil hcsc
      nofun (by simpa using hlen)
  have hel : eliminatedUndecided decls' cases = none :=
    eliminatedUndecided_none_of hs (fun y hy => hf.fd hy) hph hcases
  have hcol : findCollision decls' = none := by
    refine findCollision_none hnd fun a ha b hb hk => ?_
    exact hki a.name b.name (findDecl_isSome_iff.2 (List.mem_map_of_mem (hs a ha)))
      (findDecl_isSome_iff.2 (List.mem_map_of_mem (hs b hb))) hk
  have hbc : findBlockCollision decls' = none := findBlockCollision_none hs hbi
  refine ⟨decls', ?_⟩
  unfold collectDeps
  rw [bind_ok_eq hcs, bind_ok_eq hcl]
  simp only [hel, hrm, hcol, hbc]
  rfl

end EraseProof
