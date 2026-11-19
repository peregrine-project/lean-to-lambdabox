import EraseProof.Core.CollectSpec
import EraseProof.Relation.Lookup

/-!
# The fragment test accepts the fragment

`collectDeps_ok_of`: on a program con-leche accepts, read through a view that agrees with it,
`Erasure.collectDeps` succeeds on a term whose read closure lies inside the first-phase fragment:
a sub-environment `decls` of the program that holds what the traversal reads (`ReadClosed`), whose
declarations are in the fragment (`PhaseIDecl`), whose read expressions are plain (`PlainExpr`) and
name recursors only in the shape the fragment admits (`RecShaped`), without name collisions,
within the fuel. The closure the code computes stays inside `decls`: every name it reads is a
declaration of `decls` that is not a recursor or is a recursor in that shape (`Cov`), which
`declExclusion` accepts (`dex_rec`), every check `closureStep` makes holds there, and the fuel
exceeds the number of declarations of `decls`; the checks after the closure hold on any sub-list
of `decls`. The program gives the kinds of the names an inductive or a constructor reads
(`blockOf?`, `declOf?`) and the block of a recursor (`recs_mention`). Port of
`ML-V Core/CollectOk.lean`. Reference: none (DV-26).
-/

open Lean Erasure

namespace EraseProof

namespace CollectOk

open CollectSub CollectSpec Decls

/-! ## Kinds of the names a declaration reads -/

/-- `n` names a declaration of `decls` that is not a recursor, or a recursor in the shape that the
fragment admits over `decls` (`RecInFragment`). Port of `ML-V Core/CollectOk.lean:45`. -/
def Cov (cfg : ErasureConfig) (decls : List ConstantInfo) (n : Name) : Prop :=
  ∃ y ∈ decls, y.name = n ∧ ∀ R, y = .recInfo R → RecInFragment cfg decls R

/-- A name `Cov` by a list is a name of the list. Port of `ML-V Core/CollectOk.lean:49`. -/
theorem Cov.mem {cfg : ErasureConfig} {l : List ConstantInfo} {n : Name} (h : Cov cfg l n) :
    n ∈ l.map (·.name) :=
  let ⟨_, hy, hn, _⟩ := h
  hn ▸ List.mem_map_of_mem hy

/-- The members of an inductive of a program con-leche accepts are inductives of the program, and
its constructors are constructors of the program: `blockOf?` reads them so at the block's head.
Replaces `ML-V Core/CollectOk.lean:70 ProgEnv.kinds_closed` for inductives. -/
theorem ind_kinds {P : List ConstantInfo} {env : ConLeche.Env} (hP : ConLecheAccepts P env)
    {iv : InductiveVal} (hiv : .inductInfo iv ∈ P) :
    (∀ n ∈ iv.all, ∃ t, findDecl P n = some (.inductInfo t)) ∧
      ∀ n ∈ iv.ctors, ∃ c, findDecl P n = some (.ctorInfo c) := by
  obtain ⟨ds, hds, -⟩ := id hP
  obtain ⟨Hn, H, hH, hhead, hall, hmem⟩ := hP.head hiv
  obtain ⟨block, p, hblk, -, -⟩ := hP.block hH hhead (hP.ind_safe (findDecl_mem hH).1)
  obtain ⟨block', -, -, hspec⟩ := blockOf?_spec hblk
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨t, ht, -⟩ := hspec n (hall ▸ hn)
    exact ⟨t, ht⟩
  · obtain ⟨t, ht, -, hc⟩ := hspec iv.name hmem
    have ht' : findDecl P iv.name = some (.inductInfo t) := ht
    have hself : findDecl P iv.name = some (.inductInfo iv) := findDecl_self (DeclsOf?.nodup hds) hiv
    rw [hself] at ht'
    cases ht'
    obtain ⟨c, hc', -⟩ := hc n hn
    exact ⟨c, hc'⟩

/-- The inductive of a constructor of a program con-leche accepts is an inductive of the program
(`declOf?`). Replaces `ML-V Core/CollectOk.lean:70 ProgEnv.kinds_closed` for constructors. -/
theorem ctor_kind {P : List ConstantInfo} {env : ConLeche.Env} (hP : ConLecheAccepts P env)
    {cv : ConstructorVal} (hcv : .ctorInfo cv ∈ P) :
    ∃ t, findDecl P cv.induct = some (.inductInfo t) := by
  obtain ⟨ds, hds, -⟩ := id hP
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hcv
  simp only [declOf?] at hL
  split at hL
  · rename_i t ht; exact ⟨t, ht⟩
  · cases hL

/-! ## Expressions -/

/-- `ConstsIn` of two predicates is `ConstsIn` of their conjunction. Port of
`ML-V Core/CollectOk.lean:135`. -/
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

/-- A level without metavariables passes the level test of `exprConsts`. Port of
`ML-V Core/CollectOk.lean:149`. -/
theorem hasMVar'_of_plain : ∀ {u : Level}, LevelPlain u = true → u.hasMVar' = false
  | .zero, _ | .param _, _ => rfl
  | .succ u, h => hasMVar'_of_plain (u := u) h
  | .max a b, h | .imax a b, h => by
    simp only [LevelPlain, Bool.and_eq_true] at h
    simp only [Level.hasMVar', hasMVar'_of_plain h.1, hasMVar'_of_plain h.2, Bool.or_self]
  | .mvar _, h => nomatch h

/-- `exprConsts` succeeds on a plain expression. Port of `ML-V Core/CollectOk.lean:158`. -/
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

/-- A successful first computation of a bind passes its value on. Port of
`ML-V Core/CollectOk.lean:211`. -/
theorem bind_ok_eq {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} (h : x = .ok a) :
    (x >>= f) = f a := by
  rw [h]; rfl

/-! ## The checks of a declaration -/

/-- The sort test answers `false` only on an arity whose sort is neither zero nor never zero. Port
of `ML-V Core/CollectOk.lean:246`. -/
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

/-- The sort test accepts an arity whose sort is zero, never zero, or may be not zero. Port of
`ML-V Core/CollectOk.lean:260`. -/
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

/-- `declExclusion` accepts a recursor on which its two checks pass, over the block it looks up
through the view. Port of `ML-V Core/CollectOk.lean:282`. -/
theorem declExclusion_rec_of {view : EnvView} {cfg : ErasureConfig} {R : RecursorVal}
    {ivs : List InductiveVal} {cvs : List ConstructorVal}
    (hivs : (R.all.flatMap (viewFind view)).filterMap
      (fun | .inductInfo iv => some iv | _ => none) = ivs)
    (hcvs : ((ivs.flatMap (·.ctors)).flatMap (viewFind view)).filterMap
      (fun | .ctorInfo cv => some cv | _ => none) = cvs)
    (h1 : recStaysConstant cfg.nat R ivs cvs = false)
    (h2 : recShapeInFragment R ivs cvs = true) :
    declExclusion view cfg (.recInfo R) = .ok () := by
  subst hivs hcvs
  rw [declExclusion]
  split
  · next h => exact absurd h (by rw [Bool.not_eq_true]; exact h1)
  · split
    · rfl
    · next h => exact absurd h2 h

/-- The constructors that a lookup of constructors in a list of the view's declarations finds are
those the view has. Port of `ML-V Core/CollectOk.lean:296`. -/
theorem viewCtors_of_mapM {view : EnvView} {decls : List ConstantInfo}
    (hvw : ∀ y ∈ decls, view.find? y.name = some y) {f : Name → Option ConstructorVal}
    (hf : ∀ c cv, f c = some cv → findDecl decls c = some (.ctorInfo cv)) :
    ∀ {l : List Name} {cvs : List ConstructorVal}, l.mapM f = some cvs →
      (l.flatMap (viewFind view)).filterMap (fun | .ctorInfo cv => some cv | _ => none) = cvs
  | [], cvs, h => by cases h; rfl
  | n :: l, cvs, h => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, cvs', hl, rfl⟩ := h
    have hfd := hf n cv hcv
    obtain ⟨hm, hn⟩ := findDecl_eq_some hfd
    have hv : viewFind view n = [.ctorInfo cv] := viewFind_of (hn ▸ hvw _ hm) hn
    simp only [List.flatMap_cons, hv, List.singleton_append, List.filterMap_cons]
    rw [viewCtors_of_mapM hvw hf hl]

/-- `declExclusion` accepts a recursor in the shape that `RecInFragment` admits over a list of the
view's declarations: the block it looks up through the view is the one `RecInFragment` reads from
the list. Port of `ML-V Core/CollectOk.lean:318`. -/
theorem dex_rec {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}
    (hvw : ∀ y ∈ decls, view.find? y.name = some y) {R : RecursorVal}
    (hfr : RecInFragment cfg decls R) : declExclusion view cfg (.recInfo R) = .ok () := by
  obtain ⟨T, iv, cvs, -, hall, hblk, hsh, hsc⟩ := hfr
  unfold recBlockOf? at hblk
  rw [hall] at hblk
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hblk
  obtain ⟨_, ⟨iv', hiv, _, rfl, rfl⟩, cvs', hcvs, h⟩ := hblk
  simp only [Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hcvs
  have hfI : findDecl decls T = some (.inductInfo iv') := by
    split at hiv
    · cases hiv; assumption
    · cases hiv
  obtain ⟨hm, hn⟩ := findDecl_eq_some hfI
  refine declExclusion_rec_of (ivs := [iv']) ?_ ?_ hsc hsh
  · rw [hall]
    simp [viewFind_of (hn ▸ hvw _ hm) hn]
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine viewCtors_of_mapM hvw (fun c cv h => ?_) hcvs
    split at h
    · cases h; assumption
    · cases h

/-- `declExclusion` accepts a definition, theorem, opaque, axiom, inductive or constructor in the
first-phase fragment. Part of `ML-V Core/CollectOk.lean:559 Frag.dex`. -/
theorem dex_nonrec {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}
    {ci : ConstantInfo} (hph : PhaseIDecl view cfg decls ci) (hnr : ∀ R, ci ≠ .recInfo R) :
    declExclusion view cfg ci = .ok () := by
  cases ci with
  | recInfo r => exact absurd rfl (hnr r)
  | quotInfo _ => rfl
  | thmInfo t =>
    have h4 : t.all = [t.name] := hph
    simp [declExclusion, h4]; rfl
  | defnInfo d =>
    obtain ⟨h1, h4, h2 | h2, h3⟩ := hph
    · simp [declExclusion, h1, h2, h3, h4]; rfl
    · simp only [Bool.and_eq_true] at h2
      simp [declExclusion, h1, h2.1, h2.2, h3, h4]; rfl
  | opaqueInfo o =>
    obtain ⟨h1, h4, h2, h3⟩ := hph
    simp [declExclusion, h1, h2, h3, h4]; rfl
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

/-- A `for` loop whose body yields on every element succeeds. Port of
`ML-V Core/CollectOk.lean:344`. -/
theorem forIn_ok_of {ε α : Type} {f : α → Unit → Except ε (ForInStep Unit)} :
    ∀ {l : List α}, (∀ a ∈ l, f a () = .ok (.yield ())) → forIn l () f = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons, h a List.mem_cons_self]
    exact forIn_ok_of (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)

/-! ## The `casesOn` recognizer -/

/-- What `recognizeCasesOn` checks: the view's `T` and `T.rec`, and `casesInfo?` on `recogList`.
Port of `ML-V Core/CollectSpec.lean:772`. -/
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

/-- The declarations `recognizeCasesOn` checks are the view's. Port of
`ML-V Core/CollectSpec.lean:914`. -/
theorem recogList_view {view : EnvView} {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal}
    {T : Name} (hd : view.find? d.name = some (.defnInfo d))
    (hI : viewFind view T = [.inductInfo I]) (hR : viewFind view (mkRecName T) = [.recInfo R]) :
    ∀ y ∈ recogList view (.defnInfo d) I R, view.find? y.name = some y := by
  have vf : ∀ {n y}, y ∈ viewFind view n → view.find? y.name = some y := fun h => by
    rw [(viewFind_mem h).2]; exact (viewFind_mem h).1
  intro y hy
  simp only [recogList, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hy
  rcases hy with rfl | rfl | rfl | ⟨x, -, hx⟩ | ⟨x, -, hx⟩
  · exact hd
  · exact vf (n := T) (hI ▸ List.mem_singleton_self _)
  · exact vf (n := mkRecName T) (hR ▸ List.mem_singleton_self _)
  · exact vf hx
  · exact vf hx

/-- On a list of the view's declarations that holds a definition `T.casesOn`, `T`, `T.rec`, `T`'s
constructors and `T.rec`'s block, `casesInfo?` answers as on the list `recognizeCasesOn` checks.
Part of `ML-V Core/CollectSpec.lean:1015 recog_of_ds_of`. -/
theorem recog_agree {view : EnvView} {decls : List ConstantInfo}
    (hvw : ∀ y ∈ decls, view.find? y.name = some y) {d : DefinitionVal} {I : InductiveVal}
    {R : RecursorVal} {T : Name} (hd : .defnInfo d ∈ decls) (hT : d.name = .str T "casesOn")
    (hI : viewFind view T = [.inductInfo I]) (hR : viewFind view (mkRecName T) = [.recInfo R])
    (hin : ∀ x, x = T ∨ x = mkRecName T ∨ x ∈ I.ctors ∨ x ∈ R.all → x ∈ decls.map (·.name)) :
    casesInfo? decls d.name = casesInfo? (recogList view (.defnInfo d) I R) d.name := by
  have hl := recogList_view (hvw _ hd) hI hR
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  have flat : ∀ {l : List Name} {x : Name}, x ∈ l → x ∈ decls.map (·.name) →
      x ∈ (l.flatMap (viewFind view)).map (·.name) := by
    intro l x hx hxd
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxd
    exact List.mem_map_of_mem (f := ConstantInfo.name) (List.mem_flatMap.2 ⟨_, hx, by
      rw [viewFind_of (hvw y hy) rfl]; exact List.mem_singleton_self _⟩)
  have both : ∀ x, x = d.name ∨ x = T ∨ x = mkRecName T ∨ x ∈ I.ctors ∨ x ∈ R.all →
      findDecl decls x = findDecl (recogList view (.defnInfo d) I R) x := by
    intro x hx
    have hxd : x ∈ decls.map (·.name) := by
      rcases hx with rfl | hx
      · exact List.mem_map_of_mem (f := ConstantInfo.name) hd
      · exact hin x hx
    refine findConst_agree hl hvw ?_ hxd
    simp only [recogList, List.cons_append, List.map_cons, List.map_append, List.mem_cons,
      List.mem_append]
    rcases hx with rfl | rfl | rfl | hx | hx
    · exact .inl rfl
    · exact .inr (.inl hIn.symm)
    · exact .inr (.inr (.inl hRn.symm))
    · exact .inr (.inr (.inr (.inl (flat hx hxd))))
    · exact .inr (.inr (.inr (.inr (flat hx hxd))))
  have same : ∀ {n : Name} {y z : ConstantInfo},
      findDecl (recogList view (.defnInfo d) I R) n = some y → view.find? n = some z → y = z := by
    intro n y z hy hz
    obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
    rw [← hy2, hl y hy1] at hz
    cases hz; rfl
  refine casesInfo?_congr (both _ (.inl rfl)) fun T' hT' => ?_
  rw [hT, Name.str.injEq] at hT'
  obtain ⟨rfl, -⟩ := hT'
  refine ⟨both _ (.inr (.inl rfl)), both _ (.inr (.inr (.inl rfl))), fun I' R' hI' hR' => ?_⟩
  cases same hI' hIf
  cases same hR' hRf
  exact ⟨fun x hx => both x (.inr (.inr (.inr (.inl hx)))),
    fun x hx => both x (.inr (.inr (.inr (.inr hx))))⟩

/-- A `casesOn` that `casesOnOf?` recognizes is recognized by `casesInfo?`. -/
theorem casesInfo?_of {X : List ConstantInfo} {n : Name} {iv : InductiveVal}
    (h : casesOnOf? X n = some iv) : ∃ c, casesInfo? X n = some c := by
  unfold casesOnOf? at h
  split at h
  · rename_i c hc; exact ⟨c, hc⟩
  · cases h

/-! ## The premises, on the declarations of `decls` -/

/-- The premises of `collectDeps_ok_of`, with the facts of the program they are used with. Port of
`ML-V Core/CollectOk.lean:354`, with the kinds of the names of inductives and constructors and the
blocks of recursors (`recs_mention`) where that file has Metalean's `ProgEnv`. -/
structure Frag (P : List ConstantInfo) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (e : Expr) : Prop where
  vw : ∀ y ∈ decls, view.find? y.name = some y
  sub : SubEnv decls P
  ind : ∀ iv, .inductInfo iv ∈ decls → (∀ n ∈ iv.all, ∃ t, findDecl P n = some (.inductInfo t)) ∧
    ∀ n ∈ iv.ctors, ∃ c, findDecl P n = some (.ctorInfo c)
  ctor : ∀ cv, .ctorInfo cv ∈ decls → ∃ t, findDecl P cv.induct = some (.inductInfo t)
  recs : ∀ R, .recInfo R ∈ decls → ∀ n ∈ R.all, mentionsAny [n] R.type = true
  rc : ReadClosed decls e
  phase : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci
  plainE : PlainExpr cfg e
  plain : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → PlainExpr cfg x
  recShapedE : RecShaped cfg decls e
  recShaped : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecShaped cfg decls x
  preRead : PreRead view cfg decls

namespace Frag

variable {P : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}
  {decls : List ConstantInfo} {e : Expr} (hf : Frag P view cfg decls e)
include hf

/-- A declaration of `decls` is the first of its name. Port of `ML-V Core/CollectOk.lean:376`. -/
theorem fd {y : ConstantInfo} (hy : y ∈ decls) : findDecl decls y.name = some y := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 (List.mem_map_of_mem hy))
  obtain ⟨hz1, hz2⟩ := findDecl_eq_some hz
  have h := hf.vw z hz1
  rw [hz2, hf.vw y hy] at h
  cases h
  exact hz

/-- What `ReadClosed` asks of each declaration. Port of `ML-V Core/CollectOk.lean:386`. -/
theorem rcd {ci : ConstantInfo} (hci : ci ∈ decls) :
    let inD := fun c => (findDecl decls c).isSome = true
    (∀ x, ReadExpr decls ci x → ConstsIn inD x ∧ (HasNatLit x → inD ``Nat)) ∧
    (∀ n ∈ ci.all, inD n) ∧ (∀ iv, ci = .inductInfo iv → ∀ n ∈ iv.ctors, inD n) ∧
    (∀ cv, ci = .ctorInfo cv → inD cv.induct) ∧
    (∀ iv, casesOnOf? decls ci.name = some iv → inD iv.name ∧ inD (mkRecName iv.name)) ∧
    (∀ iv, ci = .inductInfo iv → iv.ctors.length = 1 → inD (mkRecName iv.name)) :=
  hf.rc.2.2 ci hci

/-- A definition, theorem or opaque of `decls` is alone in its block (`PhaseIDecl`), as every
declaration that is not an inductive or a recursor is. -/
theorem own {ci : ConstantInfo} (hci : ci ∈ decls) (hni : ∀ iv, ci ≠ .inductInfo iv) :
    ci.all = [ci.name] := by
  have hph := hf.phase ci hci
  cases ci with
  | defnInfo _ => obtain ⟨-, h, -⟩ := hph; exact h
  | thmInfo _ => exact hph
  | opaqueInfo _ => obtain ⟨-, h, -⟩ := hph; exact h
  | inductInfo iv => exact absurd rfl (hni iv)
  | axiomInfo _ | quotInfo _ | ctorInfo _ | recInfo _ => rfl

/-- The block of a recursor of `decls` is in `decls`: the recursor's type names it
(`recs_mention`) and is read. -/
theorem rall {R : RecursorVal} (hR : .recInfo R ∈ decls) : ∀ n ∈ R.all, n ∈ decls.map (·.name) :=
  fun n hn => findDecl_isSome_iff.1
    (mentionsAny_consts (hf.recs R hR n hn) ((hf.rcd hR).1 _ (.inl rfl)).1)

omit hf in
/-- A name of `decls` that is no recursor of `decls` or a recursor in the fragment's shape is
covered. Port of `ML-V Core/CollectOk.lean:399`. -/
theorem covered {n : Name} (hin : (findDecl decls n).isSome = true)
    (hrs : ∀ rv, findDecl decls n = some (.recInfo rv) → RecInFragment cfg decls rv) :
    Cov cfg decls n := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  exact ⟨y, hy1, hy2, fun R hR => hrs R (hR ▸ hy)⟩

/-- A name of `decls` whose declaration in the program is not a recursor is covered. Port of
`ML-V Core/CollectOk.lean:407`. -/
theorem covered_of_P {n : Name} (hin : (findDecl decls n).isSome = true) {x : ConstantInfo}
    (hx : findDecl P n = some x) (hr : ∀ R, x ≠ .recInfo R) : Cov cfg decls n := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  have h := hf.sub y hy1
  rw [hy2, hx] at h
  cases h
  exact ⟨_, hy1, hy2, fun R hR => absurd hR (hr R)⟩

/-- `Nat`, when in `decls`, is no recursor of `decls`: the recursors of `decls` are named
`T.rec`. Port of `ML-V Core/CollectOk.lean:418`. -/
theorem nat_covered (hin : (findDecl decls ``Nat).isSome = true) : Cov cfg decls ``Nat := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
  refine ⟨y, hy1, hy2, fun R hR => ?_⟩
  subst hR
  have hph := hf.phase _ hy1
  have hn : ∃ T, R.name = mkRecName T := by
    rcases hph with ⟨T, -, hT, -⟩ | ⟨T, -, hT, -⟩ | ⟨T, -, -, hT, -⟩ <;> exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hn
  have h2 : (ConstantInfo.recInfo R).name = R.name := rfl
  rw [h2, hT] at hy2
  unfold mkRecName at hy2
  injection hy2 with _ h
  exact absurd h (by decide)

/-- The names `exprConsts` lists on an expression whose constants are in `decls`, recursors only in
the fragment's shape, are covered. Port of `ML-V Core/CollectOk.lean:435`. -/
theorem names_of {x : Expr} (hc : ConstsIn (fun c => (findDecl decls c).isSome = true) x)
    (hnl : HasNatLit x = true → (findDecl decls ``Nat).isSome = true) (hr : RecShaped cfg decls x)
    (hpl : PlainExpr cfg x) : ∃ cs, exprConsts cfg x = .ok cs ∧ ∀ n ∈ cs, Cov cfg decls n := by
  obtain ⟨cs, hcs⟩ := exprConsts_of_plain hpl
  exact ⟨cs, hcs, exprConsts_mem hcs
    (ConstsIn_mono (fun c hc => covered hc.1 hc.2) (ConstsIn_and hc hr))
    (fun h => hf.nat_covered (hnl h))⟩

/-- The names of a read expression are covered. Port of `ML-V Core/CollectOk.lean:444`. -/
theorem read_names {ci : ConstantInfo} (hci : ci ∈ decls) {x : Expr} (hx : ReadExpr decls ci x) :
    ∃ cs, exprConsts cfg x = .ok cs ∧ ∀ n ∈ cs, Cov cfg decls n :=
  hf.names_of ((hf.rcd hci).1 x hx).1 ((hf.rcd hci).1 x hx).2 (hf.recShaped ci hci x hx)
    (hf.plain ci hci x hx)

/-- The names of the term are covered. Port of `ML-V Core/CollectOk.lean:450`. -/
theorem term_names : ∃ cs, exprConsts cfg e = .ok cs ∧ ∀ n ∈ cs, Cov cfg decls n :=
  hf.names_of hf.rc.1 hf.rc.2.1 hf.recShapedE hf.plainE

/-- A `casesOn` that the view recognizes is recognized on `decls`, with its inductive and its
recursor in `decls`: otherwise its value is read, so the recursor at its head is in `decls`
(`ReadClosed`) with its block (`rall`), which holds the inductive, and the inductive's
constructors (`ReadClosed`), and `casesInfo?` answers on `decls` as on the view's declarations
(`recog_cases`). Port of `ML-V Core/CollectOk.lean:464`. -/
theorem recog_dec {d : DefinitionVal} {I : InductiveVal} {R : RecursorVal}
    {ctors : List ConstantInfo} (hd : .defnInfo d ∈ decls)
    (hrec : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors)) :
    (casesOnOf? decls d.name).isSome ∧ .inductInfo I ∈ decls ∧ .recInfo R ∈ decls ∧
      d.name = .str I.name "casesOn" ∧ ctors = I.ctors.flatMap (viewFind view) := by
  obtain ⟨T, hT, hI, hR, hct, hc⟩ := recognize_iff.1 hrec
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  obtain ⟨hRf, hRn⟩ := viewFind_eq hR
  have hT' : d.name = .str T "casesOn" := hT
  have hIn' : I.name = T := hIn
  have hRn' : R.name = mkRecName T := hRn
  have hcs : (casesOnOf? decls d.name).isSome := by
    cases hnone : casesOnOf? decls d.name with
    | some _ => rfl
    | none =>
      exfalso
      have hx : ReadExpr decls (.defnInfo d) d.value :=
        .inr (.inl ⟨d, rfl, rfl, by rw [hnone]; rfl⟩)
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hc
      obtain ⟨T', d', I', R', k, body, us, hn, -, hd', -, hR', hTR, hb, hhd⟩ := casesInfo?_reads hc
      have hTT : T' = T := by
        have h2 : Name.str T "casesOn" = Name.str T' "casesOn" := hT'.symm.trans hn
        rw [Name.str.injEq] at h2
        exact h2.1.symm
      -- the recursor at the head of the value is the view's `T.rec`
      have hl := recogList_view (hf.vw _ hd) hI hR
      obtain ⟨hR'1, hR'2⟩ := findDecl_eq_some hR'
      have hRR : R' = R := by
        have h1 := hl _ hR'1
        rw [hR'2, hTT, hRf] at h1
        cases h1; rfl
      obtain ⟨hd'1, hd'2⟩ := findDecl_eq_some hd'
      have hdd : d' = d := by
        have h1 := hl _ hd'1
        rw [hd'2, hf.vw _ hd] at h1
        cases h1; rfl
      rw [hRR] at hhd
      rw [hdd] at hb
      have hhead : ∀ {p : Name → Prop}, ConstsIn p d.value → p R.name := fun h => by
        have hbody := ConstsIn_spine (ConstsIn_peelLams hb h)
        rw [hhd] at hbody
        exact hbody
      have hRd : .recInfo R ∈ decls :=
        mem_of_view hf.vw (findDecl_isSome_iff.1 (hhead ((hf.rcd hd).1 _ hx).1))
          (by rw [hRn']; exact hRf)
      -- its block, which holds `T`, is in `decls`
      have hTd : T ∈ decls.map (·.name) := hf.rall hRd T (by rw [← hTT, ← hRR]; exact hTR)
      have hId : .inductInfo I ∈ decls := mem_of_view hf.vw hTd hIf
      have hrc := recog_cases hf.vw hd hrec fun x hx => by
        rcases hx with rfl | rfl | hx | hx
        · exact List.mem_map_of_mem (f := ConstantInfo.name) hId
        · exact List.mem_map_of_mem (f := ConstantInfo.name) hRd
        · exact findDecl_isSome_iff.1 ((hf.rcd hId).2.2.1 I rfl x hx)
        · exact hf.rall hRd x hx
      rw [hnone] at hrc
      exact absurd hrc (by simp)
  -- the recognized inductive and its recursor are in `decls`
  obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.1 hcs
  obtain ⟨c, hc'⟩ := casesInfo?_of hiv
  obtain ⟨T₀, -, I₀, R₀, -, -, -, hn, -, -, hI₀, hR₀, -⟩ := casesInfo?_reads hc'
  have hTT : T₀ = T := by
    rw [hT', Name.str.injEq] at hn
    exact hn.1.symm
  rw [hTT] at hI₀ hR₀
  have hId : .inductInfo I ∈ decls :=
    mem_of_view hf.vw (findDecl_isSome_iff.1 (by rw [hI₀]; rfl)) hIf
  have hRd : .recInfo R ∈ decls :=
    mem_of_view hf.vw (findDecl_isSome_iff.1 (by rw [hR₀]; rfl)) hRf
  exact ⟨hcs, hId, hRd, by rw [hT', hIn'], hct⟩

/-- A `casesOn` recognized on `decls` is recognized by the view: `casesInfo?` answers on the
view's declarations as on `decls`, which holds the inductive's constructors (`ReadClosed`) and the
recursor's block (`rall`). Port of `ML-V Core/CollectOk.lean:550`. -/
theorem recog_of_dec {d : DefinitionVal} (hd : .defnInfo d ∈ decls) {iv : InductiveVal}
    (hcs : casesOnOf? decls d.name = some iv) :
    ∃ I R ctors, recognizeCasesOn view (.defnInfo d) = some (I, R, ctors) := by
  obtain ⟨c, hc⟩ := casesInfo?_of hcs
  obtain ⟨T, -, I, R, -, -, -, hn, -, -, hI, hR, -⟩ := casesInfo?_reads hc
  obtain ⟨hIm, hIn⟩ := findDecl_eq_some hI
  obtain ⟨hRm, hRn⟩ := findDecl_eq_some hR
  have hIv : viewFind view T = [.inductInfo I] := viewFind_of (hIn ▸ hf.vw _ hIm) hIn
  have hRv : viewFind view (mkRecName T) = [.recInfo R] := viewFind_of (hRn ▸ hf.vw _ hRm) hRn
  have hag := recog_agree hf.vw hd hn hIv hRv fun x hx => by
    rcases hx with rfl | rfl | hx | hx
    · exact findDecl_isSome_iff.1 (by rw [hI]; rfl)
    · exact findDecl_isSome_iff.1 (by rw [hR]; rfl)
    · exact findDecl_isSome_iff.1 ((hf.rcd hIm).2.2.1 I rfl x hx)
    · exact hf.rall hRm x hx
  refine ⟨I, R, _, recognize_iff.2 ⟨T, hn, hIv, hRv, rfl, ?_⟩⟩
  exact Option.isSome_iff_exists.2 ⟨c, hag.symm.trans hc⟩

/-- `declExclusion` accepts a declaration of `decls` that is not a recursor or is a recursor in the
fragment's shape. Port of `ML-V Core/CollectOk.lean:559`. -/
theorem dex {ci : ConstantInfo} (hci : ci ∈ decls)
    (hnr : ∀ R, ci = .recInfo R → RecInFragment cfg decls R) :
    declExclusion view cfg ci = .ok () := by
  cases ci with
  | recInfo r => exact dex_rec hf.vw (hnr r rfl)
  | _ => exact dex_nonrec (hf.phase _ hci) nofun

/-- One step of the closure succeeds on a declaration of `decls` that is not a recursor or is a
recursor in the fragment's shape, reads covered names, and adds a companion recursor of `decls`
whose type's names are covered and, for a definition, only for a `casesOn` recognized on
`decls`. Port of `ML-V Core/CollectOk.lean:604`. -/
theorem step {ci : ConstantInfo} (hci : ci ∈ decls)
    (hnr : ∀ R, ci = .recInfo R → RecInFragment cfg decls R) :
    ∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, Cov cfg decls n) ∧
      (∀ r, ro = some r → r ∈ decls ∧ r.name ≠ ci.name ∧
        ∃ tys, exprConsts cfg r.type = .ok tys ∧ ∀ n ∈ tys, Cov cfg decls n) ∧
      (∀ r d, ro = some r → ci = .defnInfo d → (casesOnOf? decls ci.name).isSome) := by
  have hdex := hf.dex hci hnr
  obtain ⟨ty, hty, htyc⟩ := hf.read_names hci (x := ci.type) (.inl rfl)
  have hall : (∀ R, ci ≠ .recInfo R) → ∀ n ∈ ci.all, Cov cfg decls n := by
    intro hr n hn
    by_cases hi : ∃ iv, ci = .inductInfo iv
    · obtain ⟨iv, rfl⟩ := hi
      obtain ⟨t, ht⟩ := (hf.ind iv hci).1 n hn
      exact hf.covered_of_P ((hf.rcd hci).2.1 n hn) ht nofun
    · rw [hf.own hci (fun iv h => hi ⟨iv, h⟩), List.mem_singleton] at hn
      exact ⟨ci, hci, hn.symm, fun R hR => absurd hR (hr R)⟩
  -- a companion of `decls` that is a recursor, of a declaration that is not one
  have comp : (∀ R, ci ≠ .recInfo R) → ∀ R, .recInfo R ∈ decls →
      (ConstantInfo.recInfo R).name ≠ ci.name ∧
      ∃ tys, exprConsts cfg R.type = .ok tys ∧ ∀ n ∈ tys, Cov cfg decls n := by
    intro hr R hR
    refine ⟨fun he => hr R ?_, hf.read_names hR (.inl rfl)⟩
    have := hf.fd hR
    rw [he, hf.fd hci] at this
    cases this; rfl
  unfold closureStep
  rw [bind_ok_eq hdex, bind_ok_eq hty]
  cases ci with
  | recInfo r => exact ⟨ty, none, rfl, htyc, nofun, nofun⟩
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
          obtain ⟨-, -, -, hidx⟩ := hf.phase _ hI
          have hin := (hf.rcd hI).2.2.1 I rfl cn hcn
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hin
          obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
          have e1 := hf.vw y hy1
          rw [hy2, hcv] at e1
          cases e1
          have hk := hidx (by rw [← hdn]; exact hcs) cn hcn cv hy
          simp [hk]; rfl
        | _ => rfl
      · intro n hn
        simp only [List.mem_append, List.mem_cons] at hn
        rcases hn with hn | rfl | hn
        · exact htyc n hn
        · exact ⟨_, hI, rfl, fun _ h => nomatch h⟩
        · exact hall nofun n hn
      · intro r hr
        cases hr
        exact ⟨hR, comp nofun R hR⟩
      · intro _ _ _ _
        exact hcs
    | none =>
      have hnone : (casesOnOf? decls d.name).isNone := by
        cases h : casesOnOf? decls d.name with
        | none => rfl
        | some iv =>
          obtain ⟨I, R, ctors, h'⟩ := hf.recog_of_dec hci h
          rw [hrec] at h'; cases h'
      obtain ⟨vs, hvs, hvsc⟩ := hf.read_names hci (x := d.value) (.inr (.inl ⟨d, rfl, rfl, hnone⟩))
      obtain ⟨ps, hps, hpsc⟩ : ∃ ps, (match preDef? view cfg (.defnInfo d) with
          | some p => exprConsts cfg p
          | none => pure []) = .ok ps ∧ ∀ n ∈ ps, Cov cfg decls n := by
        cases hp : preDef? view cfg (.defnInfo d) with
        | none => exact ⟨[], rfl, nofun⟩
        | some p =>
          obtain ⟨h1, h2, h3, h4⟩ := hf.preRead _ hci p hp
          exact hf.names_of h1 h2 h4 h3
      refine ⟨ty ++ vs ++ ps ++ d.all, none, ?_, ?_, nofun, nofun⟩
      · dsimp only
        revert hps
        cases preDef? view cfg (.defnInfo d) with
        | none =>
          intro hps
          cases hps
          dsimp only
          rw [pure_bind, bind_ok_eq hvs]
          rfl
        | some p =>
          intro hps
          dsimp only at hps ⊢
          rw [bind_ok_eq hps, bind_ok_eq hvs]
          rfl
      · intro n hn
        simp only [List.mem_append] at hn
        rcases hn with ((hn | hn) | hn) | hn
        · exact htyc n hn
        · exact hvsc n hn
        · exact hpsc n hn
        · exact hall nofun n hn
  | thmInfo t =>
    refine ⟨ty ++ t.all, none, rfl, fun n hn => ?_, nofun, nofun⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact htyc n hn
    · exact hall nofun n hn
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
      · exact hall nofun n hn
  | inductInfo iv =>
    refine ⟨ty ++ iv.all ++ iv.ctors, _, rfl, fun n hn => ?_, fun r hr => ?_, nofun⟩
    · simp only [List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact htyc n hn
      · exact hall nofun n hn
      · obtain ⟨c, hc⟩ := (hf.ind iv hci).2 n hn
        exact hf.covered_of_P ((hf.rcd hci).2.2.1 iv rfl n hn) hc nofun
    · split at hr
      · rename_i c r' R hc hv
        cases hr
        obtain ⟨hvf, hvn⟩ := viewFind_eq hv
        have hin := (hf.rcd hci).2.2.2.2.2 iv rfl (by simp [hc])
        have hy1 : ConstantInfo.recInfo R ∈ decls :=
          mem_of_view hf.vw (findDecl_isSome_iff.1 hin) hvf
        exact ⟨hy1, comp nofun R hy1⟩
      · cases hr
  | ctorInfo cv =>
    refine ⟨ty ++ [cv.induct], none, rfl, fun n hn => ?_, nofun, nofun⟩
    rcases List.mem_append.1 hn with hn | hn
    · exact htyc n hn
    · rw [List.mem_singleton.1 hn]
      obtain ⟨t, ht⟩ := hf.ctor cv hci
      exact hf.covered_of_P ((hf.rcd hci).2.2.2.1 cv rfl) ht nofun
  | axiomInfo a => exact ⟨ty, none, rfl, htyc, nofun, nofun⟩
  | quotInfo q => exact ⟨ty, none, rfl, htyc, nofun, nofun⟩

/-- `dropKnown` succeeds on covered names: it drops the names the accumulator has (`declExclusion`
accepts those that are recursors, `dex_rec`) and stops at one it does not have. Port of
`ML-V Core/CollectOk.lean:750`. -/
theorem dropKnown_ok_of {acc : List ConstantInfo} (hacc : ∀ y ∈ acc, y ∈ decls) :
    ∀ {todo : List Name}, (∀ n ∈ todo, Cov cfg decls n) →
    ∃ rest, dropKnown view cfg acc todo = .ok rest ∧ (∀ n ∈ rest, n ∈ todo) ∧
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
      | recInfo R =>
        show (do declExclusion view cfg (.recInfo R); dropKnown view cfg acc todo) = _
        rw [bind_ok_eq (dex_rec hf.vw (hzr R rfl))]
        exact hrest
      | _ => exact hrest

omit hf in
/-- A list of declarations of `decls` with distinct names, at least as long as `decls`, has every
name of `decls`. Port of `ML-V Core/CollectOk.lean:782`. -/
theorem full {acc : List ConstantInfo} (hacc : ∀ y ∈ acc, y ∈ decls)
    (hnd : (acc.map (·.name)).Nodup) (hlen : decls.length ≤ acc.length) {n : Name}
    (hn : n ∈ decls.map (·.name)) : n ∈ acc.map (·.name) := by
  refine Classical.byContradiction fun hna => ?_
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
distinct names, and its recognized `casesOn` are recognized on `decls`. Port of
`ML-V Core/CollectOk.lean:799`. -/
theorem closure_ok_of : ∀ (f : Nat) {todo : List Name} {acc : List ConstantInfo}
    {cases : List Name}, (∀ y ∈ acc, y ∈ decls) → (acc.map (·.name)).Nodup →
    (∀ n ∈ todo, Cov cfg decls n) → (∀ m ∈ cases, (casesOnOf? decls m).isSome) →
    decls.length ≤ f + acc.length →
    ∃ res, closure view cfg f todo acc cases = .ok res ∧ (∀ y ∈ res.1, y ∈ decls) ∧
      (res.1.map (·.name)).Nodup ∧ ∀ m ∈ res.2, (casesOnOf? decls m).isSome
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
      exact absurd (findDecl_isSome_iff.2 hin)
        (by rw [show findDecl acc n = findConst acc n from rfl, hn]; simp)
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
      have htl : ∀ m ∈ rest', Cov cfg decls m :=
        fun m hm => htodo m (hsub m (List.mem_cons_of_mem _ hm))
      obtain ⟨ns, ro, hstep, hns, hro, hcas⟩ := hf.step hy hyr
      have hnd1 : ((y :: acc).map (·.name)).Nodup := by
        rw [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => absurd (findDecl_isSome_iff.2 hm)
          (by rw [show findDecl acc y.name = findConst acc y.name from rfl, hnacc]; simp), hnd⟩
      have hacc1 : ∀ z ∈ y :: acc, z ∈ decls := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hy
        · exact hacc z hz
      have hlen1 : decls.length ≤ f + (y :: acc).length := by
        rw [List.length_cons]; omega
      have htodo1 : ∀ m ∈ ns ++ rest', Cov cfg decls m := by
        intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hns m hm
        · exact htl m hm
      rw [closure, bind_ok_eq hrest]
      dsimp only
      rw [hf.vw y hy]
      dsimp only
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [bind_ok_eq hstep]
      cases ro with
      | none =>
        exact closure_ok_of f hacc1 hnd1 htodo1 hcases hlen1
      | some r =>
        obtain ⟨hr, hrn, tys, htys, htysc⟩ := hro r rfl
        have hcases1 : ∀ m ∈ (if y matches .defnInfo _ then y.name :: cases else cases),
            (casesOnOf? decls m).isSome := by
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

/-- No collision among declarations with distinct names and kernames. Port of
`ML-V Core/CollectOk.lean:895`. -/
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
      have := hk cj (List.mem_cons_of_mem _ hcj) ci List.mem_cons_self (kername_eq_of_beq hb)
      exact hnd.1 (this ▸ List.mem_map_of_mem hcj)
    rw [hf]
    exact ih hnd.2 fun a ha b hb => hk a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)

/-- No block collision on a sub-list of declarations whose block names are distinct. Port of
`ML-V Core/CollectOk.lean:912`. -/
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
    have := (hb iv₂ iv₁ hd₂ hd₁).1 (kername_eq_of_beq hc.1)
    simp [this] at hc
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro ci hci hc
  rw [Bool.and_eq_true] at hc
  have hem : EmitsConst ci = true := by
    cases ci <;> simp_all [EmitsConst]
  exact (hb iv₁ iv₁ hd₁ hd₁).2 ci (hs _ hci) hem (kername_eq_of_beq hc.2)

/-- `eliminatedUndecided` answers `none` on a sub-list of `decls` whose recognized `casesOn` are
recognized on `decls`, when every inductive of `decls` is in the first-phase fragment. Port of
`ML-V Core/CollectOk.lean:942`. -/
theorem eliminatedUndecided_none_of {view : EnvView} {cfg : ErasureConfig}
    {l decls : List ConstantInfo} {cases : List Name} (hs : ∀ y ∈ l, y ∈ decls)
    (hfd : ∀ y ∈ decls, findDecl decls y.name = some y)
    (hph : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci)
    (hcases : ∀ m ∈ cases, (casesOnOf? decls m).isSome) :
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
/-- **The fragment test accepts every program whose read closure lies inside the first-phase
fragment**: on a program con-leche accepts, read through a view that agrees with it, a term with a
sub-environment `decls` that holds what the traversal reads (`ReadClosed`), keeps every declaration
inside the fragment (`PhaseIDecl`), reads only plain expressions (`PlainExpr`) that name recursors
only in the fragment's shape (`RecShaped`), reads the compiled pre-definitions of its declarations
as values (`PreRead`), has distinct kernames and λ□ block names and fewer declarations than the
fuel, `Erasure.collectDeps` succeeds. Its closure is a sub-list of `decls`. The kinds of the names
an inductive or a constructor reads come from con-leche's acceptance (`blockOf?`, `declOf?`), the
block of a recursor from its type (`recs_mention`). Port of `ML-V Core/CollectOk.lean:997`.
Reference: none (DV-26). -/
theorem collectDeps_ok_of : collectDeps_ok_of_statement := by
  intro P decls env e view cfg hP hview _ hrm hsub hrc hph hpl hrf hprd hki hbi hlen
  have hmem : ∀ ci ∈ decls, ci ∈ P := fun ci hci => (findDecl_mem (hsub ci hci)).1
  have hf : Frag P view cfg decls e :=
    ⟨fun y hy => (hview y (hmem y hy)).1, hsub, fun iv hiv => ind_kinds hP (hmem _ hiv),
      fun cv hcv => ctor_kind hP (hmem _ hcv), fun R hR => recs_mention hP R (hmem _ hR), hrc, hph,
      hpl.1, hpl.2, hrf.1, hrf.2, hprd⟩
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
