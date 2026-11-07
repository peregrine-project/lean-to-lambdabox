import EraseProof.Bridge.CasesWhred
import EraseProof.Bridge.Inst

/-!
# Reduction of a recursor on a constructor value

A saturated recursor `T.rec` of a single inductive without indices, whose recursive fields take
no arguments, applied to parameters, motives, minors and a constructor value of `T`, translates to a
Metalean recursor node that reduces by ι (`WHRed.iota`) and β (through `wrapCase`) to the
translation of the constructor's minor applied to the fields and to the induction hypotheses
`T.rec ps ms mvs f` of the recursive fields, which are Metalean's induction hypotheses
(`RecWhred.recIota_whred`). The recursive fields and their order are those of `recShape` on the
recursor's Lean type, which `IndBlock.recIHs` relates to Metalean's block. Reference:
`WHRed.iota` (`ML Syntax/Reduction.lean:60`), `iotaRhs` (`ML Syntax/Inductive/Iota.lean:161`).
-/

open Lean Erasure
open Metalean (WHRed WHRedS Head Defeq)

namespace EraseProof

namespace RecWhred

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- The block of a recursor of a single inductive: the inductive, found in the environment, and its
constructors, in order. -/
theorem recBlock?_single {σ : EvalEnv} {rv : RecursorVal} {T : Name} {iv : InductiveVal}
    {cvs : List ConstructorVal} (hall : rv.all = [T]) (h : σ.recBlock? rv = some ([iv], cvs)) :
    findDecl σ.decls T = some (.inductInfo iv) ∧ iv.ctors.mapM σ.ctorOf? = some cvs := by
  unfold EvalEnv.recBlock? at h
  rw [hall] at h
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨ivs, ⟨i, hi, l, rfl, rfl⟩, cvs', hcvs, h⟩ := h
  simp only [Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by simpa using hcvs⟩
  revert hi
  unfold EvalEnv.indOf?
  cases findDecl σ.decls T with
  | none => intro h; cases h
  | some ci => cases ci <;> intro h <;> simp at h; subst h; rfl

/-- A successful `mapM` over `List.ofFn` gives, entry by entry, the images. -/
theorem mapM_ofFn {α β : Type} {k : Nat} {f : α → Option β} {g : Fin k → α} {r : List β}
    (h : (List.ofFn g).mapM f = some r) : r.length = k ∧ ∀ i : Fin k, ∃ y, r[i.val]? = some y ∧ f (g i) = some y := by
  induction k generalizing r with
  | zero => simp at h; subst h; exact ⟨rfl, fun i => i.elim0⟩
  | succ k ih =>
    rw [List.ofFn_succ, List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hall⟩ := ih hys
    refine ⟨by simp [hl], fun i => ?_⟩
    refine Fin.cases ⟨y, rfl, hy⟩ (fun j => ?_) i
    obtain ⟨z, hz, hf⟩ := hall j
    exact ⟨z, by simpa using hz, hf⟩

/-- What the program says about a recursor of a single inductive of the evaluation environment:
the block at its Metalean head, the recursor and the inductive in it at the sort `s` (the only one),
the table entries, and the constructors read by `recBlock?` (the block's, in order). -/
theorem rec_block {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) :
    ∃ (ι : Metalean.IndSig) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (lps₀ : List Name)
      (Is : Fin ι.nsorts → InductiveVal)
      (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal)
      (Rs : Fin ι.nsorts → RecursorVal) (orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat),
      CasesWhred.BlockAt P B η lps₀ Is Cs Rs orders ∧ rv = Rs s ∧ iv = Is s ∧ T = (Is s).name ∧
      B T = some (.ind η s) ∧
      B c = some (.recr η s (List.ofFn fun t => List.ofFn fun c => orders t c)) ∧
      ι.nsorts = 1 ∧ cvs = List.ofFn (Cs s) := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨hT, hcvs⟩ := recBlock?_single hall hblk
  obtain ⟨ι, η, s, hBT, -, -, -⟩ := henv.lookup_ind (hP hT)
  obtain ⟨lps₀, Is, Cs, Rs, orders, hb⟩ := CasesWhred.ProgEnv.block henv η
  obtain ⟨⟨_, _, _, _, hIB⟩, hnd, hfd, hrec, hindB, hctorB⟩ := hb
  have hTs : T = (Is s).name := hindB _ _ hBT
  have hmemI : ∀ t, ConstantInfo.inductInfo (Is t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hmemC : ∀ t c, ConstantInfo.ctorInfo (Cs t c) ∈ IndBlock.decls Is Cs Rs := fun t c => by
    simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
    exact .inl (.inr ⟨_, ⟨t, rfl⟩, List.mem_ofFn.mpr ⟨c, rfl⟩⟩)
  have hmemR : ∀ t, ConstantInfo.recInfo (Rs t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hfdI : ∀ t, findDecl P (Is t).name = some (.inductInfo (Is t)) := fun t => hfd _ (hmemI t)
  have hfdC : ∀ t c, findDecl P (Cs t c).name = some (.ctorInfo (Cs t c)) := fun t c =>
    hfd _ (hmemC t c)
  have hfdR : ∀ t, findDecl P (Rs t).name = some (.recInfo (Rs t)) := fun t => hfd _ (hmemR t)
  have hivs : iv = Is s := by
    have h1 := hP hT
    rw [hTs, hfdI s] at h1
    cases h1; rfl
  subst hivs
  have hcR : c = (Rs s).name := by rw [hcT, hTs, (hIB.recr s).1]
  have hrvs : rv = Rs s := by
    have h1 := hP hcr
    rw [hcR, hfdR s] at h1
    cases h1; rfl
  subst hrvs
  have hns : ι.nsorts = 1 := by
    obtain ⟨-, -, -, -, -, hRall, -⟩ := hIB.recr s
    obtain ⟨-, -, hIall, -⟩ := hIB.ind s
    have := congrArg List.length (hRall.trans hIall)
    rw [hall] at this
    simpa using this.symm
  refine ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, ⟨⟨_, _, _, _, hIB⟩, hnd, hfd, hrec, hindB, hctorB⟩,
    rfl, rfl, hTs, hBT, by rw [hcR]; exact hrec s, hns, ?_⟩
  rw [(hIB.ind s).2.2.2.2.2.1] at hcvs
  obtain ⟨hl, hent⟩ := mapM_ofFn hcvs
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ι.nctors s
  · obtain ⟨y, hy, hf⟩ := hent ⟨i, hi⟩
    rw [hy, List.getElem?_ofFn]
    simp only [hi, ↓reduceDIte, Option.some.injEq]
    revert hf
    unfold EvalEnv.ctorOf?
    cases hx : findDecl σ.decls (Cs s ⟨i, hi⟩).name with
    | none => intro h; cases h
    | some ci =>
      cases ci <;> intro h <;> simp at h
      subst h
      have h1 := hP hx
      rw [hfdC s ⟨i, hi⟩] at h1
      cases h1; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- A list with one inductive's constructors per sort, over a single sort. -/
theorem ofFn_single {α : Type} {k : Nat} (hk : k = 1) (s : Fin k) (f : Fin k → α) :
    List.ofFn f = [f s] := by
  subst hk
  rw [List.ofFn_succ, List.ofFn_zero]
  congr
  exact (Fin.fin_one_eq_zero s).symm

/-- The image of a constructor value of the inductive at the Metalean head `η`, sort `s`: a
constructor node of that sort whose fields translate the Lean fields, related by the constructor's
Metalean field order. -/
theorem major_ctor {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {lps : List Name} {T : Name} {mj : Expr} {k : Nat} {fs : List Expr} {ι : Metalean.IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {a₀ : Metalean.Expr ζ lps.length 0}
    (hBT : B T = some (.ind η s)) (hcv : CtorValue σ T mj k fs)
    (ha : TrM E B lps .nil [] mj a₀) :
    ∃ (k' : Fin (ι.nctors s)) (order : List Nat) (ls₂ : Fin ι.nlevels → Metalean.Level lps.length)
      (ps₂ : Fin ι.nparams → Metalean.Expr ζ lps.length 0)
      (fds : Fin (ι.ctors s k').nfields → Metalean.Expr ζ lps.length 0)
      (recFds : Fin (ι.ctors s k').nrecFields → Metalean.Expr ζ lps.length 0)
      (fsT : List (Metalean.Expr ζ lps.length 0)) (C : Name),
      k'.val = k ∧ (∃ cv, findDecl σ.decls C = some (.ctorInfo cv) ∧ cv.cidx = k) ∧
      B C = some (.ctor η s k' order) ∧
      MetaOrderOK order (ι.ctors s k').nfields (ι.ctors s k').nrecFields ∧
      a₀ = .ctor η s k' ls₂ ps₂ fds recFds ∧
      fsT.length = (ι.ctors s k').nfields + (ι.ctors s k').nrecFields ∧
      List.Forall₂ (TrM E B lps .nil []) fs fsT ∧ CasesWhred.FieldsPerm order fsT fds recFds := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨C, us', cv, ps, hC, hind, hcidx, hps, hfs, rfl⟩ := hcv
  obtain ⟨ι', η', s', k', order, hBC, hk, hnp, hnf, hmo, hBT'⟩ := ProgEnv.lookup_ctor henv (hP hC)
  rw [hind, hBT] at hBT'
  cases hBT'
  obtain ⟨ls₂, ps₂, fds, recFds, fs'', rfl, hrel, hperm⟩ :=
    TrM.ctor_inv hBC (by simp only [List.length_append]; omega) ha
  obtain ⟨hlT, hpermT, htake⟩ := CasesWhred.order_fields hmo hperm
  refine ⟨k', order, ls₂, ps₂, fds, recFds, _, C, hk.symm.trans hcidx, ⟨cv, hC, hcidx⟩, hBC, hmo,
    rfl, hlT, ?_, hpermT⟩
  refine CasesWhred.forall₂_of_getElem? (by rw [hlT, hfs, hnf]) fun j x y h1 h2 => ?_
  have hj : j < (ι.ctors s k').nfields + (ι.ctors s k').nrecFields := by
    have := (List.getElem?_eq_some_iff.mp h2).1; omega
  refine hrel (ps.length + j) x y ?_ ?_
  · rw [List.getElem?_append_right (by omega)]; simpa using h1
  · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn, hps, hnp,
      Nat.add_sub_cancel_left, ← htake j hj]
    exact h2

/-- Metalean's induction hypothesis of a recursive field without arguments, into an index-free
sort `s₀`: the recursor node on the field. -/
theorem iotaIH_eq {ι : Metalean.IndSig} {nfields arity : Nat} {target : Fin ι.nsorts}
    (fd : Metalean.RecField ζ ι nfields arity target) (h : arity = 0) {s₀ : Fin ι.nsorts}
    (ht : target = s₀) (hni : ι.nindices s₀ = 0) {ℓ n : Nat} (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (l : Metalean.Level ℓ)
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Metalean.Expr ζ ℓ n)
    (σ : Metalean.Subst ζ ℓ (ι.nparams + nfields) n) (r : Metalean.Expr ζ ℓ n)
    (is₀ : Fin (ι.nindices s₀) → Metalean.Expr ζ ℓ n) :
    fd.iotaIH η ls l ps ms mins σ r = .recr η s₀ ls l ps ms mins is₀ r := by
  subst h; subst ht
  have : fd.instantiatedIndices ls σ = is₀ := funext fun i => absurd i.isLt (by omega)
  simp! [Metalean.RecField.iotaIH, Metalean.RecField.instantiatedTelescope, this]

/-- A successful `mapM` over a list gives, entry by entry, the images. -/
theorem mapM_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      r.length = l.length ∧ ∀ (i : Nat) x, l[i]? = some x → ∃ y, r[i]? = some y ∧ f x = some y
  | [], r, h => by simp at h; subst h; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hall⟩ := mapM_get hys
    refine ⟨by simp [hl], fun i z hz => ?_⟩
    cases i with
    | zero => simp at hz; subst hz; exact ⟨y, rfl, hy⟩
    | succ i => obtain ⟨w, hw, hf⟩ := hall i z (by simpa using hz); exact ⟨w, by simpa using hw, hf⟩

/-- A saturated recursor of a single inductive without indices whose recursive fields take no
arguments, applied to parameters, motives, minors `mvs` and a constructor value of its inductive,
reduces to the translation of the constructor's minor applied to the fields and to the induction
hypotheses `T.rec ps ms mvs f` of the recursive fields (`rfs`, as `recShape` lists them): by ι
(`WHRed.iota`) and β through `wrapCase` (`ctorSat_iota`); Metalean's induction hypotheses
(`iotaIHs`) are the translations of the Lean ones. -/
theorem recIota_whred {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {lps : List Name} {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal}
    {cvs : List ConstructorVal} {motives : List (List Name)} {minors : List RecMinor}
    {mj : Expr} {k : Nat} {mi : RecMinor} {mk : Expr} {us : List Level}
    {ps ms mvs fs rfs : List Expr} {t : Metalean.Expr ζ lps.length 0}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hps : ps.length = rv.numParams) (hms : ms.length = rv.numMotives)
    (hmvs : mvs.length = rv.numMinors)
    (hcv : CtorValue σ T mj k fs) (hmi : minors[k]? = some mi) (hmk : mvs[k]? = some mk)
    (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs)
    (he : TrM E B lps .nil [] (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [mj]).toArray) t) :
    ∃ (a₁ : Metalean.Expr ζ lps.length 0) (fs₀ ihs₀ : List (Metalean.Expr ζ lps.length 0)),
      TrM E B lps .nil [] mk a₁ ∧ List.Forall₂ (TrM E B lps .nil []) fs fs₀ ∧
      List.Forall₂ (TrM E B lps .nil [])
        (rfs.map fun f => mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) ihs₀ ∧
      E ⊢ t ⤳* a₁.appList (fs₀ ++ ihs₀) := by
  obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, rfl, rfl, hTs, hBT, hBc, hns, rfl⟩ :=
    rec_block henv hsub hcr hall hcT hblk
  obtain ⟨⟨_, _, _, _, hIB⟩, -, -, -, -, hctorB⟩ := hb
  obtain ⟨-, -, -, -, -, -, hRnp, hRnm, hRmin, hRni⟩ := hIB.recr s
  have hs0 : s.val = 0 := by have := s.isLt; omega
  have hsum : (List.ofFn fun t => ι.nctors t).sum = ι.nctors s := by
    rw [ofFn_single hns s]; simp
  have hnis : ι.nindices s = 0 := by rw [← hRni, hni]
  have hlen : (ps ++ ms ++ mvs ++ [mj]).length = ι.recrEnd s := by
    show _ = ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1
    simp only [List.length_append, List.length_singleton, hps, hms, hmvs, hRnp, hRnm, hRmin,
      CasesWhred.fin_sum_eq, hnis]
  obtain ⟨ls, l, mo, A, mins, hA, hmo, hw, rfl, us', hRL, hTL⟩ :=
    CasesWhred.trM_recr_inv hBc hlen he
  have hpre : (ps ++ ms ++ mvs).length = ι.recrEnd s - 1 := by
    simp only [List.length_append, List.length_singleton] at hlen ⊢; omega
  -- the major: a constructor node
  obtain ⟨a₀, ha₀, htr₀⟩ := hA (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve
  have hlast : ((Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve).val =
      ι.recrEnd s - 1 := rfl
  rw [hlast, ← hpre, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at ha₀
  cases ha₀
  obtain ⟨k', order, ls₂, ps₂, fds, recFds, fsT, C, hk', -, hBC, hmoC, hmaj, hlT, hfsT, hperm⟩ :=
    major_ctor henv hsub hBT hcv htr₀
  obtain rfl := hctorB _ _ _ _ hBC
  have hmok : mo s k' = orders s k' := by
    have := hmo s k'
    simp only [List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.bind_some] at this
    exact (Option.some.inj this).symm
  -- the minor of the constructor
  obtain ⟨a₁, ha₁, htr₁⟩ := hA (Metalean.IndSig.RecrBinder.case (s := s) s k').resolve
  have hpos₁ : ((Metalean.IndSig.RecrBinder.case (s := s) s k').resolve).val =
      ps.length + ms.length + k := by
    simp only [Metalean.IndSig.RecrBinder.resolve, Fin.val_castSucc, Fin.val_castAdd,
      Fin.val_natAdd, CasesWhred.encodeSigma_val, Metalean.IndSig.motivesEnd]
    rw [hps, hms, hRnp, hRnm, hs0, List.take_zero, List.sum_nil, hk']
    omega
  have hkm : k < mvs.length := (List.getElem?_eq_some_iff.mp hmk).1
  rw [hpos₁, List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by simp), List.length_append,
    show ps.length + ms.length + k - (ps.length + ms.length) = k by omega, hmk] at ha₁
  cases ha₁
  -- ι, then β through `wrapCase`
  have hw' := hw s k'
  rw [hmok] at hw'
  have hstep : E ⊢ Metalean.Expr.recr η s ls l
      (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
      (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve)
      (A (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve) ⤳
      (E.get η).block.iotaRhs η ls l
        (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
        (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins s k' fds recFds := by
    rw [hmaj]; exact WHRed.iota
  rw [Metalean.Inductive.iotaRhs] at hstep
  have hiota := Relation.ReflTransGen.head hstep
    (ctorSat_iota hw' hmoC fsT hlT fds recFds hperm _)
  -- the shape of the minor premise (`IndBlock.recIHs`)
  obtain ⟨motives', mins', hsh', -, hcl⟩ := hIB.recIHs s
  have hinput : (List.ofFn (Cs s)).map (·.numFields) = (List.ofFn fun t => List.ofFn fun c =>
      (ι.ctors t c).nfields + (ι.ctors t c).nrecFields).flatten := by
    rw [ofFn_single hns s, List.flatten_singleton, List.map_ofFn]
    congr 1
    funext c
    exact (hIB.ctor s c).2.2.2.2.2.1
  rw [hinput, hRnp, hRnm, hsh'] at hshape
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape)
  have hcl' := hcl s k'
  simp only [hs0, List.take_zero, List.sum_nil, Nat.zero_add, hk', hmi, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at hcl'
  obtain ⟨-, hcl'⟩ := hcl'
  have hih := hihs mi (List.mem_of_getElem? hmi)
  have hnr : mi.ihs.length = (ι.ctors s k').nrecFields := by
    have := congrArg List.length hcl'
    simpa using this
  obtain ⟨hrl, hrget⟩ := mapM_get hrfs
  -- each recursive field: no binders, into `s`, translated as Metalean's recursive field
  have hfield : ∀ j : Fin (ι.ctors s k').nrecFields,
      (ι.ctors s k').recursiveArity j = 0 ∧ (ι.ctors s k').recursiveTarget j = s ∧
      ∃ rf, rfs[j.val]? = some rf ∧ TrM E B lps .nil [] rf (recFds j) := by
    intro j
    obtain ⟨h, hh⟩ : ∃ h, mi.ihs[j.val]? = some h :=
      ⟨_, List.getElem?_eq_getElem (by rw [hnr]; exact j.isLt)⟩
    have e1 := congrArg (·[j.val]?) hcl'
    simp only [List.getElem?_map, hh, Option.map_some, List.getElem?_ofFn, j.isLt,
      ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at e1
    obtain ⟨-, hfld, har⟩ := e1
    have e2 := congrArg (·[j.val]?) hih
    simp only [List.getElem?_map, hh, Option.map_some, List.getElem?_range', Option.some.injEq,
      Prod.mk.injEq] at e2
    have hjr : j.val < (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).length := by
      simp [hnr]
    have hbin : h.binders = [] := by
      rw [List.getElem?_eq_getElem hjr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e2
      exact e2.2
    refine ⟨by rw [← har, hbin]; rfl, Fin.ext (by have := ((ι.ctors s k').recursiveTarget j).isLt; omega), ?_⟩
    obtain ⟨rf, hrf, hfx⟩ := hrget j.val h hh
    refine ⟨rf, hrf, ?_⟩
    obtain ⟨j', a, h1, h2, h3⟩ := hperm (Fin.natAdd _ j)
    rw [Fin.append_right] at h3
    subst h3
    have hj' : h.field = j' := by
      rw [hfld]; simp only [Fin.val_natAdd] at h1; rw [List.getD_eq_getElem?_getD, h1]; rfl
    subst hj'
    obtain ⟨y, hy, hty⟩ := CasesWhred.forall₂_getElem? hfsT hfx
    rw [h2] at hy
    cases hy
    exact hty
  -- the Lean induction hypotheses translate to the recursor node on the recursive field
  have hIH : ∀ rf x, TrM E B lps .nil [] rf x →
      TrM E B lps .nil [] (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [rf]).toArray)
        (.recr η s ls l (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
          (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve) x) := by
    intro rf x hx
    let A' : Fin (ι.recrEnd s) → Metalean.Expr ζ lps.length 0 := fun i =>
      if i.val = ι.recrEnd s - 1 then x else A i
    have hcs : ∀ i : Fin (ι.casesEnd + ι.nindices s), A' i.castSucc = A i.castSucc := fun i =>
      if_neg (by simp only [Fin.val_castSucc]; show ¬ i.val = ι.casesEnd + ι.nindices s + 1 - 1; omega)
    have hl' : A' (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve = x :=
      if_pos rfl
    have hsat := SatTr.recrSat (E := E) (lps := lps) (us := us) mo A' [] mins hRL hTL hmo
      (fun t c => by
        show Metalean.Frontend.wrapCase _ _ _ (fun p => A' (((p.castAdd _).castAdd _).castAdd _).castSucc)
          (fun t => A' (((t.natAdd _).castAdd _).castAdd _).castSucc) t c (mo t c)
          (A' (((Fin.encodeSigma _ ⟨t, c⟩).natAdd _).castAdd _).castSucc) = _
        simp only [hcs]
        exact hw t c)
    have hnode : Metalean.Expr.appList (Metalean.Expr.recr η s ls l
        (fun p => A' (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
        (fun t => A' (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
        (fun i => A' (Metalean.IndSig.RecrBinder.index i).resolve)
        (A' (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve)) [] =
      .recr η s ls l (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
          (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve) x := by
      rw [hl']
      simp only [Metalean.IndSig.RecrBinder.resolve, hcs]
      rfl
    rw [hnode] at hsat
    refine TrM.special hBc rfl (by simp only [List.length_append, List.length_ofFn,
      List.length_singleton, List.length_nil, Nat.add_zero] at hlen ⊢; omega) ?_ hsat
    intro i a a' ha ha'
    rw [List.append_nil, List.getElem?_ofFn] at ha'
    split at ha'
    · rename_i hi
      cases ha'
      by_cases hil : i = ι.recrEnd s - 1
      · subst hil
        rw [← hpre, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at ha
        cases ha
        simp only [A', ↓reduceIte]
        exact hx
      · have hi' : i < (ps ++ ms ++ mvs).length := by rw [hpre]; omega
        rw [List.getElem?_append_left hi'] at ha
        obtain ⟨a₂, ha₂, htr⟩ := hA ⟨i, hi⟩
        rw [List.getElem?_append_left hi', ha] at ha₂
        cases ha₂
        simp only [A', hil, ↓reduceIte]
        exact htr
    · cases ha'
  let N : Fin (ι.ctors s k').nrecFields → Metalean.Expr ζ lps.length 0 := fun j =>
    .recr η s ls l (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
      (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve) (recFds j)
  have hN : (E.get η).block.iotaIHs η ls l
      (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins s k' fds recFds =
      N := by
    funext j
    obtain ⟨har, htg, -⟩ := hfield j
    exact iotaIH_eq _ har htg hnis _ _ _ _ _ _ _ _ _
  have hIHs : List.Forall₂ (TrM E B lps .nil [])
      (rfs.map fun f => mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) (List.ofFn N) := by
    refine CasesWhred.forall₂_of_getElem? (by simp [hrl, hnr]) fun j x y h1 h2 => ?_
    rw [List.getElem?_ofFn] at h2
    split at h2
    · rename_i hj
      cases h2
      obtain ⟨-, -, rf, hrf, htr⟩ := hfield ⟨j, hj⟩
      rw [List.getElem?_map, hrf, Option.map_some, Option.some.injEq] at h1
      subst h1
      exact hIH rf _ htr
    · cases h2
  refine ⟨_, _, _, htr₁, hfsT, hIHs, hiota.trans ?_⟩
  rw [hN, ← appList_ofFn, ← TrApps.appList_append]

/-- `wrapCase` with the identity field order is the identity. -/
theorem wrapCase_id {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι) (η : Head ζ (.inductive ι))
    {ℓ n : Nat} (ls : Fin ι.nlevels → Metalean.Level ℓ) (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n)
    (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n) (t : Fin ι.nsorts) (c : Fin (ι.nctors t))
    {minor w : Metalean.Expr ζ ℓ n}
    (hw : Metalean.Frontend.wrapCase I η ls ps ms t c
      (List.range ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields)) minor = .ok w) :
    w = minor := by
  unfold Metalean.Frontend.wrapCase at hw
  dsimp only at hw
  rw [ite_eq_left (by simp [Metalean.Frontend.isIdentityOrder])] at hw
  cases hw
  rfl

/-- When the recursive fields of a single inductive come last in each constructor (the shape of
the source ι, `SrcEval.recIota`), Metalean's field orders are the identity: by `IndBlock.recIHs` the
`k`-th recursive field is at the order's position `nfields + k`, and the order lists the ordinary
fields first, in increasing Lean order (`MetaOrderOK`). -/
theorem orders_identity {ζ₀ : Metalean.Sigs} {E₀ : Metalean.Env ζ₀} {B₀ : Binds ζ₀}
    {ι : Metalean.IndSig} {η₀ : Head ζ₀ (.inductive ι)} {lps : List Name}
    {Is : Fin ι.nsorts → InductiveVal} {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal}
    {Rs : Fin ι.nsorts → RecursorVal} {orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat}
    (hIB : IndBlock E₀ B₀ η₀ lps Is Cs Rs orders) (s : Fin ι.nsorts) (hns : ι.nsorts = 1)
    {motives : List (List Name)} {minors : List RecMinor}
    (hshape : recShape (Rs s).numParams (Rs s).numMotives (Rs s).type
      ((List.ofFn (Cs s)).map (·.numFields)) = some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (c : Fin (ι.nctors s)) :
    orders s c = List.range ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) := by
  obtain ⟨-, -, -, -, -, -, hRnp, hRnm, -, -⟩ := hIB.recr s
  obtain ⟨motives', mins', hsh', -, hcl⟩ := hIB.recIHs s
  have hinput : (List.ofFn (Cs s)).map (·.numFields) = (List.ofFn fun t => List.ofFn fun c =>
      (ι.ctors t c).nfields + (ι.ctors t c).nrecFields).flatten := by
    rw [ofFn_single hns s, List.flatten_singleton, List.map_ofFn]
    congr 1
    funext c
    exact (hIB.ctor s c).2.2.2.2.2.1
  rw [hinput, hRnp, hRnm, hsh'] at hshape
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape)
  have hs0 : s.val = 0 := by have := s.isLt; omega
  have hcl' := hcl s c
  simp only [hs0, List.take_zero, List.sum_nil, Nat.zero_add] at hcl'
  obtain ⟨mi, hmi, hmap⟩ := Option.map_eq_some_iff.1 hcl'
  simp only [Prod.mk.injEq] at hmap
  obtain ⟨hfl, hihl⟩ := hmap
  have hih := hihs mi (List.mem_of_getElem? hmi)
  have hnr : mi.ihs.length = (ι.ctors s c).nrecFields := by
    simpa using congrArg List.length hihl
  have hfj : ∀ j : Fin (ι.ctors s c).nrecFields,
      (orders s c).getD ((ι.ctors s c).nfields + j.val) 0 = (ι.ctors s c).nfields + j.val := by
    intro j
    obtain ⟨h, hh⟩ : ∃ h, mi.ihs[j.val]? = some h :=
      ⟨_, List.getElem?_eq_getElem (by rw [hnr]; exact j.isLt)⟩
    have e1 := congrArg (·[j.val]?) hihl
    simp only [List.getElem?_map, hh, Option.map_some, List.getElem?_ofFn, j.isLt,
      ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at e1
    have e2 := congrArg (·[j.val]?) hih
    have hjr : j.val < (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).length := by
      simp [hnr]
    simp only [List.getElem?_map, hh, Option.map_some] at e2
    rw [List.getElem?_eq_getElem hjr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e2
    rw [← e1.2.1, e2.1, List.getElem_range', hfl, hnr]
    omega
  obtain ⟨ords, recs, hord, hol, hrl, hop, -, hperm⟩ := (hIB.ctor s c).2.2.2.2.2.2.2
  have hrecs : recs = List.range' (ι.ctors s c).nfields (ι.ctors s c).nrecFields := by
    refine List.ext_getElem (by simp [hrl]) fun j h1 h2 => ?_
    have := hfj ⟨j, by omega⟩
    rw [hord, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hol,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem h1] at this
    simpa using this
  have hrange : List.range ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) =
      List.range (ι.ctors s c).nfields ++
        List.range' (ι.ctors s c).nfields (ι.ctors s c).nrecFields := by
    rw [List.range'_eq_map_range, List.range_add]
  have hords : ords = List.range (ι.ctors s c).nfields := by
    have hp := hperm
    rw [hord, hrecs, hrange] at hp
    exact List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd (h1.trans h2) (Nat.lt_irrefl _))
      hop List.pairwise_lt_range ((List.perm_append_right_iff _).1 hp)
  rw [hord, hords, hrecs, ← hrange]

/-- The arguments of a typed image of a recursor whose field orders are the identity are typed:
the minors are then not wrapped. -/
theorem satTr_recr_typed {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {ι : Metalean.IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {os : List (List (List Nat))} {us : List Level} {bs' : List (Metalean.Expr ζ lps.length n)}
    {t T : Metalean.Expr ζ lps.length n} (hE : Metalean.EnvWF E) (hΓ : E[Γ] ⊢ ok)
    (hsat : SatTr E lps (.recr η s os) us bs' t) (ht : E[Γ] ⊢ t : T)
    (hid : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) mo, (os[t.val]?.bind (·[c.val]?)) = some mo →
      mo = List.range ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields)) :
    ∀ a ∈ bs', ∃ A, E[Γ] ⊢ a : A := by
  cases hsat with
  | recrEta => exact (InstPre.appList_inv ht).2
  | recrSat mo A rest mins hRL hls hmo hw =>
    obtain ⟨⟨F, hF⟩, hrest⟩ := InstPre.appList_inv ht
    obtain ⟨-, hps, hms, hmins, his, hmaj⟩ := Metalean.Defeq.recr_typed hE hΓ hF
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      obtain ⟨b, rfl⟩ := Metalean.IndSig.RecrBinder.resolve_surjective i
      cases b with
      | param p => exact ⟨_, hps p⟩
      | motive t => exact ⟨_, hms t⟩
      | case t c =>
        have hw' := hw t c
        rw [hid t c _ (hmo t c)] at hw'
        rw [← wrapCase_id _ _ _ _ _ _ _ hw']
        exact ⟨_, hmins t c⟩
      | index i => exact ⟨_, his i⟩
      | major => exact ⟨_, hmaj⟩
    · exact hrest a ha

/-- An application whose head is a recursor spine with at least its arity of arguments translates
to the application of the translations (`saturate`, `ML Frontend/Translate.lean:226`, applies the
node to the arguments beyond the arity). -/
theorem TrM.wf_app_recr {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {c : Name} {us : List Level} {bs : List Lean.Expr} {a : Lean.Expr}
    {ι : Metalean.IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {os : List (List (List Nat))} {t T : Metalean.Expr ζ lps.length n}
    (hb : B c = some (.recr η s os)) (hk : ι.recrEnd s ≤ bs.length)
    (he : TrM E B lps Γ Δ (.app (mkAppN (.const c us) bs.toArray) a) t) (ht : E[Γ] ⊢ t : T) :
    ∃ f' a', TrM E B lps Γ Δ (mkAppN (.const c us) bs.toArray) f' ∧ TrM E B lps Γ Δ a a' ∧
      t = .app f' a' ∧ (∃ F, E[Γ] ⊢ f' : F) ∧ ∃ A, E[Γ] ⊢ a' : A := by
  have hsnoc : Expr.app (mkAppN (.const c us) bs.toArray) a =
      mkAppN (.const c us) (bs ++ [a]).toArray := by
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl
  rw [hsnoc] at he
  obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hb rfl he
  obtain ⟨bs', a', rfl⟩ : ∃ bs' a', as' = bs' ++ [a'] := by
    rcases as'.eq_nil_or_concat with h | ⟨L, x, h⟩
    · subst h; simp at hlen
    · exact ⟨L, x, by simp [h]⟩
  simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
  have hargs' : ∀ (i : Nat) x x', bs[i]? = some x → bs'[i]? = some x' → TrM E B lps Γ Δ x x' :=
    fun i x x' hx hx' => hargs i x x'
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx)
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx').1]; exact hx')
  have ha : TrM E B lps Γ Δ a a' := hargs bs.length a a' (by simp) (by simp [hlen])
  obtain ⟨f', hsat', rfl⟩ : ∃ f', SatTr E lps (.recr η s os) us bs' f' ∧ t = .app f' a' := by
    have hk' : ι.recrEnd s ≤ bs'.length := hlen ▸ hk
    generalize hl : bs' ++ [a'] = l at hsat
    cases hsat with
    | recrEta _ _ _ _ hlt _ => subst hl; rw [List.length_append, List.length_singleton] at hlt; omega
    | recrSat mo A rest mins hRL hls hmo hw =>
      have hle : (List.ofFn A).length ≤ bs'.length := by simpa using hk'
      obtain ⟨r, hbs, hrest⟩ : ∃ r, bs' = List.ofFn A ++ r ∧ rest = r ++ [a'] := by
        obtain ⟨r, hr⟩ : ∃ r, bs' = List.ofFn A ++ r :=
          ⟨bs'.drop (List.ofFn A).length, by
            have := congrArg (List.take (List.ofFn A).length) hl
            rw [List.take_append_of_le_length hle, List.take_left' rfl] at this
            conv_lhs => rw [← List.take_append_drop (List.ofFn A).length bs', this]⟩
        subst hr
        rw [List.append_assoc] at hl
        exact ⟨r, rfl, (List.append_cancel_left hl).symm⟩
      subst hbs hrest
      exact ⟨_, .recrSat mo A r mins hRL hls hmo hw, by rw [TrApps.appList_append]; rfl⟩
  obtain ⟨_, _, hf', ha', -⟩ := ht.app_inv
  exact ⟨f', a', .special hb rfl hlen hargs' hsat', ha, rfl, ⟨_, hf'⟩, _, ha'⟩

/-- The shape of the recursor of a single inductive without indices (`IndBlock.recIHs`): one motive
binding the major premise only, the minor of each constructor binding its fields, each induction
hypothesis into the only member of the block. -/
theorem rec_minors {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal}
    {cvs : List ConstructorVal} {motives : List (List Name)} {minors : List RecMinor}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors)) :
    (∃ x, motives = [[x]]) ∧ cvs.length = iv.ctors.length ∧ rv.numMinors = cvs.length ∧
      ∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
        mi.fields.length = cv.numFields ∧ mi.ihs.length ≤ mi.fields.length ∧
          ∀ h ∈ mi.ihs, h.member = 0 := by
  have hcvs := (recBlock?_single hall hblk).2
  obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, rfl, rfl, -, -, -, hns, rfl⟩ :=
    rec_block henv hsub hcr hall hcT hblk
  obtain ⟨⟨_, _, _, _, hIB⟩, -⟩ := hb
  obtain ⟨-, -, -, -, -, -, hRnp, hRnm, hRmin, hRni⟩ := hIB.recr s
  have hs0 : s.val = 0 := by have := s.isLt; omega
  have hnis : ι.nindices s = 0 := by rw [← hRni, hni]
  obtain ⟨motives', mins', hsh', hmo, hcl⟩ := hIB.recIHs s
  have hinput : (List.ofFn (Cs s)).map (·.numFields) = (List.ofFn fun t => List.ofFn fun c =>
      (ι.ctors t c).nfields + (ι.ctors t c).nrecFields).flatten := by
    rw [ofFn_single hns s, List.flatten_singleton, List.map_ofFn]
    congr 1
    funext c
    exact (hIB.ctor s c).2.2.2.2.2.1
  rw [hinput, hRnp, hRnm, hsh'] at hshape
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape)
  refine ⟨?_, by rw [(mapM_get hcvs).1], ?_, ?_⟩
  · rw [ofFn_single hns s, hnis] at hmo
    revert hmo
    rcases motives' with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> intro hmo <;> simp at hmo
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hmo
    exact ⟨x, rfl⟩
  · rw [hRmin, List.length_ofFn, ofFn_single hns s]; simp
  · intro i cv hcv
    have hi : i < ι.nctors s := by
      have := (List.getElem?_eq_some_iff.mp hcv).1; simpa using this
    rw [List.getElem?_ofFn] at hcv
    simp only [hi, ↓reduceDIte, Option.some.injEq] at hcv
    subst hcv
    have hcl' := hcl s ⟨i, hi⟩
    simp only [hs0, List.take_zero, List.sum_nil, Nat.zero_add] at hcl'
    obtain ⟨mi, hmi, he⟩ := Option.map_eq_some_iff.1 hcl'
    simp only [Prod.mk.injEq] at he
    refine ⟨mi, hmi, by rw [he.1, (hIB.ctor s ⟨i, hi⟩).2.2.2.2.2.1], ?_, fun h hh => ?_⟩
    · have := congrArg List.length he.2
      simp only [List.length_map, List.length_ofFn] at this
      omega
    have := congrArg (fun l => (h.member, h.field, h.binders.length) ∈ l) he.2
    simp only [List.mem_map, eq_iff_iff] at this
    obtain ⟨k, hk⟩ := List.mem_ofFn.1 (this.1 ⟨h, hh, rfl⟩)
    have := congrArg Prod.fst hk
    simp only at this
    have := ((ι.ctors s ⟨i, hi⟩).recursiveTarget k).isLt
    omega

end RecWhred

end EraseProof
