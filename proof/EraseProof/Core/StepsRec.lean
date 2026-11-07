import EraseProof.Core.StepsQuot
import EraseProof.Simulation.Rec

/-!
# The recursor step on saturated spines

`Steps.visitRec_sat`: `visitRec` (`LeanToLambdaBox/Erasure.lean:971`) on a spine of the recursor
`T.rec` of a single inductive `T` without indices whose induction hypotheses take no arguments and
are about the last fields (the recursors of `SrcEval.recIota`), applied to at least its arity of
arguments, erases the spine by `Erases.recLet`: the minor premises erased and let-bound around the
fixpoint of the block (`RecFixOf`), applied to the erased major premise and to the erased arguments
beyond the arity. The fixpoint's members are those `recMembers` computes, its alternatives those of
`SimRec.recCs`, it is closed under the minors and has no free variable (`recFix_closed`), and its
only `case` reads the registered block of `T` (`deps_recFix`). The subsingleton property of `T`
and the side conditions on the oracle's level of the major premise's type (`casesSortLevel` when it
is never zero, `FieldsErasable` when it may be zero) are premises.

Reference: none in MetaRocq (PCUIC has no recursors); DV-30.
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

namespace Steps

open TravFrame

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- A `mapM` succeeds with a list whose entries are the images of the entries. -/
theorem mapM_of_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, r.length = l.length → (∀ (i : Nat) x, l[i]? = some x → f x = r[i]?) →
      l.mapM f = some r
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l, y :: r, hlen, h => by
    have hx : f x = some y := h 0 x rfl
    have hl : l.mapM f = some r := mapM_of_get (by simpa using hlen) fun i z hz => h (i + 1) z hz
    simp [List.mapM_cons, hx, hl]

/-- `recShape` returns one minor premise per constructor. -/
theorem recShape_length {P M : Nat} {type : Expr} {nfs : List Nat} {motives : List (List Name)}
    {minors : List RecMinor} (h : recShape P M type nfs = some (motives, minors)) :
    minors.length = nfs.length := by
  unfold recShape at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨u, hg, mins, hmins, -, rfl⟩ := h
  have hc : (List.take nfs.length (List.drop (P + M) (piBinders type).1)).length = nfs.length := by
    revert hg
    simp only [guard]
    split
    · rename_i h; intro _; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.2
    · intro h; cases h
  rw [(RecWhred.mapM_get hmins).1]
  simp [List.length_zip, hc]

/-- A `mapM` of lookups that keep the states: the images are those of the lookup. -/
theorem mapM_run_lookup {pc : PureCtx} {tc : TravCtx} {α β : Type} {f : α → EraseT PureM β}
    {g : α → Option β}
    (hf : ∀ x st ps b st' ps', (f x).runPure st tc pc ps = .ok ((b, st'), ps') →
      g x = some b ∧ st' = st ∧ ps' = ps) :
    ∀ (l : List α) {st : ErasureState} {ps : PureState} {bs : List β} {st' : ErasureState}
      {ps' : PureState}, (l.mapM f).runPure st tc pc ps = .ok ((bs, st'), ps') →
      l.mapM g = some bs ∧ st' = st ∧ ps' = ps
  | [], st, ps, bs, st', ps', h => by cases h; exact ⟨rfl, rfl, rfl⟩
  | x :: l, st, ps, bs, st', ps', h => by
    rw [List.mapM_cons, runPure_bind] at h
    obtain ⟨⟨⟨b, st₁⟩, ps₁⟩, h1, h2⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨hg, rfl, rfl⟩ := hf x _ _ _ _ _ h1
    rw [runPure_bind] at h2
    obtain ⟨⟨⟨bs', st₂⟩, ps₂⟩, h3, h4⟩ := OracleWhnf.ok_of_bind h2
    obtain ⟨hgs, rfl, rfl⟩ := mapM_run_lookup hf l h3
    cases h4
    simp [List.mapM_cons, hg, hgs]

/-- `List.mapM (visitExpr j)` at the pure backend, from `visitExpr` at `j` (`ih`): each result
erases its argument, has erased dependencies at the end, and the run grows. Reference: the
`tApp` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), argument by argument. -/
theorem visitExpr_mapM {j : Nat} (ih : ∀ e, ExprSpec E B view cfg decls j e)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {tc : TravCtx} :
    ∀ {args : List Expr} {st st' : ErasureState} {ps ps' : PureState} {ms : List LBTerm},
    CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
    (∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A) →
    StateOK E B (evalEnvOf view cfg decls) st →
    (args.mapM (visitExpr (m := PureM) j)).runPure st tc ⟨decls, view⟩ ps = .ok ((ms, st'), ps') →
    args.length = ms.length ∧
      (∀ (i : Nat) a a', args[i]? = some a → ms[i]? = some a' →
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ a a') ∧
      (∀ a' ∈ ms, ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls a') ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps'
  | [], st, st', ps, ps', ms, _, _, _, hok, hrun => by
    cases hrun
    exact ⟨rfl, by simp, by simp, .refl hok⟩
  | a :: l, st, st', ps, ps', ms, hctx, hsc, hargs, hok, hrun => by
    rw [List.mapM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨ta, st₁⟩, ps₁⟩, ha, hr1⟩ := OracleWhnf.ok_of_bind hrun
    rw [runPure_bind] at hr1
    obtain ⟨⟨⟨tl, st₂⟩, ps₂⟩, hl, hr2⟩ := OracleWhnf.ok_of_bind hr1
    cases hr2
    obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs a (.head _)
    have ⟨hera, hdepsa, hgra⟩ := ih a hctx hsc hoa hma hna hra hok hta ⟨A, hA⟩ ha
    obtain ⟨hlen, hers, hdeps, hgr⟩ := visitExpr_mapM ih (hctx.mono hgra.next) hsc
      (fun b hb => hargs b (.tail _ hb)) hgra.inv hl
    refine ⟨by simp [hlen], fun i b b' h1 h2 => ?_, fun b hb => ?_, hgra.trans hgr⟩
    · cases i with
      | zero => simp at h1 h2; subst h1 h2; exact hera
      | succ i => exact hers i b b' (by simpa using h1) (by simpa using h2)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ErasesDeps.ext hgr.ext hdepsa
      · exact hdeps b hb

/-- `closedn` of a `case` branch list. -/
theorem closednB_iff {k : Nat} : ∀ {bs : List (List BinderName × LBTerm)},
    closednB k bs = true ↔ ∀ b ∈ bs, closedn (k + b.1.length) b.2 = true
  | [] => by simp [closednB]
  | (ns, b) :: bs => by simp [closednB, closednB_iff]

/-- `hasFVar` of a `case` branch list. -/
theorem hasFVarB_iff {x : FVarId} : ∀ {bs : List (List BinderName × LBTerm)},
    hasFVarB x bs = false ↔ ∀ b ∈ bs, hasFVar x b.2 = false
  | [] => by simp [hasFVarB]
  | (ns, b) :: bs => by simp [hasFVarB, hasFVarB_iff]

/-- `closedn` and `hasFVar` under λs. -/
theorem foldr_lambda_closed (k : Nat) (x : FVarId) : ∀ (xs : List BinderName) (b : LBTerm),
    closedn (k + xs.length) b = true → hasFVar x b = false →
      closedn k (xs.foldr .lambda b) = true ∧ hasFVar x (xs.foldr .lambda b) = false
  | [], b, h1, h2 => ⟨h1, h2⟩
  | y :: xs, b, h1, h2 => by
    have := foldr_lambda_closed (k + 1) x xs b (by simpa [Nat.add_assoc, Nat.add_comm 1] using h1) h2
    exact ⟨this.1, this.2⟩

/-- `closedn` and `hasFVar` of an application to `□`s. -/
theorem foldl_box_closed (k : Nat) (x : FVarId) : ∀ (m : Nat) (f : LBTerm),
    closedn k f = true → hasFVar x f = false →
      closedn k ((List.replicate m LBTerm.box).foldl .app f) = true ∧
        hasFVar x ((List.replicate m LBTerm.box).foldl .app f) = false
  | 0, f, h1, h2 => ⟨h1, h2⟩
  | m + 1, f, h1, h2 => by
    rw [List.replicate_succ, List.foldl_cons]
    exact foldl_box_closed k x m (.app f .box) (by simp [closedn, h1]) (by simp [hasFVar, h2])

/-- The fixpoint of a recursor of a single inductive in the simple shape (`RecFix.SimpleAlt`) is
closed under its `N` minors and has no free variable. -/
theorem recFix_closed {N npars : Nat} {direct : Bool} {nm : Name} {x : Name} {indid : InductiveId}
    {minors : List RecMinor} (hN : minors.length = N)
    (hs : ∀ c ∈ SimRec.recCs minors, RecFix.SimpleAlt c) :
    closedn N (recFix N npars direct [⟨nm, [x], indid, SimRec.recCs minors⟩] 0) = true ∧
      ∀ y, hasFVar y (recFix N npars direct [⟨nm, [x], indid, SimRec.recCs minors⟩] 0) = false := by
  rw [RecFix.recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.sub_self,
    List.foldr_cons, List.foldr_nil]
  rw [RecFix.innerS_congr (fun c hc => RecFix.altF_simple N _ rfl (hs c hc))]
  -- every alternative is closed under the fixpoint, the major's λ and its fields
  have halt : ∀ c ∈ SimRec.recCs minors, ∀ y,
      closedn (N + 1 + 1 + ((RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi)))
        (fun B => .bvar (B + 1)) c).1.length)) (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi)))
          (fun B => .bvar (B + 1)) c).2 = true ∧
      hasFVar y (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi)))
          (fun B => .bvar (B + 1)) c).2 = false := by
    intro c hc y
    have hgi := SimRec.recCs_fst hc
    obtain ⟨gi, mi, mask⟩ := c
    obtain ⟨-, hih⟩ := hs _ hc
    simp only [RecFix.altG, RecFix.length_altNames, RecFix.recAltS]
    refine ⟨RecLam.closedn_mkApps.2 ⟨by simp [closedn]; omega, fun a ha => ?_⟩, ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
        have := List.mem_range.1 hf
        simp [closedn]; omega
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 ha
        have := (hih h hh).2.2
        simp [closedn]; omega
    · cases hf : hasFVar y (mkApps (.bvar (mi.fields.length + 2 + (N - 1 - gi)))
        ((List.range mi.fields.length).map (fun f => .bvar (mi.fields.length - 1 - f)) ++
          mi.ihs.map fun h => .app (.bvar (mi.fields.length + 1))
            (.bvar (mi.fields.length - 1 - h.field)))) with
      | false => rfl
      | true =>
        rcases RecLam.hasFVar_mkApps hf with h | ⟨a, ha, h⟩
        · simp [hasFVar] at h
        · rcases List.mem_append.1 ha with ha | ha
          · obtain ⟨f, -, rfl⟩ := List.mem_map.1 ha; simp [hasFVar] at h
          · obtain ⟨h', -, rfl⟩ := List.mem_map.1 ha; simp [hasFVar] at h
  have hinner : ∀ y, closedn (N + 1 + 1) (RecFix.innerS direct indid npars (SimRec.recCs minors)
      (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi))) (fun B => .bvar (B + 1)))) = true ∧
      hasFVar y (RecFix.innerS direct indid npars (SimRec.recCs minors)
      (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi))) (fun B => .bvar (B + 1)))) = false := by
    intro y
    unfold RecFix.innerS
    split
    · rename_i c hcs
      have hc : c ∈ SimRec.recCs minors := by rw [hcs]; exact .head _
      obtain ⟨h1, h2⟩ := halt c hc y
      obtain ⟨h3, h4⟩ := foldr_lambda_closed (N + 1 + 1) y _ _ h1 h2
      exact foldl_box_closed _ y _ _ h3 h4
    · refine ⟨?_, ?_⟩
      · simp only [closedn, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨by omega, closednB_iff.2 fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact (halt c hc y).1
      · simp only [hasFVar, Bool.or_eq_false_iff]
        refine ⟨trivial, hasFVarB_iff.2 fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact (halt c hc y).2
  refine ⟨?_, fun y => ?_⟩
  · simp [closedn, closednD, (hinner (default : FVarId)).1]
  · simp [hasFVar, hasFVarD, (hinner y).2]

/-- The fixpoint of a recursor of a single inductive in the simple shape has erased dependencies
when its inductive's block has (its `case` is the only node that reads the λ□ environment). -/
theorem deps_recFix {σ : EvalEnv} {lenv : GlobalDeclarations} {N npars : Nat} {direct : Bool}
    {nm x T : Name} {indid : InductiveId} {minors : List RecMinor}
    (hs : ∀ c ∈ SimRec.recCs minors, RecFix.SimpleAlt c) (hid : IndIdOf σ T = some indid)
    (hind : ErasesInd E B σ lenv T) :
    ErasesDeps E B σ lenv (recFix N npars direct [⟨nm, [x], indid, SimRec.recCs minors⟩] 0) := by
  rw [RecFix.recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.sub_self,
    List.foldr_cons, List.foldr_nil]
  rw [RecFix.innerS_congr (fun c hc => RecFix.altF_simple N _ rfl (hs c hc))]
  have halt : ∀ c, ErasesDeps E B σ lenv (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi)))
      (fun B => .bvar (B + 1)) c).2 := by
    rintro ⟨gi, mi, mask⟩
    simp only [RecFix.altG, RecFix.recAltS]
    refine ErasesDeps.mkApps_iff.2 ⟨.bvar, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨f, -, rfl⟩ := List.mem_map.1 ha; exact .bvar
    · obtain ⟨h, -, rfl⟩ := List.mem_map.1 ha; exact .app .bvar .bvar
  refine .fix fun d hd => ?_
  obtain rfl := List.mem_singleton.1 hd
  refine .lambda ?_
  unfold RecFix.innerS
  split
  · rename_i c _
    rw [RecEval.foldl_app_eq_mkApps]
    refine ErasesDeps.mkApps_iff.2 ⟨?_, fun a ha => by rw [(List.mem_replicate.1 ha).2]; exact .box⟩
    have : ∀ (xs : List BinderName) (b : LBTerm), ErasesDeps E B σ lenv b →
        ErasesDeps E B σ lenv (xs.foldr .lambda b) := by
      intro xs; induction xs with
      | nil => exact fun _ h => h
      | cons y ys ih => exact fun b h => .lambda (ih b h)
    exact this _ _ (halt c)
  · exact .case hid hind .bvar fun br hbr => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hbr
      exact halt c

/-- `withAppEtaToMinArity` on a spine with at least the arity of arguments runs the continuation
on the head and the arguments (`LeanToLambdaBox/Erasure.lean:646`), once the spine's type is
inferred. -/
theorem withAppEta_sat {pc : PureCtx} {ar f : Nat} {c : Name} {us : List Level} {e : Expr}
    {kont : Expr → Array Expr → EraseT PureM LBTerm} (hfn : e.getAppFn = .const c us)
    (hsat : ar ≤ (spineArgs e).length) {st : ErasureState} {tc : TravCtx} {ps : PureState}
    {res : (LBTerm × ErasureState) × PureState}
    (h : (withAppEtaToMinArity (m := PureM) f e ar kont).runPure st tc pc ps = .ok res) :
    (kont (.const c us) (spineArgs e).toArray).runPure st tc pc ps = .ok res := by
  have hA : (e.withApp fun _ as => as) = (spineArgs e).toArray := by
    rw [← withApp_toList e, Array.toArray_toList]
  rw [withAppEtaToMinArity, runPure_read_bind, runPure_read_bind, runPure_bind,
    inferType_runPure] at h
  rcases hinf : Pure.inferType ⟨pc.decls⟩ oracleFuel tc.locals [] e with err | T
  · rw [hinf] at h; cases h
  rw [hinf, show Except.map (fun T => ((T, st), ps)) (Except.ok T : Except EraseError Expr) =
    Except.ok ((T, st), ps) from rfl, ok_bind'] at h
  dsimp only at h
  rw [withApp_eq, hfn, hA] at h
  cases f with
  | zero => rw [withAppEtaToMinArity.go] at h; cases h
  | succ f =>
  rw [withAppEtaToMinArity.go] at h
  simp only [show (spineArgs e).toArray.size ≥ ar by simp; omega, ↓reduceIte] at h
  exact h

/-- `visitRec` at the pure backend on a spine `c.{us} as` of the recursor `rv = T.rec` of a single
inductive `iv` without indices whose induction hypotheses take no arguments and are about the last
fields (`hihs`), which the traversal does not keep as a constant (`hnsc`), with at least its arity
of arguments, from `visitExpr` at the fuels up to `fuel` (`ih`): a successful run erases the spine
by `Erases.recLet`, with erased dependencies, grows, and returns a closed term, given that `T` is a
subsingleton (`hss`) and, for the oracle's level `u` of the major premise's type, that the
inductive's sort at the spine's levels is never zero when `u` is, and that the fields of a
one-constructor `iv` are erasable when `u` may be zero (`hdir`). Reference: `visitRec`
(`LeanToLambdaBox/Erasure.lean:971`); DV-30. -/
theorem visitRec_sat (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {c : Name} {us : List Level} {rv : RecursorVal}
    {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    (hcr : findDecl decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : (evalEnvOf view cfg decls).recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hihs : ∀ motives minors, recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors) → ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
        (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hnsc : recStaysConstant cfg.nat rv [iv] cvs = false) (hss : Subsingleton E B T)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {e : Expr} (hfn : e.getAppFn = .const c us)
    (hdir : ∀ m u, (spineArgs e)[rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices]? =
      some m →
      Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals m = .ok u →
      (u.isNeverZero = true → ∃ l, casesSortLevel iv us = some l ∧ l.isNeverZero = true) ∧
      (u.isNeverZero = false → iv.ctors.length = 1 → FieldsErasable E B iv.name))
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ spineArgs e, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hsat : rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 ≤ (spineArgs e).length)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hrun : (visitRec (m := PureM) fuel rv e).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ closedn 0 r = true := by
  cases fuel with
  | zero => rw [visitRec] at hrun; cases hrun
  | succ fuel =>
  rw [visitRec, runPure_bind] at hrun
  obtain ⟨⟨⟨ivs, st₁⟩, ps₁⟩, hivs0, hr1⟩ := OracleWhnf.ok_of_bind hrun
  obtain ⟨hivs, rfl, rfl⟩ := mapM_run_lookup (g := (evalEnvOf view cfg decls).indOf?)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      simp only [EvalEnv.indOf?, evalEnvOf]
      rw [show findDecl decls x = _ from hci]) _ hivs0
  dsimp only at hr1
  rw [runPure_bind] at hr1
  obtain ⟨⟨⟨cvs', st₂⟩, ps₂⟩, hcvs0, hr2⟩ := OracleWhnf.ok_of_bind hr1
  obtain ⟨hcvs, rfl, rfl⟩ := mapM_run_lookup (g := (evalEnvOf view cfg decls).ctorOf?)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      simp only [EvalEnv.ctorOf?, evalEnvOf]
      rw [show findDecl decls x = _ from hci]) _ hcvs0
  dsimp only at hr2
  have hblk' : (evalEnvOf view cfg decls).recBlock? rv = some (ivs, cvs') := by
    unfold EvalEnv.recBlock?
    rw [hivs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [hcvs]
    rfl
  rw [hblk] at hblk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hblk')
  rw [runPure_read_bind, hctx.config, hnsc] at hr2
  simp only [Bool.false_eq_true, ↓reduceIte] at hr2
  cases hsh : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) with
  | none => rw [hsh] at hr2; cases hr2
  | some mm =>
  obtain ⟨motives, minors⟩ := mm
  rw [hsh] at hr2
  dsimp only at hr2
  obtain ⟨⟨x, rfl⟩, hcl, hmc, hmin⟩ := RecWhred.rec_minors (σ := evalEnvOf view cfg decls)
    hG.prog hG.sub hcr hall hcT hblk hni hsh
  have hTn : iv.name = T := by
    have := RecWhred.rec_block (σ := evalEnvOf view cfg decls) hG.prog hG.sub hcr hall hcT hblk
    obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, hrv', hiv', hT', -⟩ := this
    rw [hiv', hT']
  have hivT : findDecl decls iv.name = some (.inductInfo iv) :=
    hTn ▸ (RecWhred.recBlock?_single hall hblk).1
  rw [runPure_bind] at hr2
  obtain ⟨⟨⟨s3, st₃⟩, ps₃⟩, hloop, hr3⟩ := OracleWhnf.ok_of_bind hr2
  rw [List.forIn_cons, runPure_bind] at hloop
  obtain ⟨⟨⟨y, st₄⟩, ps₄⟩, hreg0, hloop2⟩ := OracleWhnf.ok_of_bind hloop
  simp only [Std.toStream, Std.Stream.next?] at hreg0
  rw [runPure_bind] at hreg0
  obtain ⟨⟨⟨⟨indid, masks⟩, st₅⟩, ps₅⟩, hreg, hy⟩ := OracleWhnf.ok_of_bind hreg0
  cases hy
  dsimp only at hloop2
  cases hloop2
  dsimp only at hr3
  obtain ⟨hok₅, hext₅, hcon₅, hid, hmasks⟩ := register_inductive_ok hG.prog hG.wf hG.sub hok rfl
    (hctx.config ▸ hG.irr iv ⟨_, (findDecl_eq_some hivT).1, rfl⟩) (hctx.config ▸ hG.phase) hG.bn
    hivT hreg
  rw [runPure_bind] at hr3
  obtain ⟨⟨⟨j, st₆⟩, ps₆⟩, hj0, hr4⟩ := OracleWhnf.ok_of_bind hr3
  obtain ⟨hj, rfl, rfl⟩ := getOrFail_run hj0
  rw [hall, List.idxOf?_eq_some_iff] at hj
  obtain ⟨hj1, hj2, -⟩ := hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj1
  subst hj1
  have hmaj : rv.getMajorInduct = T := hj2.symm
  dsimp only at hr4
  have hr5 := withAppEta_sat hfn hsat hr4
  beta_reduce at hr5
  have hps₆ : ps₆ = ps₂ := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
  subst hps₆
  have hgr₅ : Grows E B (evalEnvOf view cfg decls) S st₂ st₆ ps₆ ps₆ :=
    ⟨hok₅, hext₅, Nat.le_refl _, fun c kn h h' => by rw [hcon₅, h] at h'; cases h'⟩
  -- the major premise
  rw [runPure_bind] at hr5
  obtain ⟨⟨⟨mj, st₇⟩, ps₇⟩, hm0, hr6⟩ := OracleWhnf.ok_of_bind hr5
  obtain ⟨hmj, rfl, rfl⟩ := getOrFail_run hm0
  dsimp only at hr6
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run] at hr6
  rcases hTL : Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals mj with err | u
  · rw [hTL] at hr6; cases hr6
  rw [hTL] at hr6
  dsimp only [Except.map] at hr6
  rw [ok_bind', ok_bind'] at hr6
  dsimp only at hr6
  -- the arguments
  have hsub : ∀ l : List Expr, (∀ a ∈ l, a ∈ spineArgs e) → ∀ a ∈ l,
      (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧ NatPlain cfg a ∧ RecFree decls a ∧
        ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A := fun l hl a ha => hargs a (hl a ha)
  -- the minor premises
  rw [runPure_bind] at hr6
  obtain ⟨⟨⟨ms, st₈⟩, ps₈⟩, hms, hr7⟩ := OracleWhnf.ok_of_bind hr6
  rw [show ((spineArgs e).toArray.extract (rv.numParams + rv.numMotives)
      (rv.numParams + rv.numMotives + rv.numMinors)).toList =
      ((spineArgs e).drop (rv.numParams + rv.numMotives)).take rv.numMinors by simp] at hms
  have hmsub : ∀ a ∈ ((spineArgs e).drop (rv.numParams + rv.numMotives)).take rv.numMinors,
      a ∈ spineArgs e := fun a ha => List.mem_of_mem_drop (List.mem_of_mem_take ha)
  obtain ⟨hlenm, hersm, hdepsm, hgrm⟩ := visitExpr_mapM (fun e => ih.expr fuel (by omega) e)
    hctx hsc (hsub _ hmsub) hok₅ hms
  dsimp only at hr7
  rw [runPure_bind] at hr7
  obtain ⟨⟨⟨app, st₉⟩, ps₉⟩, happ, hr8⟩ := OracleWhnf.ok_of_bind hr7
  cases fuel with
  | zero => rw [visitAppArgs] at happ; cases happ
  | succ j =>
  rw [show (spineArgs e).toArray.extract (rv.numParams + rv.numMotives + rv.numMinors)
      (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
      (((spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors)).take
        (rv.numIndices + 1)).toArray by simp; congr 1; omega] at happ
  have hisub : ∀ a ∈ ((spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors)).take
      (rv.numIndices + 1), a ∈ spineArgs e := fun a ha => List.mem_of_mem_drop (List.mem_of_mem_take ha)
  obtain ⟨as', rfl, hlena, hersa, hdepsa, hgra⟩ := visitAppArgs_list
    (fun e => ih.expr j (by omega) e) (hctx.mono (hgr₅.trans hgrm).next) hsc (hsub _ hisub)
    hgrm.inv happ
  dsimp only at hr8
  rw [show (spineArgs e).toArray.extract
      (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
      ((spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)).toArray
      by simp] at hr8
  have hxsub : ∀ a ∈ (spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors +
      rv.numIndices + 1), a ∈ spineArgs e := fun a ha => List.mem_of_mem_drop ha
  obtain ⟨ex', rfl, hlenx, hersx, hdepsx, hgrx⟩ := visitAppArgs_list
    (fun e => ih.expr j (by omega) e) (hctx.mono ((hgr₅.trans hgrm).trans hgra).next) hsc
    (hsub _ hxsub) hgra.inv hr8
  -- the shapes
  have hlenmin : minors.length = rv.numMinors := by
    rw [recShape_length hsh, List.length_map, hmc]
  have hlenmi : minors.length = iv.ctors.length := by omega
  have hA := hsat
  have hmj' : (spineArgs e)[rv.numParams + rv.numMotives + rv.numMinors]? = some mj := by
    simpa [hni] using hmj
  obtain ⟨hd1, hd2⟩ := hdir mj u (by simpa [hni] using hmj') hTL
  -- the alternatives of the fixpoint are those of `SimRec.recCs`
  have hmk : ∀ ci, ci < minors.length →
      masks.getD ci #[] = Array.replicate (minors.getD ci default).fields.length .keep := by
    intro ci hci
    obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors[ci]? = some cn := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hcvs₁ := (RecWhred.recBlock?_single hall hblk).2
    obtain ⟨-, hcget⟩ := RecWhred.mapM_get hcvs₁
    obtain ⟨cv, hcv, hcvd⟩ := hcget ci cn hcn
    obtain ⟨mi, hmi, hmf, -⟩ := hmin ci cv hcv
    have hfd : findDecl decls cn = some (.ctorInfo cv) := by
      unfold EvalEnv.ctorOf? at hcvd
      split at hcvd
      · rename_i cv' hcv'; cases hcvd; exact hcv'
      · cases hcvd
    rw [List.getD_eq_getElem?_getD, hmasks.2 ci cn cv hcn hfd, List.getD_eq_getElem?_getD, hmi]
    simp [hmf]
  have hcs : (List.range (List.take iv.ctors.length (List.drop 0 minors)).length).map (fun c =>
      (0 + c, (List.take iv.ctors.length (List.drop 0 minors)).getD c default, List.getD masks c #[])) =
      SimRec.recCs minors := by
    unfold SimRec.recCs
    rw [List.drop_zero, ← hlenmi, List.take_length]
    refine List.map_congr_left fun ci hci => ?_
    simp only [Nat.zero_add, Prod.mk.injEq, true_and]
    exact hmk ci (List.mem_range.1 hci)
  have hsimple : ∀ c ∈ SimRec.recCs minors, RecFix.SimpleAlt c := by
    intro c hc
    unfold SimRec.recCs at hc
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
    have hci' := List.mem_range.1 hci
    obtain ⟨cv, hcv⟩ : ∃ cv, cvs[ci]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by rw [hcl]; omega)⟩
    obtain ⟨mi, hmi, -, hle, hmem0⟩ := hmin ci cv hcv
    rw [List.getD_eq_getElem?_getD, hmi, Option.getD_some]
    simp only [RecFix.SimpleAlt]
    have hih := hihs _ _ hsh mi (List.mem_of_getElem? hmi)
    refine ⟨trivial, fun h hh => ⟨?_, hmem0 h hh, ?_⟩⟩
    · have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [hih] at hm
      obtain ⟨f, -, hf⟩ := List.mem_map.1 hm
      exact (Prod.mk.inj hf).2.symm
    · have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [hih] at hm
      obtain ⟨f, hf, hf'⟩ := List.mem_map.1 hm
      rw [List.mem_range'_1] at hf
      have := (Prod.mk.inj hf').1
      omega
  have hmasks' : iv.ctors.mapM (fun c => (ctorFields (evalEnvOf view cfg decls) c).map fun k =>
      (Array.replicate k .keep : ConstructorArgMask)) = some masks := by
    refine mapM_of_get hmasks.1 fun ci cn hcn => ?_
    have hcvs₁ := (RecWhred.recBlock?_single hall hblk).2
    obtain ⟨-, hcget⟩ := RecWhred.mapM_get hcvs₁
    obtain ⟨cv, hcv, hcvd⟩ := hcget ci cn hcn
    have hfd : findDecl decls cn = some (.ctorInfo cv) := by
      unfold EvalEnv.ctorOf? at hcvd
      split at hcvd
      · rename_i cv' hcv'; cases hcvd; exact hcv'
      · cases hcvd
    rw [hmasks.2 ci cn cv hcn hfd]
    simp [ctorFields, evalEnvOf, hfd]
  have hrm : recMembers (evalEnvOf view cfg decls) minors 0 [iv] [[x]] = some
      [⟨iv.name, [x], indid, SimRec.recCs minors⟩] := by
    rw [← hcs]
    simp [recMembers, hid, hmasks']
  rw [hcs] at *
  have hmemb : Array.toList (Array.push #[]
      (⟨iv.name, [x], indid, SimRec.recCs minors⟩ : RecMember)) =
      [⟨iv.name, [x], indid, SimRec.recCs minors⟩] := rfl
  rw [hmemb]
  -- the fixpoint
  have hcF := recFix_closed (npars := rv.numParams) (direct := !u.isNeverZero) (nm := iv.name)
    (x := x) (indid := indid) hlenmin hsimple
  have hRF : RecFixOf E B (evalEnvOf view cfg decls) rv us minors
      (recFix rv.numMinors rv.numParams (!u.isNeverZero)
        [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) :=
    ⟨[iv], cvs, [[x]], _, T, iv, 0, !u.isNeverZero, hblk, hsh, hlenmin, hrm, hmaj, hTn ▸ hivT,
      by rw [hall]; simp [List.idxOf?, List.findIdx?, List.findIdx?.go],
      fun h => hd1 (by simpa using h),
      fun h iv' hiv' h1 => by
        obtain rfl := List.mem_singleton.1 hiv'
        exact hd2 (by simpa using h) h1,
      fun t ht => by rw [hall] at ht; obtain rfl := List.mem_singleton.1 ht; exact hss,
      rfl, hcF.1, hcF.2⟩
  -- the major premise and the arguments
  have hdrop : (spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors) =
      mj :: (spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors + 1) := by
    rw [List.drop_eq_getElem_cons (by omega)]
    rw [List.getElem?_eq_getElem (by omega)] at hmj'
    cases hmj'
    rfl
  obtain ⟨a', rfl⟩ : ∃ a', as' = [a'] := by
    rw [hni, hdrop] at hlena
    simp only [List.take_succ_cons, List.take_zero, List.length_singleton] at hlena
    match as', hlena with
    | [a'], _ => exact ⟨a', rfl⟩
  have hera : Erases E B lps (evalEnvOf view cfg decls) Γ Δ mj a' :=
    hersa 0 mj a' (by rw [hni, hdrop]; rfl) rfl
  have hsp : mkAppN (.const c us) (spineArgs e).toArray = e := by
    rw [← hfn]; exact mkAppN_spine e
  have hdec : spineArgs e = (spineArgs e).take rv.numParams ++
      ((spineArgs e).drop rv.numParams).take rv.numMotives ++
      ((spineArgs e).drop (rv.numParams + rv.numMotives)).take rv.numMinors ++ [] ++ [mj] ++
      (spineArgs e).drop (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) := by
    rw [hni, Nat.add_zero]
    conv_lhs => rw [← List.take_append_drop rv.numParams (spineArgs e),
      ← List.take_append_drop rv.numMotives ((spineArgs e).drop rv.numParams), List.drop_drop,
      ← List.take_append_drop rv.numMinors ((spineArgs e).drop (rv.numParams + rv.numMotives)),
      List.drop_drop, hdrop]
    simp [List.append_assoc]
  -- the closedness of the erasures
  have hclm : ∀ m ∈ ms, closedn 0 m = true := by
    intro m hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
    have hi' : i < (((spineArgs e).drop (rv.numParams + rv.numMotives)).take rv.numMinors).length := by
      rw [hlenm]; exact (List.getElem?_eq_some_iff.1 hi).1
    exact closed_of_arg hctx hargs (hmsub _ (List.getElem_mem hi'))
      (hersm i _ _ (List.getElem?_eq_getElem hi') hi)
  have hcla : closedn 0 a' = true :=
    closed_of_arg hctx hargs (List.mem_of_getElem? hmj') hera
  have hclx := closed_of_args (hctx.mono (((hgr₅.trans hgrm).trans hgra)).next) hargs hxsub hlenx hersx
  have hform : List.foldr (fun x b => LBTerm.letIn (binderNameOf x.2.name) x.1 b)
      (mkApps (recFix rv.numMinors rv.numParams (!u.isNeverZero)
        [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) [a']) (ms.zip minors) =
      recLets 0 (ms.zip minors) (mkApps (recFix rv.numMinors rv.numParams (!u.isNeverZero)
        [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) (([] ++ [a']).map (lbLift rv.numMinors 0))) := by
    rw [RecLam.recLets_closed _ 0 _ fun p hp => hclm p.1 (List.of_mem_zip hp).1]
    simp [TargetLift.lbLift_closedn _ _ 0 hcla]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hform, ← hsp]
    conv_lhs => rw [hdec]
    refine Erases.recLet hcr hRF ?_ ?_ ?_ (by rw [hni]; rfl) hlenm hersm rfl
      (fun _ _ _ h => nomatch h) hera hlenx hersx
    · simp; omega
    · simp; omega
    · simp; omega
  · have hirr : tc.config.remove_irrel_constr_args = false := by
      rw [hctx.config]; exact hG.irr iv ⟨_, (findDecl_eq_some hivT).1, rfl⟩
    have hph : ∀ ci ∈ (evalEnvOf view cfg decls).decls,
        PhaseIDecl view tc.config (evalEnvOf view cfg decls).decls ci := by
      rw [hctx.config]; exact hG.phase
    have hmem₅ := register_inductive_mem (σ := evalEnvOf view cfg decls) hG.prog hG.sub rfl hirr
      hph hivT hreg
    have hind : ErasesInd E B (evalEnvOf view cfg decls) st'.gdecls iv.name :=
      StateLemmas.ErasesInd.ext ((hgrm.trans hgra).trans hgrx).ext
        (hok₅.inductives iv.name _ hmem₅).2.1
    have hlets : ∀ (zs : List (LBTerm × RecMinor)) (b : LBTerm),
        (∀ p ∈ zs, ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls p.1) →
        ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls b →
        ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls
          (zs.foldr (fun x b => LBTerm.letIn (binderNameOf x.2.name) x.1 b) b) := by
      intro zs b hz hb
      induction zs with
      | nil => exact hb
      | cons z zs ih => exact .letIn (hz z (.head _)) (ih fun p hp => hz p (.tail _ hp))
    refine deps_mkApps_intro (hlets _ _ (fun p hp => ?_) ?_) hdepsx
    · exact ErasesDeps.ext (hgra.trans hgrx).ext (hdepsm p.1 (List.of_mem_zip hp).1)
    · exact deps_mkApps_intro (deps_recFix hsimple hid hind) fun b hb => by
        obtain rfl := List.mem_singleton.1 hb
        exact ErasesDeps.ext hgrx.ext (hdepsa _ (.head _))
  · exact ((hgr₅.trans hgrm).trans hgra).trans hgrx
  · rw [hform]
    refine RecLam.closedn_mkApps.2 ⟨?_, hclx⟩
    have := RecLam.closedn_recLets (ms.zip minors) 0 0
      (mkApps (recFix rv.numMinors rv.numParams (!u.isNeverZero)
        [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) (([] ++ [a']).map (lbLift rv.numMinors 0)))
      (fun p hp => hclm p.1 (List.of_mem_zip hp).1) ?_
    · simpa using this
    have hz : (ms.zip minors).length = rv.numMinors := by
      rw [List.length_zip, ← hlenm, hlenmin]; simp; omega
    rw [hz]
    refine RecLam.closedn_mkApps.2 ⟨by simpa using hcF.1, fun b hb => ?_⟩
    simp only [List.nil_append, List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    simpa using TargetLift.closedn_lbLift rv.numMinors a' 0 0 hcla (Nat.le_refl _)

end
end Steps
end EraseProof
