import EraseProof.Core.StepsCases
import EraseProof.Simulation.Rec

/-!
# Steps of the shipping core's correctness: recursors

An application or a constant whose head is a recursor, which the closure reads only in the
fragment's shape (`RecShaped`, `RecInFragment`): the recursor `T.rec` of a single inductive `T`
without indices whose induction hypotheses take no arguments and are about the last fields.
`visitConstApp` (`LeanToLambdaBox/Erasure.lean:966`) hands the spine to `visitRec` (`:1011`,
`visitRec_spec`), which registers the block of `T`, η-expands the spine to the recursor's arity
(`withAppEtaI_spec`, under the invariant that the block of `T` is erased in the λ□ environment),
and erases the saturated spine (`MarkSat.recr`) by `Erases.recLet`: the erased minor premises
let-bound around the fixpoint of the block (`RecFixOf`), applied to the erased major premise and to
the erased arguments beyond the arity. The fixpoint's alternatives are those of `SimRec.recCs`; it
is closed under the minors and has no free variable (`recFix_closed`), and its only `case` reads
the registered block (`deps_recFix`). It reduces its `case` itself (`direct`) only if the declared
sort of `T` may be `Prop`, and then the fragment test (`PhaseIDecl`) gives `RecFixOf`'s condition
(`rec_direct`): `T` is declared in `Prop`, or its one constructor has no field. The values of
`brecOn` (structural recursion under `structural := .kernel`) reach recursors through this step.

Reference: none in MetaRocq (PCUIC has no recursors); DV-30. Adapted from
`ML-V Core/StepsRec.lean`, whose typing premises are replaced by the marking and whose side
conditions (`rec_side`) by the fragment test.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- A recursor is no recognized `casesOn` (`casesInfo?` reads a definition) and no constructor.
Reference: none. -/
theorem rec_heads {c : Name} {rv : RecursorVal} (hrv : findDecl decls c = some (.recInfo rv)) :
    casesInfo? decls c = none ∧ ctorArity? decls c = none := by
  have hf : findConst decls c = some (.recInfo rv) := hrv
  refine ⟨?_, ?_⟩
  · unfold casesInfo?
    split
    · rw [hf]
    · rfl
  · unfold ctorArity?
    rw [hf]

/-- A `mapM` succeeds with a list whose entries are the images of the entries. Copy of
`ML-V Core/StepsRec.lean:40`. -/
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

/-- A `mapM` of lookups that keep the states: the images are those of the lookup. Copy of
`ML-V Core/StepsRec.lean:69`. -/
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
    obtain ⟨⟨⟨b, st₁⟩, ps₁⟩, h1, h2⟩ := ok_of_bind h
    obtain ⟨hg, rfl, rfl⟩ := hf x _ _ _ _ _ h1
    rw [runPure_bind] at h2
    obtain ⟨⟨⟨bs', st₂⟩, ps₂⟩, h3, h4⟩ := ok_of_bind h2
    obtain ⟨hgs, rfl, rfl⟩ := mapM_run_lookup hf l h3
    cases h4
    simp [List.mapM_cons, hg, hgs]

/-- `List.mapM (visitExpr j)` at the pure backend on renamed terms, from `visitExpr` at `j`
(`ih`): each result is a closed erasure of the renamed marking of its term, with erased
dependencies at the end, and the run grows. Adapted from `ML-V Core/StepsRec.lean:90`.
Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), term by term. -/
theorem visitExpr_mapM {j : Nat} (ih : ∀ e, ExprSpec view cfg decls j e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop} {tc : TravCtx}
    (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc) :
    ∀ {as âs : List Expr} {st st' : ErasureState} {ps ps' : PureState} {ms : List LBTerm},
    RenOK ρ S ls tc.locals ps.next → (∀ a ∈ as, ArgOK S Sc cfg decls a) →
    as.length = âs.length →
    (∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â) →
    StateOK noCert (evalEnvOf view cfg decls) st →
    ((as.map (renFV ρ)).mapM (visitExpr (m := PureM) j)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((ms, st'), ps') →
    (âs.map (renFV ρ)).length = ms.length ∧
      (∀ (i : Nat) a a', (âs.map (renFV ρ))[i]? = some a → ms[i]? = some a' →
        Erases noCert (evalEnvOf view cfg decls) [] a a') ∧
      (∀ a' ∈ ms, closedn 0 a' = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls a') ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps'
  | [], âs, st, st', ps, ps', ms, _, _, hlen, _, hok, hrun => by
    cases âs with
    | cons => cases hlen
    | nil => cases hrun; exact ⟨rfl, by simp, by simp, .refl hok⟩
  | a :: l, âs, st, st', ps, ps', ms, hR, hargs, hlen, hm, hok, hrun => by
    cases âs with
    | nil => cases hlen
    | cons â âl =>
    rw [List.map_cons, List.mapM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨ta, st₁⟩, ps₁⟩, ha, hr1⟩ := ok_of_bind hrun
    rw [runPure_bind] at hr1
    obtain ⟨⟨⟨tl, st₂⟩, ps₂⟩, hl, hr2⟩ := ok_of_bind hr1
    cases hr2
    obtain ⟨hfa, hoa, hna, hra⟩ := hargs a (.head _)
    have ⟨hera, hca, hdepsa, hgra⟩ := ih a hctx hR hfa hsc hoa hna hra hok (hm 0 a â rfl rfl) ha
    obtain ⟨hlen', hers, hdeps, hgr⟩ := visitExpr_mapM ih hctx hsc (hR.mono hgra.next)
      (fun b hb => hargs b (.tail _ hb)) (by simpa using hlen)
      (fun i b bM h1 h2 => hm (i + 1) b bM h1 h2) hgra.inv hl
    refine ⟨by simp [hlen'], fun i b b' h1 h2 => ?_, fun b hb => ?_, hgra.trans hgr⟩
    · cases i with
      | zero => simp at h1 h2; subst h1 h2; exact hera
      | succ i => exact hers i b b' (by simpa using h1) (by simpa using h2)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨hca, ErasesDeps.ext hgr.ext hdepsa⟩
      · exact hdeps b hb

/-- A `case` branch list without the variable in any branch has none. Reference: none. -/
theorem hasFVarB_of {x : FVarId} : ∀ {bs : List (List BinderName × LBTerm)},
    (∀ b ∈ bs, hasFVar x b.2 = false) → hasFVarB x bs = false
  | [], _ => rfl
  | (ns, b) :: bs, h => by
    simp only [hasFVarB, Bool.or_eq_false_iff]
    exact ⟨h _ (.head _), hasFVarB_of fun b hb => h b (.tail _ hb)⟩

/-- `closedn` and `hasFVar` under λs. Copy of `ML-V Core/StepsRec.lean:138`. -/
theorem foldr_lambda_closed (k : Nat) (x : FVarId) : ∀ (xs : List BinderName) (b : LBTerm),
    closedn (k + xs.length) b = true → hasFVar x b = false →
      closedn k (xs.foldr .lambda b) = true ∧ hasFVar x (xs.foldr .lambda b) = false
  | [], b, h1, h2 => ⟨h1, h2⟩
  | y :: xs, b, h1, h2 => by
    have := foldr_lambda_closed (k + 1) x xs b (by simpa [Nat.add_assoc, Nat.add_comm 1] using h1) h2
    exact ⟨this.1, this.2⟩

/-- `closedn` and `hasFVar` of an application to `□`s. Copy of `ML-V Core/StepsRec.lean:147`. -/
theorem foldl_box_closed (k : Nat) (x : FVarId) : ∀ (m : Nat) (f : LBTerm),
    closedn k f = true → hasFVar x f = false →
      closedn k ((List.replicate m LBTerm.box).foldl .app f) = true ∧
        hasFVar x ((List.replicate m LBTerm.box).foldl .app f) = false
  | 0, f, h1, h2 => ⟨h1, h2⟩
  | m + 1, f, h1, h2 => by
    rw [List.replicate_succ, List.foldl_cons]
    exact foldl_box_closed k x m (.app f .box) (by simp [closedn, h1]) (by simp [hasFVar, h2])

/-- The fixpoint of a recursor of a single inductive in the simple shape (`RecFix.SimpleAlt`) is
closed under its `N` minors and has no free variable. Copy of `ML-V Core/StepsRec.lean:158`. -/
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
        refine ⟨by omega, closednB_of fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact (halt c hc y).1
      · simp only [hasFVar, Bool.or_eq_false_iff]
        refine ⟨trivial, hasFVarB_of fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact (halt c hc y).2
  refine ⟨?_, fun y => ?_⟩
  · simp [closedn, closednD, (hinner (default : FVarId)).1]
  · simp [hasFVar, hasFVarD, (hinner y).2]

/-- The fixpoint of a recursor of a single inductive in the simple shape has erased dependencies
when its inductive's block has (its `case` is the only node that reads the λ□ environment). Copy
of `ML-V Core/StepsRec.lean:225`. -/
theorem deps_recFix {σ : EvalEnv} {lenv : GlobalDeclarations} {N npars : Nat} {direct : Bool}
    {nm x T : Name} {indid : InductiveId} {minors : List RecMinor}
    (hs : ∀ c ∈ SimRec.recCs minors, RecFix.SimpleAlt c) (hid : IndIdOf σ T = some indid)
    (hind : ErasesInd σ lenv T) :
    ErasesDeps noCert σ lenv (recFix N npars direct [⟨nm, [x], indid, SimRec.recCs minors⟩] 0) := by
  rw [RecFix.recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.sub_self,
    List.foldr_cons, List.foldr_nil]
  rw [RecFix.innerS_congr (fun c hc => RecFix.altF_simple N _ rfl (hs c hc))]
  have halt : ∀ c, ErasesDeps noCert σ lenv (RecFix.altG (fun gi B => .bvar (B + 2 + (N - 1 - gi)))
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
    rw [RecFix.foldl_app_eq_mkApps]
    refine ErasesDeps.mkApps_iff.2 ⟨?_, fun a ha => by rw [(List.mem_replicate.1 ha).2]; exact .box⟩
    have : ∀ (xs : List BinderName) (b : LBTerm), ErasesDeps noCert σ lenv b →
        ErasesDeps noCert σ lenv (xs.foldr .lambda b) := by
      intro xs; induction xs with
      | nil => exact fun _ h => h
      | cons y ys ih => exact fun b h => .lambda (ih b h)
    exact this _ _ (halt c)
  · exact .case hid hind .bvar fun br hbr => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hbr
      exact halt c

/-- `RecFixOf`'s condition on the `direct` form from the fragment test: if `visitRec` reads the
declared sort of the recursor's inductive `T` as one that may be `Prop` (`sortMayBeProp`,
`LeanToLambdaBox/Erasure.lean:1038`: the sort `u` of its arity is not syntactically never zero),
then `T`, if it has one constructor, is declared in `Prop` or its constructor has no field:
`PhaseIDecl` admits a sort that may be zero only if it is `Prop` or `T` is not `Eliminated`.
Reference: none (DV-30). -/
theorem rec_direct (hG : CoreEnv view cfg decls) {T : Name} {iv : InductiveVal} {n : Nat}
    {u : Level} (hT : findDecl decls T = some (.inductInfo iv))
    (hsh : arityShape iv.type = some (n, u)) (hz : u.isNeverZero = false) :
    ∀ iv' ∈ [iv], iv'.ctors.length = 1 → (evalEnvOf view cfg decls).propInd iv'.name = true ∨
      ∀ cn ∈ iv'.ctors, ctorFields (evalEnvOf view cfg decls) cn = some 0 := by
  intro iv' hiv' h1
  obtain rfl := List.mem_singleton.1 hiv'
  have hTn : iv'.name = T := (findDecl_eq_some hT).2
  obtain ⟨-, -, ⟨n', u', hsh', hu⟩, -⟩ := hG.phase _ (findDecl_eq_some hT).1
  rw [hsh] at hsh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsh')
  rcases hu with rfl | hu | ⟨-, hne⟩
  · left
    simp [EvalEnv.propInd, evalEnvOf, hTn, hT, hsh, EvidentZero]
  · rw [hz] at hu; cases hu
  · right
    obtain ⟨cn, hcn⟩ : ∃ cn, iv'.ctors = [cn] := List.length_eq_one_iff.1 h1
    obtain ⟨cv, hcv, -, -⟩ := hG.ctorIdx T iv' hT 0 cn (by simp [hcn])
    intro cn' hcn'
    rw [hcn, List.mem_singleton] at hcn'
    subst hcn'
    have h0 : cv.numFields = 0 := Nat.eq_zero_of_not_pos fun hp => hne (.inr ⟨cn', cv, hcn, hcv, hp⟩)
    simp [ctorFields, evalEnvOf, hcv, h0]

/-- The slice of an array between two prefixes of its list. Reference: none. -/
theorem extract_mid {α : Type} (l₁ l₂ l₃ : List α) :
    (l₁ ++ l₂ ++ l₃).toArray.extract l₁.length (l₁.length + l₂.length) = l₂.toArray := by
  apply Array.ext'
  simp

/-- The suffix of an array after a prefix of its list. Reference: none. -/
theorem extract_tail {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).toArray.extract l₁.length = l₂.toArray := by
  apply Array.ext'
  simp

/-- `visitRec (i + 1)` at the pure backend on the renamed spine of `c.{us} as`, for a recursor
`rv` in the fragment's shape (`RecInFragment`: `T.rec` of a single inductive `iv` without indices
whose induction hypotheses take no arguments and are about the last fields, not kept as a
constant), whose marking is the η-expansion `MarkEta` to the recursor's arity, from `visitExpr`
at the fuels up to `i` (`ih`): the block of `T` is registered (`register_inductive_spec`), the
spine is η-expanded (`withAppEtaI_spec`, the block erased in the state the continuation starts
from), and the saturated spine (`MarkSat.recr`) is erased by `Erases.recLet`: the minors one by
one (`visitExpr_mapM`), let-bound around the fixpoint `RecFixOf` gives (`recFix_closed`,
`rec_direct`) applied to the major premise, then the arguments beyond the arity
(`visitAppArgs_list`). Adapted from `ML-V Core/StepsRec.lean:425`. Reference: `visitRec`
(`LeanToLambdaBox/Erasure.lean:1011`); DV-30. -/
theorem visitRec_spec (hG : CoreEnv view cfg decls) {i : Nat}
    (ih : ∀ m ≤ i, ∀ e, ExprSpec view cfg decls m e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {c : Name}
    {us : List Level} {rv : RecursorVal} {as : List Expr} {A ê : Expr}
    (hrv : findDecl decls c = some (.recInfo rv)) (hfr : RecInFragment cfg decls rv)
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (hsc : ScopeOK decls Sc)
    (hargs : ∀ a ∈ as, ArgOK S Sc cfg decls a)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hA : Pure.inferType ⟨decls⟩ oracleFuel ls [] (mkAppN (.const c us) as.toArray) = .ok A)
    (hη : MarkEta decls cfg ls (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)
      A c us as ê)
    (hrun : (visitRec (m := PureM) (i + 1) rv (mkAppN (.const c us) (as.map (renFV ρ)).toArray)).runPure
      st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨T, iv, cvs, hRn, hall, hblk, hshF, hnsc⟩ := hfr
  obtain ⟨hT, hcl, hcget⟩ := SimRec.recBlock?_single (σ := evalEnvOf view cfg decls) hall hblk
  have hT' : findDecl decls T = some (.inductInfo iv) := hT
  have hTn : iv.name = T := (findDecl_eq_some hT').2
  unfold recShapeInFragment at hshF
  rw [hall] at hshF
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hshF
  obtain ⟨⟨hni, -⟩, hihF⟩ := hshF
  rw [visitRec, runPure_bind] at hrun
  obtain ⟨⟨⟨ivs, st₁⟩, ps₁⟩, hivs0, hr1⟩ := ok_of_bind hrun
  obtain ⟨hivs, hs1, hp1⟩ := mapM_run_lookup (g := fun t => match findDecl decls t with
      | some (.inductInfo iv) => some iv
      | _ => none)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      rw [show findDecl decls x = _ from hci]) _ hivs0
  subst st₁ ps₁
  dsimp only at hr1
  rw [runPure_bind] at hr1
  obtain ⟨⟨⟨cvs', st₂⟩, ps₂⟩, hcvs0, hr2⟩ := ok_of_bind hr1
  obtain ⟨hcvs, hs2, hp2⟩ := mapM_run_lookup (g := fun c => match findDecl decls c with
      | some (.ctorInfo cv) => some cv
      | _ => none)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      rw [show findDecl decls x = _ from hci]) _ hcvs0
  subst st₂ ps₂
  dsimp only at hr2
  have hblk' : recBlockOf? decls rv = some (ivs, cvs') := by
    unfold recBlockOf?
    erw [hivs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    erw [hcvs]
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
  obtain ⟨x, rfl⟩ := (hG.recs c rv T iv hrv hall hT' hni).2 _ _ _ hsh
  obtain ⟨hlmo, hlmi, hmi⟩ := SimRec.recShape_spec hsh
  have hlenmin : minors.length = rv.numMinors := by
    rw [hlmi, List.length_map, hcl, hG.recMinors c rv T iv hrv hall hRn hT']
  rw [runPure_bind] at hr2
  obtain ⟨⟨⟨s3, st₃⟩, ps₃⟩, hloop, hr3⟩ := ok_of_bind hr2
  rw [List.forIn_cons, runPure_bind] at hloop
  obtain ⟨⟨⟨y, st₄⟩, ps₄⟩, hreg0, hloop2⟩ := ok_of_bind hloop
  simp only [Std.toStream, Std.Stream.next?] at hreg0
  rw [runPure_bind] at hreg0
  obtain ⟨⟨⟨⟨indid, masks⟩, st₅⟩, ps₅⟩, hreg, hy⟩ := ok_of_bind hreg0
  cases hy
  dsimp only at hloop2
  cases hloop2
  dsimp only at hr3
  obtain ⟨hok₅, hext₅, hcon₅, hid, hind₅, hmasks, hp5⟩ :=
    register_inductive_spec hG hctx hok hT' hreg
  subst ps₃
  rw [runPure_bind] at hr3
  obtain ⟨⟨⟨j, st₆⟩, ps₆⟩, hj0, hr4⟩ := ok_of_bind hr3
  obtain ⟨hj, hs6, hp6⟩ := getOrFail_run hj0
  subst st₆ ps₆
  rw [hall, List.idxOf?_eq_some_iff] at hj
  obtain ⟨hj1, hj2, -⟩ := hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj1
  subst hj1
  have hmaj : rv.getMajorInduct = T := hj2.symm
  dsimp only at hr4
  have hgr₅ : Grows (evalEnvOf view cfg decls) Sc st st₃ ps ps :=
    ⟨hok₅, hext₅, Nat.le_refl _, fun c kn h h' => by rw [hcon₅, h] at h'; cases h'⟩
  refine (fun h => ⟨h.1, h.2.1, h.2.2.1, hgr₅.trans h.2.2.2⟩) (withAppEtaI_spec
    (I := fun st => ErasesInd (evalEnvOf view cfg decls) st.gdecls T) hG.closed ?_ hctx hR hsc
    hargs hok₅ hind₅ hA hη hr4)
  -- the saturated spine
  intro ρ₁ S₁ ls₁ Sc₁ ê₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁ hctx₁ hR₁ hsc₁ hargs₁ hle₁ hok₁ hI₁ hs₁ hrun₁
  obtain ⟨hci₀, hca⟩ := rec_heads hrv
  have hlenmi : minors.length = iv.ctors.length := by rw [hlmi, List.length_map, hcl]
  have hmo : rv.numMotives = 1 := by rw [← hlmo]; rfl
  rw [hsh] at hihF
  -- the alternatives of the fixpoint are those of `SimRec.recCs`, in the simple shape
  have hmk : ∀ ci, ci < minors.length →
      masks.getD ci #[] = Array.replicate (minors.getD ci default).fields.length .keep := by
    intro ci hci
    obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors[ci]? = some cn := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨cv, hcv, hcvd⟩ := hcget ci cn hcn
    obtain ⟨mi, hmi'⟩ : ∃ mi, minors[ci]? = some mi := ⟨_, List.getElem?_eq_getElem hci⟩
    obtain ⟨hmf, -⟩ := hmi ci cv.numFields mi (by simp [hcv]) hmi'
    rw [List.getD_eq_getElem?_getD, hmasks.2 ci cn cv hcn hcvd, List.getD_eq_getElem?_getD, hmi']
    simp [hmf]
  have hcs : (List.range (List.take iv.ctors.length (List.drop 0 minors)).length).map (fun c =>
      (0 + c, (List.take iv.ctors.length (List.drop 0 minors)).getD c default,
        List.getD masks c #[])) = SimRec.recCs minors := by
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
    obtain ⟨mi, hmi'⟩ : ∃ mi, minors[ci]? = some mi := ⟨_, List.getElem?_eq_getElem hci'⟩
    obtain ⟨n, hn⟩ : ∃ n, (cvs.map (·.numFields))[ci]? = some n :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_map]; omega)⟩
    obtain ⟨hnf, hihs⟩ := hmi ci n mi hn hmi'
    have hih := beq_iff_eq.1 (List.all_eq_true.1 hihF mi (List.mem_of_getElem? hmi'))
    rw [List.getD_eq_getElem?_getD, hmi', Option.getD_some]
    refine ⟨rfl, fun h hh => ?_⟩
    dsimp only at hh ⊢
    refine ⟨?_, by have := (hihs h hh).2; omega, by have := (hihs h hh).1; omega⟩
    have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
      List.mem_map.2 ⟨h, hh, rfl⟩
    rw [hih] at hm
    obtain ⟨f, -, hf⟩ := List.mem_map.1 hm
    exact (Prod.mk.inj hf).2.symm
  have hmasks' : iv.ctors.mapM (fun c => (ctorFields (evalEnvOf view cfg decls) c).map fun k =>
      (Array.replicate k .keep : ConstructorArgMask)) = some masks := by
    refine mapM_of_get hmasks.1 fun ci cn hcn => ?_
    obtain ⟨cv, -, hcvd⟩ := hcget ci cn hcn
    rw [hmasks.2 ci cn cv hcn hcvd]
    simp [ctorFields, show findDecl (evalEnvOf view cfg decls).decls cn = _ from hcvd]
  have hid' : IndIdOf (evalEnvOf view cfg decls) iv.name = some indid := by rw [hTn]; exact hid
  have hrm : recMembers (evalEnvOf view cfg decls) minors 0 [iv] [[x]] =
      some [⟨iv.name, [x], indid, SimRec.recCs minors⟩] := by
    rw [← hcs]; simp [recMembers, hid', hmasks']
  have hTm : findDecl decls rv.getMajorInduct = some (.inductInfo iv) := by rw [hmaj]; exact hT'
  have hidx : rv.all.idxOf? T = some 0 := by rw [hall]; simp
  cases hs₁ with
  | @recr _ _ _ _ _ maj majM _ ps₀ ms₀ mins minsM is îs extra êxtra _ _ hrv' _ _ _ hlps hlms
      hlmins hlis _ hlm hminsM hli hisM hmajM hle hextra =>
    rw [hrv] at hrv'
    cases hrv'
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (by rw [hlis, hni])
    have hlî : îs.length = 0 := by rw [← hli]; rfl
    have hA₁ : ∀ a ∈ ps₀ ++ ms₀ ++ mins ++ [] ++ [maj] ++ extra, ArgOK S₁ Sc₁ cfg decls a := hargs₁
    dsimp only at hrun₁
    rw [hcs] at hrun₁
    rw [show (#[].push (⟨iv.name, [x], indid, SimRec.recCs minors⟩ : RecMember)).toList =
      [⟨iv.name, [x], indid, SimRec.recCs minors⟩] from rfl] at hrun₁
    obtain ⟨⟨n₀, u₀⟩, harity⟩ := Option.isSome_iff_exists.1
      (hG.arity iv ⟨_, (findDecl_eq_some hT').1, rfl⟩)
    have hfind : [iv].find? (fun x => x.name == rv.getMajorInduct) = some iv := by
      simp [hmaj, hTn]
    rw [hfind, Option.bind_some, harity] at hrun₁
    dsimp only at hrun₁
    -- the major premise
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨mj, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
    obtain ⟨hmj, hsa, hpa⟩ := getOrFail_run hg
    subst sa pa
    have hmj' : mj = renFV ρ₁ maj := by
      have hl : (ps₀ ++ ms₀ ++ mins ++ [] ++ [maj] ++ extra).map (renFV ρ₁) =
          (ps₀ ++ ms₀ ++ mins).map (renFV ρ₁) ++ ([renFV ρ₁ maj] ++ extra.map (renFV ρ₁)) := by simp
      rw [hl, show rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 - 1 =
        ((ps₀ ++ ms₀ ++ mins).map (renFV ρ₁)).length by simp [hlps, hlms, hlmins, hni] <;> omega,
        List.getElem?_toArray, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hmj
      simpa using hmj.symm
    subst hmj'
    dsimp only at hrun₁
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run] at hrun₁
    rcases hTL : Pure.typeLevel ⟨decls⟩ oracleFuel tc₁.locals (renFV ρ₁ maj) with err | u
    · rw [hTL] at hrun₁; cases hrun₁
    rw [hTL] at hrun₁
    dsimp only [Except.map] at hrun₁
    rw [ok_bind', ok_bind'] at hrun₁
    dsimp only at hrun₁
    -- the minor premises
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨ms', st₈⟩, ps₈⟩, hms, hrun₁⟩ := ok_of_bind hrun₁
    have hex1 : ((ps₀ ++ ms₀ ++ mins ++ [] ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives) (rv.numParams + rv.numMotives + rv.numMinors) =
        (mins.map (renFV ρ₁)).toArray := by
      have := extract_mid ((ps₀ ++ ms₀).map (renFV ρ₁)) (mins.map (renFV ρ₁))
        (([maj] ++ extra).map (renFV ρ₁))
      simp only [List.length_map, List.length_append, hlps, hlms, hlmins] at this
      simpa using this
    rw [hex1, List.toList_toArray] at hms
    dsimp only at hrun₁
    obtain ⟨hlenm, hersm, hdepsm, hgrm⟩ := visitExpr_mapM (ih i (Nat.le_refl _)) hctx₁ hsc₁ hR₁
      (fun a ha => hA₁ a (by simp [ha])) hlm hminsM hok₁ hms
    -- the fixpoint applied to the major premise
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨app, st₉⟩, ps₉⟩, happ, hrun₁⟩ := ok_of_bind hrun₁
    cases i with
    | zero => rw [visitAppArgs] at happ; cases happ
    | succ i' =>
    have hex2 : ((ps₀ ++ ms₀ ++ mins ++ [] ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives + rv.numMinors)
        (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
        ([maj].map (renFV ρ₁)).toArray := by
      have := extract_mid ((ps₀ ++ ms₀ ++ mins).map (renFV ρ₁)) ([maj].map (renFV ρ₁))
        (extra.map (renFV ρ₁))
      simp only [List.length_map, List.length_append, List.length_singleton, hlps, hlms,
        hlmins] at this
      simpa [hni] using this
    rw [hex2] at happ
    obtain ⟨as', rfl, hlen', hers, hdeps, hgra⟩ := visitAppArgs_list (ih i' (by omega)) hctx₁ hsc₁
      (hR₁.mono hgrm.next) (fun a ha => hA₁ a (by simp at ha; simp [ha])) (as := [maj]) (âs := [majM]) rfl
      (fun k a â h1 h2 => by
        cases k with
        | zero => simp at h1 h2; subst h1 h2; exact hmajM
        | succ k => simp at h1) hgrm.inv happ
    obtain ⟨a', rfl⟩ : ∃ a', as' = [a'] := by
      match as', hlen' with
      | [a'], _ => exact ⟨a', rfl⟩
    have hera := hers 0 _ a' rfl rfl
    have hcla := (hdeps a' (.head _)).1
    -- the arguments beyond the arity
    have hex3 : ((ps₀ ++ ms₀ ++ mins ++ [] ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
        (extra.map (renFV ρ₁)).toArray := by
      have := extract_tail ((ps₀ ++ ms₀ ++ mins ++ [maj]).map (renFV ρ₁)) (extra.map (renFV ρ₁))
      simp only [List.length_map, List.length_append, List.length_singleton, hlps, hlms,
        hlmins] at this
      simpa [hni] using this
    dsimp only at hrun₁
    rw [hex3] at hrun₁
    obtain ⟨ex', rfl, hlenx, hersx, hdepsx, hgrx⟩ := visitAppArgs_list (ih i' (by omega)) hctx₁
      hsc₁ (hR₁.mono (hgrm.trans hgra).next) (fun a ha => hA₁ a (by simp [ha])) hle hextra
      hgra.inv hrun₁
    -- the erasure
    have hRF : RecFixOf (evalEnvOf view cfg decls) rv minors (recFix rv.numMinors rv.numParams
        (!u₀.isNeverZero && !u.isNeverZero) [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) :=
      ⟨[iv], cvs, [[x]], _, T, iv, 0, _, hblk, hsh, hlenmin, hrm, hmaj, hT', hidx,
        fun h => rec_direct hG hT' harity (by simp at h; exact h.1), rfl,
        (recFix_closed hlenmin hsimple).1, (recFix_closed hlenmin hsimple).2⟩
    have hcF := recFix_closed (npars := rv.numParams) (direct := !u₀.isNeverZero && !u.isNeverZero)
      (nm := iv.name) (x := x) (indid := indid) hlenmin hsimple
    have hclm : ∀ m ∈ ms', closedn 0 m = true := fun m hm => (hdepsm m hm).1
    have hform : List.foldr (fun x b => LBTerm.letIn (binderNameOf x.snd.name) x.fst b)
        (mkApps (recFix rv.numMinors rv.numParams (!u₀.isNeverZero && !u.isNeverZero)
          [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0) [a']) (ms'.zip minors) =
        recLets 0 (ms'.zip minors) (mkApps (recFix rv.numMinors rv.numParams
          (!u₀.isNeverZero && !u.isNeverZero) [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0)
          (([] ++ [a']).map (lbLift rv.numMinors 0))) := by
      rw [RecLam.recLets_closed _ 0 _ fun p hp => hclm p.1 (List.of_mem_zip hp).1]
      simp [TargetLift.lbLift_closedn _ _ 0 hcla]
    have hz : (ms'.zip minors).length = rv.numMinors := by
      rw [List.length_zip, ← hlenm, hlenmin]; simp [← hlm, hlmins]
    have hind : ErasesInd (evalEnvOf view cfg decls) st₁'.gdecls T :=
      ErasesInd.ext ((hgrm.trans hgra).trans hgrx).ext hI₁
    refine ⟨?_, ?_, ?_, (hgrm.trans hgra).trans hgrx⟩
    · rw [hform, renFV_mkAppN]
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine Erases.recLet (ps := ps₀.map (renFV ρ₁)) (ms := ms₀.map (renFV ρ₁))
        (mins := minsM.map (renFV ρ₁)) (is := îs.map (renFV ρ₁)) (extra := êxtra.map (renFV ρ₁))
        (is' := []) hrv hRF ?_ ?_ ?_ ?_ hlenm hersm ?_ (fun _ _ _ _ h => nomatch h) hera hlenx hersx
      · simp [hlps]
      · simp [hlms]
      · simp [← hlm, hlmins]
      · simp [hlî, hni]
      · simp [hlî]
    · rw [hform]
      refine RecLam.closedn_mkApps.2 ⟨?_, fun b hb => (hdepsx b hb).1⟩
      have hb : closedn (0 + 0 + (ms'.zip minors).length) (mkApps (recFix rv.numMinors
          rv.numParams (!u₀.isNeverZero && !u.isNeverZero)
          [⟨iv.name, [x], indid, SimRec.recCs minors⟩] 0)
          (([] ++ [a']).map (lbLift rv.numMinors 0))) = true := by
        rw [hz]
        refine RecLam.closedn_mkApps.2 ⟨by simpa using hcF.1, fun b hb => ?_⟩
        simp only [List.nil_append, List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        simpa using TargetLift.closedn_lbLift rv.numMinors a' 0 0 hcla (Nat.le_refl _)
      simpa using RecLam.closedn_recLets (ms'.zip minors) 0 0 _
        (fun p hp => hclm p.1 (List.of_mem_zip hp).1) hb
    · refine ErasesDeps.mkApps_iff.2 ⟨?_, fun b hb => (hdepsx b hb).2⟩
      have hlets : ∀ (zs : List (LBTerm × RecMinor)) (b : LBTerm),
          (∀ p ∈ zs, ErasesDeps noCert (evalEnvOf view cfg decls) st₁'.gdecls p.1) →
          ErasesDeps noCert (evalEnvOf view cfg decls) st₁'.gdecls b →
          ErasesDeps noCert (evalEnvOf view cfg decls) st₁'.gdecls
            (zs.foldr (fun x b => LBTerm.letIn (binderNameOf x.2.name) x.1 b) b) := by
        intro zs b hz hb
        induction zs with
        | nil => exact hb
        | cons z zs ih => exact .letIn (hz z (.head _)) (ih fun p hp => hz p (.tail _ hp))
      refine hlets _ _ (fun p hp => ErasesDeps.ext (hgra.trans hgrx).ext
        (hdepsm p.1 (List.of_mem_zip hp).1).2) ?_
      refine ErasesDeps.mkApps_iff.2 ⟨deps_recFix hsimple hid hind, fun b hb => ?_⟩
      obtain rfl := List.mem_singleton.1 hb
      exact ErasesDeps.ext hgrx.ext (hdeps _ (.head _)).2
  | ctor _ h₂ => rw [hca] at h₂; cases h₂
  | quotMk _ _ hq | quotLift _ _ hq => rw [hrv] at hq; cases hq
  | casesProp h₁ | casesReduced h₁ | cases h₁ => simp [casesOnOf?, hci₀] at h₁


/-- `visitApp (k + 1)` at the pure backend on a spine that the oracle keeps whose head is a
recursor, from `visitExpr` at the fuels up to `k`: the closure reads the recursor in the
fragment's shape (`RecShaped`, `RecInFragment`), so the head has its arity (`markArity?`) and the
marking is `MarkOf.special`; `visitConstApp` takes its recursor branch, and `visitRec` erases the
spine (`visitRec_spec`). Adapted from `ML-V Core/StepsRec.lean:849 visitApp_rec`. Reference:
`visitConstApp` (`LeanToLambdaBox/Erasure.lean:966`); DV-30. -/
theorem visitApp_rec (hG : CoreEnv view cfg decls) {k : Nat} (ih : StepIH view cfg decls k)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop} {e ê : Expr}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {c : Name}
    {us : List Level} {rv : RecursorVal} (hfn : e.getAppFn = .const c us)
    (hrv : findDecl decls c = some (.recInfo rv))
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e)
    (hsc : ScopeOK decls Sc) (hocc : ∀ d, nameOccurs d e = true → Sc d) (hnp : NatPlain cfg e)
    (hrs : RecShaped cfg decls e) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false)
    (hrun : (visitApp (m := PureM) (k + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨hcs, hca⟩ := rec_heads hrv
  have hor' := oracle_agree hG.closed hR he hor
  cases hm with
  | erase h₁ => rw [h₁] at hor'; cases hor'
  | @app _ f fM as âs _ _ hfa hfc =>
    rw [getAppFn_mkAppN_of hfa] at hfn
    exact absurd hfn (hfc c us)
  | @constApp _ c' us' as âs _ hma' =>
    rw [getAppFn_mkAppN_const] at hfn
    cases hfn
    obtain ⟨⟨-, -, -, hrsF⟩, -⟩ := spine_premises (f := .const c us) ⟨he, hocc, hnp, hrs⟩
    obtain ⟨T, iv, cvs, -, -, hb, -, hst⟩ := hrsF rv hrv
    simp [markArity?, hcs, hca, hrv, hb, hst] at hma'
  | @special _ c' us' ar A ê as _ hma' hA hη =>
    rw [getAppFn_mkAppN_const] at hfn
    cases hfn
    obtain ⟨⟨-, -, -, hrsF⟩, hargs⟩ := spine_premises (f := .const c us) ⟨he, hocc, hnp, hrs⟩
    have hfr := hrsF rv hrv
    obtain ⟨T, iv, cvs, -, -, hb, -, hst⟩ := id hfr
    have har : ar = rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 := by
      simp [markArity?, hcs, hca, hrv, hb, hst] at hma'
      exact hma'.symm
    subst har
    have hren : renFV ρ (mkAppN (.const c us) as.toArray) =
        mkAppN (.const c us) (as.map (renFV ρ)).toArray := renFV_mkAppN ρ _ as
    rw [hren, visitApp] at hrun
    simp only [getAppFn_mkAppN_const] at hrun
    cases k with
    | zero => rw [visitConstApp] at hrun; cases hrun
    | succ j =>
    rw [visitConstApp, withApp_mkAppN rfl] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
        EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hcs], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
        EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
        EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((some (.recInfo rv), st), ps) by
      show Except.ok ((findConst decls c, st), ps) = _
      rw [show findConst decls c = findDecl decls c from rfl, hrv], ok_bind'] at hrun
    dsimp only at hrun
    cases j with
    | zero => rw [visitRec] at hrun; cases hrun
    | succ i =>
    exact visitRec_spec hG (fun m hm => ih.expr m (by omega)) hrv hfr hctx hR hsc hargs hok hA hη
      hrun
  | fvar | mdata | lam | letE | proj | litZero | litSucc => cases hfn

/-- The recursor step: an application or a constant whose head is a recursor, through
`visitApp_rec`; when the oracle erases the spine, `visitExpr_box`. The values of `brecOn`
(structural recursion under `structural := .kernel`) reach recursors through it. Adapted from
`ML-V Core/StepsRec.lean:919 stepsB_rec`. Reference: none (PCUIC has no recursors); DV-30. -/
theorem visitExpr_rec_step (hG : CoreEnv view cfg decls) {fuel : Nat}
    (ih : StepIH view cfg decls fuel) {e : Expr} {c : Name} {us : List Level} {rv : RecursorVal}
    (hfn : e.getAppFn = .const c us) (hrv : findDecl decls c = some (.recInfo rv)) :
    ExprSpec view cfg decls (fuel + 1) e := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  have hstep : (visitExpr (m := PureM) (fuel + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps') → (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok true ∧
        r = .box ∧ st' = st ∧ ps' = ps) ∨
      (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false ∧
        (visitApp (m := PureM) fuel (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((r, st'), ps')) := by
    cases e with
    | app f a => intro h; simp only [renFV] at h ⊢; rw [visitExpr] at h; exact oracle_run h
    | const c' us' => intro h; simp only [renFV] at h ⊢; rw [visitExpr] at h; exact oracle_run h
    | _ => cases hfn
  rcases hstep hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_rec hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hfn hrv hctx hR he hsc hocc hnp hrs hok hm hor hrun

end

end Steps

end EraseProof
