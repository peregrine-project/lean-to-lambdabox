import EraseProof.Simulation.Iota
import EraseProof.Simulation.RecFix
import EraseProof.Core.Steps

/-!
# The recursor ι case of the simulation

A saturated recursor of a single inductive without indices (`SrcEval.recIota`) is erased to the λ□
fixpoint of `recFix` under `let`s of its erased minors (`Erases.recLet`), or with the minors' values
substituted (`Erases.recFix`). The λ□ evaluation binds the minors' values, unfolds the fixpoint on
the major's value, selects the constructor's alternative (a λ□ `case`, or the alternative applied
to `□` when the major is erased in the reduced form) and applies the minor's value to the fields
and to the recursive calls on the recursive fields, which are erasures of the source induction
hypotheses (`Erases.recFix`). Reference: none (MetaRocq has no recursors; DV-30); the λ□ steps are
`eval_zeta`, `eval_fix`, `eval_beta` and `eval_iota` (`MR E/EWcbvEval.v`).
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed WHRedS)

namespace EraseProof

namespace SimRec

open TargetSubst TargetLift RecEval RecFix

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- The alternatives of the fixpoint of a recursor of a single inductive, one per constructor. -/
def recCs (minors : List RecMinor) : List (Nat × RecMinor × ConstructorArgMask) :=
  (List.range minors.length).map fun ci =>
    (ci, minors.getD ci default, Array.replicate (minors.getD ci default).fields.length .keep)

/-- The fixpoint `recFix` of a recursor of a single inductive without indices whose recursive
fields take no arguments: one λ for the major premise around the `case` (or the reduced form), the
alternative of the constructor `ci` applying the bound minor `ci` to the fields and to the
fixpoint on the recursive fields. -/
theorem recFix_shape (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors minors' : List RecMinor} {us : List Level} {F : LBTerm}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hRF : RecFixOf E B σ rv us minors' F) :
    minors' = minors ∧ minors.length = rv.numMinors ∧ minors.length = iv.ctors.length ∧
    (∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
        mi.fields.length = cv.numFields) ∧
    (∀ c ∈ recCs minors, SimpleAlt c) ∧
    ∃ indid direct nm x, IndIdOf σ iv.name = some indid ∧
      F = .fix [{ name := nm, principalArgIdx := 0, body := .lambda x (innerS direct indid
        rv.numParams (recCs minors)
        (altG (fun gi B => .bvar (B + 2 + (rv.numMinors - 1 - gi))) (fun B => .bvar (B + 1)))) }] 0 ∧
      (direct = false → ∃ l, casesSortLevel iv us = some l ∧ l.isNeverZero = true) ∧
      (direct = true → iv.ctors.length = 1 → FieldsErasable E B iv.name) ∧
      Subsingleton E B T := by
  obtain ⟨ivs, cvs', motives', members, T', ivT, j, direct, hblk', hshape', hml, hmem, -, hivT,
    hj, hd1, hd2, hss, rfl, -, -⟩ := hRF
  rw [hblk] at hblk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hblk')
  rw [hshape] at hshape'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape')
  obtain ⟨⟨x, rfl⟩, hcl, hmc, hmin⟩ := RecWhred.rec_minors henv hsub hcr hall hcT hblk hni hshape
  rw [hall, List.idxOf?_eq_some_iff] at hj
  obtain ⟨hj1, hj2, -⟩ := hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj1
  subst hj1
  have hT' : T' = T := hj2.symm
  subst hT'
  have hTiv := (RecWhred.recBlock?_single hall hblk).1
  rw [hTiv] at hivT
  cases hivT
  have hlen : minors.length = iv.ctors.length := by omega
  simp [recMembers, Option.bind_eq_some_iff] at hmem
  obtain ⟨indid, hid, masks, hmasks, rfl⟩ := hmem
  -- the minors and the masks
  have hcvs := (RecWhred.recBlock?_single hall hblk).2
  have hfl : ∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
      mi.fields.length = cv.numFields := fun i cv h => by
    obtain ⟨mi, h1, h2, -⟩ := hmin i cv h
    exact ⟨mi, h1, h2⟩
  have hcs : (List.range (min iv.ctors.length minors.length)).map (fun ci =>
      (ci, (minors.take iv.ctors.length)[ci]?.getD default, masks[ci]?.getD #[])) = recCs minors := by
    unfold recCs
    rw [← hlen, Nat.min_self, List.take_length]
    refine List.map_congr_left fun ci hci => ?_
    have hci' := List.mem_range.1 hci
    simp only [List.getD_eq_getElem?_getD, Prod.mk.injEq, true_and]
    obtain ⟨n, hn⟩ : ∃ n, iv.ctors[ci]? = some n := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hml', hmget⟩ := RecWhred.mapM_get hmasks
    obtain ⟨mk, hmk, hfk⟩ := hmget ci n hn
    obtain ⟨-, hcget⟩ := RecWhred.mapM_get hcvs
    obtain ⟨cv, hcv, hcvd⟩ := hcget ci n hn
    obtain ⟨mi, hmi, hmf⟩ := hfl ci cv hcv
    rw [hmk, hmi]
    simp only [Option.getD_some]
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hfk
    unfold ctorFields at hk
    unfold EvalEnv.ctorOf? at hcvd
    split at hcvd
    · rename_i cv' hcv'
      cases hcvd
      rw [hcv'] at hk
      cases hk
      rw [hmf]
    · cases hcvd
  have hsimple : ∀ c ∈ recCs minors, SimpleAlt c := by
    intro c hc
    unfold recCs at hc
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
    have hci' := List.mem_range.1 hci
    obtain ⟨cv, hcv⟩ : ∃ cv, cvs[ci]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by rw [hcl]; omega)⟩
    obtain ⟨mi, hmi, -, hle, hmem0⟩ := hmin ci cv hcv
    rw [List.getD_eq_getElem?_getD, hmi, Option.getD_some]
    simp only [SimpleAlt]
    refine ⟨trivial, fun h hh => ⟨?_, hmem0 h hh, ?_⟩⟩
    · have := hihs mi (List.mem_of_getElem? hmi)
      have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [this] at hm
      obtain ⟨f, -, hf⟩ := List.mem_map.1 hm
      exact (Prod.mk.inj hf).2.symm
    · have := hihs mi (List.mem_of_getElem? hmi)
      have hm : (h.field, h.binders) ∈ mi.ihs.map (fun h => (h.field, h.binders)) :=
        List.mem_map.2 ⟨h, hh, rfl⟩
      rw [this] at hm
      obtain ⟨f, hf, hf'⟩ := List.mem_map.1 hm
      rw [List.mem_range'_1] at hf
      have := (Prod.mk.inj hf').1
      omega
  refine ⟨rfl, hml, hlen, hfl, hsimple, indid, direct, fixDefName (mkRecName iv.name),
    binderNameOf x, hid, ?_,
    fun h => hd1 h, fun h h1 => hd2 h iv (.head _) h1, hss _ (by rw [hall]; exact .head _)⟩
  rw [recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.foldr_cons,
    List.foldr_nil, Nat.sub_self, Nat.zero_add]
  rw [hcs]
  congr 4
  refine innerS_congr fun c hc => ?_
  exact altF_simple _ ⟨iv.name, [x], indid, recCs minors⟩ rfl (hsimple c hc)

/-! ## λ□: the fixpoint with the minors substituted -/

/-- The body of the fixpoint under the major's λ, with the minors' erasures `ws` substituted and
the recursive call `fixv`. -/
def recBody (direct : Bool) (indid : InductiveId) (npars : Nat) (minors : List RecMinor)
    (ws : List LBTerm) (fixv : Nat → LBTerm) : LBTerm :=
  innerS direct indid npars (recCs minors) (altG (fun gi _ => ws.getD gi .box) fixv)

/-- The fixpoint with the minors' erasures substituted. -/
def recFIX (nm x : BinderName) (direct : Bool) (indid : InductiveId) (npars : Nat)
    (minors : List RecMinor) (ws : List LBTerm) : LBTerm :=
  .fix [⟨nm, .lambda x (recBody direct indid npars minors ws fun B => .bvar (B + 1)), 0⟩] 0

theorem recCs_fst {minors : List RecMinor} {c : Nat × RecMinor × ConstructorArgMask}
    (hc : c ∈ recCs minors) : c.1 < minors.length := by
  unfold recCs at hc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
  exact List.mem_range.1 hci

theorem simple_fields {minors : List RecMinor} (hs : ∀ c ∈ recCs minors, SimpleAlt c) :
    ∀ c ∈ recCs minors, ∀ h ∈ c.2.1.ihs, h.field < c.2.1.fields.length :=
  fun c hc h hh => ((hs c hc).2 h hh).2.2

theorem substl_recFix {N : Nat} {nm x : BinderName} {direct : Bool} {indid : InductiveId}
    {npars : Nat} {minors : List RecMinor} {ws : List LBTerm}
    (hs : ∀ c ∈ recCs minors, SimpleAlt c) (hN : minors.length = N) (hwl : ws.length = N)
    (hws : ∀ w ∈ ws, closedn 0 w = true) :
    substl ws.reverse (.fix [{ name := nm, principalArgIdx := 0, body := .lambda x (innerS direct
      indid npars (recCs minors)
      (altG (fun gi B => .bvar (B + 2 + (N - 1 - gi))) (fun B => .bvar (B + 1)))) }] 0) =
      recFIX nm x direct indid npars minors ws := by
  have hws' : ∀ u ∈ ws.reverse, closedn 0 u = true := fun u hu => hws u (List.mem_reverse.1 hu)
  unfold recFIX recBody
  rw [substl_fix1 nm x 0 ws.reverse, foldl_csubst_innerS _ _ _ _ 2 (by omega) (simple_fields hs)]
  congr 4
  refine innerS_congr fun c hc => ?_
  obtain ⟨gi, mi, mask⟩ := c
  have hgi := recCs_fst hc
  simp only [altG]
  congr 2
  · rw [show mi.fields.length + 2 + (N - 1 - gi) = (2 + mi.fields.length) + (N - 1 - gi) by omega,
      foldl_csubst_bvar _ _ _ hws']
    have hlt : N - 1 - gi < ws.reverse.length := by simp; omega
    rw [dif_pos hlt, List.getElem_reverse, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    try simp only [List.length_reverse]
    omega
  · exact foldl_csubst_bvar_lt (by omega) _

theorem closedn_getD {ws : List LBTerm} (hws : ∀ w ∈ ws, closedn 0 w = true) (i : Nat) :
    closedn 0 (ws.getD i .box) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => rfl
  | some w => exact hws w (List.mem_of_getElem? h)

/-- λ□'s `eval_fix` and `eval_beta` on the fixpoint: the major's value is substituted into the
body, the recursive calls are the fixpoint. -/
theorem eval_recFIX {nm x : BinderName} {direct : Bool} {indid : InductiveId} {npars : Nat}
    {minors : List RecMinor} {ws : List LBTerm} {maj' mb r : LBTerm}
    (hs : ∀ c ∈ recCs minors, SimpleAlt c) (hws : ∀ w ∈ ws, closedn 0 w = true)
    (hcl : closedn 0 (recFIX nm x direct indid npars minors ws) = true)
    (hmaj : LBEval defaultFlags lenv maj' mb)
    (h : LBEval defaultFlags lenv (innerSD direct indid npars (recCs minors)
      (altG (fun gi _ => ws.getD gi .box) fun _ => recFIX nm x direct indid npars minors ws) mb) r) :
    LBEval defaultFlags lenv (.app (recFIX nm x direct indid npars minors ws) maj') r := by
  refine .fix (mfix := [⟨nm, .lambda x (recBody direct indid npars minors ws fun B => .bvar (B + 1)),
    0⟩]) (idx := 0) (argsv := []) rfl (.atom rfl) hmaj rfl ?_
  show LBEval defaultFlags lenv (.app (.lambda x (csubst (recFIX nm x direct indid npars minors ws) 1
    (recBody direct indid npars minors ws fun B => .bvar (B + 1)))) mb) r
  refine .beta (.atom rfl) (LBEval.self hmaj) ?_
  unfold recBody
  rw [csubst_innerS _ _ _ _ _ _ 1 (by omega) (simple_fields hs)]
  rw [show innerS direct indid npars (recCs minors)
      (altG (fun c B => csubst (recFIX nm x direct indid npars minors ws) (1 + B) (ws.getD c .box))
        fun B => csubst (recFIX nm x direct indid npars minors ws) (1 + B) (.bvar (B + 1))) =
      innerS direct indid npars (recCs minors)
      (altG (fun gi _ => ws.getD gi .box) fun _ => recFIX nm x direct indid npars minors ws) by
    congr 1
    funext c
    obtain ⟨gi, mi, mask⟩ := c
    simp only [altG]
    congr 2
    · exact csubst_closedn _ _ 0 _ (closedn_getD hws gi) (Nat.zero_le _)
    · simp only [csubst]; rw [ite_eq_left (by omega)]]
  rwa [csubst0_innerS _ _ _ _ _ _ (fun c _ => closedn_getD hws c) (fun _ => hcl)
    (simple_fields hs)]

/-- The dependencies of the fixpoint's body give those of the minors' erasures. -/
theorem deps_recBody {direct : Bool} {indid : InductiveId} {npars : Nat} {minors : List RecMinor}
    {ws : List LBTerm} {fixv : Nat → LBTerm}
    (h : ErasesDeps E B σ lenv (recBody direct indid npars minors ws fixv)) :
    ∀ c ∈ recCs minors, ErasesDeps E B σ lenv (ws.getD c.1 .box) := by
  have hhead : ∀ (gi n : Nat) (fv : LBTerm) (ihs : List RecIH),
      ErasesDeps E B σ lenv (recAltS (ws.getD gi .box) n fv ihs) →
        ErasesDeps E B σ lenv (ws.getD gi .box) := fun gi B fv ihs h =>
    (ErasesDeps.mkApps_iff.1 h).1
  unfold recBody innerS at h
  split at h
  · rename_i c' hcs
    intro c hc
    rw [hcs] at hc
    obtain rfl := List.mem_singleton.1 hc
    obtain ⟨gi, mi, mask⟩ := c
    rw [foldl_app_eq_mkApps] at h
    have h1 := (ErasesDeps.mkApps_iff.1 h).1
    simp only [altG] at h1
    have : ∀ (xs : List BinderName) (b : LBTerm), ErasesDeps E B σ lenv (xs.foldr .lambda b) →
        ErasesDeps E B σ lenv b := by
      intro xs
      induction xs with
      | nil => exact fun _ h => h
      | cons x xs ih => intro b h; cases h with | lambda h => exact ih b h
    exact hhead _ _ _ _ (this _ _ h1)
  · cases h with
    | case _ _ _ hbrs =>
    intro c hc
    obtain ⟨gi, mi, mask⟩ := c
    exact hhead _ _ _ _ (hbrs _ (List.mem_map.2 ⟨_, hc, rfl⟩))

/-- The level of the major's inductive at the levels of a recursor application. -/
theorem rec_level (henv : ProgEnv P ζ E B) (hE : Metalean.EnvWF E) {iv : InductiveVal}
    (hiv : findDecl P iv.name = some (.inductInfo iv)) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} (hB : B iv.name = some (.ind η s))
    {us us' : List Level} {l : Metalean.Level lps.length} {ls : Fin ι.nlevels → Metalean.Level lps.length}
    (hRL : RecrLevels (E.get η).block lps us l us') (hTL : TrLevels lps us' ι.nlevels = some ls) :
    ∀ l₀, casesSortLevel iv us = some l₀ → TrLevel lps l₀ = some ((E.get η).block.level{ls}) := by
  intro l₀ hl₀
  simp only [casesSortLevel, Option.map_eq_some_iff] at hl₀
  obtain ⟨⟨k₀, u⟩, har, rfl⟩ := hl₀
  obtain ⟨a, hk, ha, -, hlv⟩ := SrcProof.ind_level henv hE hiv hB har
  obtain ⟨hlen, -⟩ := TrLevels_get hTL
  have hdrop : us.drop (us.length - iv.levelParams.length) = us' := by
    rcases hRL with ⟨-, u0, rfl, -⟩ | ⟨-, rfl, -⟩
    · simp only [List.length_cons, hlen, hk, Nat.add_sub_cancel_left, List.drop_one, List.tail_cons]
    · simp [hlen, hk]
  obtain ⟨ls', hls', hls'eq⟩ := SrcDefeq.trLevels_cast hTL hk
  rw [hdrop, hlv, TrLevel_instLevel hls' ha]
  congr 2
  funext i
  rw [hls'eq]

/-! ## Applying a head to values -/

/-- A value argument with a closed erasure that is a λ□ value. -/
def ArgOK (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) (σ : EvalEnv)
    (lenv : GlobalDeclarations) (f : Lean.Expr) (f' : LBTerm) : Prop :=
  SrcValue σ f ∧ Erases E B lps σ .nil [] f f' ∧ closedn 0 f' = true ∧ ErasesDeps E B σ lenv f' ∧
    LBEval defaultFlags lenv f' f'

/-- Values applied to an erased head: an erasure of the application whose λ□ evaluations are those
of the erased head applied to the values' erasures. -/
theorem appArgs (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) :
    ∀ {fs : List Lean.Expr} {fs₀ : List (Metalean.Expr ζ lps.length 0)},
      List.Forall₂ (TrM E B lps .nil []) fs fs₀ →
      ∀ {fs' : List LBTerm}, List.Forall₂ (ArgOK E B lps σ lenv) fs fs' →
      ∀ {F : Lean.Expr} {F' : LBTerm} {F₀ : Metalean.Expr ζ lps.length 0},
      Erases E B lps σ .nil [] F F' → ErasesDeps E B σ lenv F' → TrM E B lps .nil [] F F₀ →
      (∃ T, E[.nil] ⊢ F₀.appList fs₀ : T) →
      ∃ G', Erases E B lps σ .nil [] (mkAppN F fs.toArray) G' ∧ ErasesDeps E B σ lenv G' ∧
        ∀ r, LBEval defaultFlags lenv G' r → LBEval defaultFlags lenv (mkApps F' fs') r := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  intro fs fs₀ hfs
  induction hfs with
  | nil =>
    intro fs' hok' F F' F₀ hF hdF _ _
    cases hok'
    exact ⟨F', by rw [mkAppN_eq_foldl]; exact hF, hdF, fun _ h => h⟩
  | @cons f f₀ fs fs₀ hf₀ _ ih =>
    intro fs' hok' F F' F₀ hF hdF hF₀ hT
    cases hok' with
    | @cons _ f' _ fs' hfa hrest =>
    obtain ⟨T, hT⟩ := hT
    rw [Metalean.Expr.appList_cons] at hT
    obtain ⟨⟨G, hG⟩, -⟩ := InstPre.appList_inv hT
    obtain ⟨hval, herf, hcl, hdf, hself⟩ := hfa
    obtain ⟨G₁, hG₁, hdG₁, hevG₁⟩ :=
      SimIota.appArg_step henv hE hsub hF hdF hF₀ hf₀ hG hval herf hcl hdf hself
    obtain ⟨t₁, ht₁, hred₁⟩ := TrM.apps hF₀ (List.Forall₂.cons hf₀ .nil)
    rw [SimIota.mkAppN_single] at ht₁
    have hd₁ := WHRedS.defeq hE hok hred₁ (by simpa using hG)
    obtain ⟨T', hT'⟩ := SatTyped.appList_defeq hE hok fs₀ hd₁.symm hT
    obtain ⟨G', hG', hdG', hevG'⟩ := ih hrest hG₁ hdG₁ ht₁ ⟨T', hT'⟩
    refine ⟨G', by rw [SimIota.mkAppN_cons]; exact hG', hdG', fun r h => ?_⟩
    show LBEval defaultFlags lenv (mkApps (.app F' f') fs') r
    exact SimIota.lbeval_mkApps_congr _ hevG₁ (hevG' r h)

/-- A list with an entry for each index below `n`. -/
theorem choose_list {δ : Type} {Q : Nat → δ → Prop} (n : Nat) (h : ∀ i < n, ∃ d, Q i d) :
    ∃ ds : List δ, ds.length = n ∧ ∀ i d, ds[i]? = some d → Q i d := by
  refine ⟨List.ofFn fun i : Fin n => Classical.choose (h i i.isLt), by simp, fun i d hd => ?_⟩
  rw [List.getElem?_ofFn] at hd
  split at hd
  · rename_i hi
    cases hd
    exact Classical.choose_spec (h i hi)
  · cases hd

/-! ## The ι step -/

/-- The recursor ι with the minors' erasures substituted into the fixpoint: λ□ unfolds the fixpoint
on the major's value, selects the constructor's alternative and applies the minor's value to the
fields and the recursive calls; these are erasures of the source induction hypotheses, whose
values the continuation is applied to. -/
theorem rec_core (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors : List RecMinor} {maj mj : Expr} {k : Nat}
    {mi : RecMinor} {mk : Expr} {us : List Level} {v : Expr}
    {ps ms mins mvs fs rfs ihvs : List Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hps : ps.length = rv.numParams) (hms : ms.length = rv.numMotives)
    (hmins : mins.length = rv.numMinors) (hlm : mins.length = mvs.length)
    (hmv : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → SrcEval σ m mv)
    (hmaj : SrcEval σ maj mj) (hcv : CtorValue σ T mj k fs) (hmi : minors[k]? = some mi)
    (hmk : mvs[k]? = some mk) (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs)
    (hrl : rfs.length = ihvs.length)
    (hih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      SrcEval σ (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihmaj : ErasesSim E B lps σ lenv maj mj)
    (ihih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      ErasesSim E B lps σ lenv (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihv : ErasesSim E B lps σ lenv (mkAppN mk (fs ++ ihvs).toArray) v)
    {t T₀ : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) t)
    (ht : E[.nil] ⊢ t : T₀)
    {minors' : List RecMinor} {F : LBTerm} (hRF : RecFixOf E B σ rv us minors' F)
    {ws : List LBTerm} (hwl : mvs.length = ws.length)
    (hwe : ∀ (i : Nat) x x', mvs[i]? = some x → ws[i]? = some x' → Erases E B lps σ .nil [] x x')
    (hwc : ∀ w ∈ ws, closedn 0 w = true ∧ (∀ x, hasFVar x w = false) ∧ LBFixed w)
    (hdF : ErasesDeps E B σ lenv (substl ws.reverse F))
    {maj' : LBTerm} (hmaj' : Erases E B lps σ .nil [] maj maj')
    (hdmaj : ErasesDeps E B σ lenv maj') :
    ∃ vb, Erases E B lps σ .nil [] v vb ∧
      LBEval defaultFlags lenv (.app (substl ws.reverse F) maj') vb := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hRF₀ := hRF
  obtain ⟨hmm, hmlN, hmlC, hfl, hsimple, indid, direct, nm, x, hid, rfl, hd1, hd2, hss⟩ :=
    recFix_shape henv hsub hcr hall hcT hblk hni hshape hihs hRF₀
  subst minors'
  have hwscl : ∀ w ∈ ws, closedn 0 w = true := fun w hw => (hwc w hw).1
  have hFIX := substl_recFix (N := rv.numMinors) (nm := nm) (x := x) (direct := direct)
    (indid := indid) (npars := rv.numParams) hsimple hmlN (by omega) hwscl
  have hFcl : closedn 0 (recFIX nm x direct indid rv.numParams minors ws) = true := by
    rw [← hFIX]
    refine TargetLift.closedn_substl _ _ 0 (fun u hu => hwscl u (List.mem_reverse.1 hu)) ?_
    rw [List.length_reverse, Nat.zero_add, ← hwl, ← hlm, hmins]
    exact (RecLam.RecFixOf.closed hRF).2.1
  have hcvs := (RecWhred.recBlock?_single hall hblk).2
  obtain ⟨-, hcvl, -, -⟩ := RecWhred.rec_minors henv hsub hcr hall hcT hblk hni hshape
  have hRFr := hRF
  rw [hFIX] at hdF ⊢
  generalize hFX : recFIX nm x direct indid rv.numParams minors ws = FIX at hdF hFcl ⊢
  -- the block
  obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, rfl, rfl, rfl, hBT, hBc, hns, rfl⟩ :=
    RecWhred.rec_block henv hsub hcr hall hcT hblk
  obtain ⟨⟨_, _, _, _, hIB⟩, -⟩ := hb
  obtain ⟨-, -, -, -, -, -, hRnp, hRnm, hRmin, hRni⟩ := hIB.recr s
  obtain ⟨-, -, -, hInp, -, -, -, -⟩ := hIB.ind s
  have hs0 : s.val = 0 := by have := s.isLt; omega
  have hnis : ι.nindices s = 0 := by rw [← hRni, hni]
  have hidO : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) mo,
      ((List.ofFn fun t => List.ofFn fun c => orders t c)[t.val]?.bind (·[c.val]?)) = some mo →
      mo = List.range ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) := by
    intro t c mo h
    simp only [List.getElem?_ofFn, t.isLt, c.isLt, ↓reduceDIte, Option.bind_some,
      Option.some.injEq] at h
    subst h
    obtain rfl : s = t := Fin.ext (by have := t.isLt; have := s.isLt; omega)
    exact RecWhred.orders_identity hIB s hns hshape hihs c
  -- the major's erasure evaluates to an erasure of its value
  obtain ⟨bs', hlenb, hargs, hsat⟩ := TrM.special_inv hBc rfl he
  have htyb := RecWhred.satTr_recr_typed hE hok hsat ht hidO
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, bs'[(ps ++ ms ++ mins).length]? = some m₀ :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlenb]; simp)⟩
  have hmT := hargs _ maj m₀ (by simp) hm₀
  obtain ⟨M, hM⟩ := htyb m₀ (List.mem_of_getElem? hm₀)
  obtain ⟨mb, hmb, hevmb⟩ := ihmaj hmT ⟨M, hM⟩ hmaj' hdmaj
  -- the spine at the values of the minors and of the major
  have srefl : ∀ x, SrcDefeq.Sound E B lps x x := fun _ _ _ he ht => ⟨_, he, ht⟩
  have hself : ∀ l : List Expr, List.Forall₂ (SrcDefeq.Sound E B lps) l l := fun l =>
    List.forall₂_same.2 fun x _ => srefl x
  have hall' : List.Forall₂ (SrcDefeq.Sound E B lps) (ps ++ ms ++ mins ++ [maj])
      (ps ++ ms ++ mvs ++ [mj]) :=
    List.rel_append (List.rel_append (List.rel_append (hself ps) (hself ms))
      (CasesWhred.forall₂_of_getElem? hlm fun i m mv h1 h2 => by
        intro _ _ he ht; exact SrcEval.defeq henv hE hsub he ht (hmv i m mv h1 h2)))
      (.cons (by intro _ _ he ht; exact SrcEval.defeq henv hE hsub he ht hmaj) .nil)
  obtain ⟨t₂, ht₂, hd₂⟩ := SrcDefeq.special_congr hE hBc rfl he ht
    (fun hsat => RecWhred.satTr_recr_typed hE hok hsat ht hidO) hall'
  have ht₂T := hd₂.right
  -- ι in Metalean
  obtain ⟨a₁, fs₀, ihs₀, ha₁, hfs₀, hihs₀, hred⟩ := RecWhred.recIota_whred henv hsub hcr hall hcT
    hblk hni hshape hihs hps hms (hlm ▸ hmins) hcv hmi hmk hrfs ht₂
  have hd₃ := WHRedS.defeq hE hok hred ht₂T
  obtain ⟨-, htyped⟩ := InstPre.appList_inv hd₃.right
  -- the major's value in the recursor node
  have hlen₂ : (ps ++ ms ++ mvs ++ [mj]).length = ι.recrEnd s := by
    show _ = ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1
    simp only [List.length_append, List.length_singleton, hps, hms, ← hlm, hmins, hRnp, hRnm,
      hRmin, CasesWhred.fin_sum_eq, hnis]
  obtain ⟨ls, l, mo, A, minsM, hA, -, -, rfl, us₂, hRL, hTL⟩ := CasesWhred.trM_recr_inv hBc hlen₂ ht₂
  obtain ⟨-, hps₀, -, -, his₀, hmajT⟩ := Defeq.recr_typed hE hok ht₂T
  have hpre : (ps ++ ms ++ mvs).length = ι.recrEnd s - 1 := by
    simp only [List.length_append, List.length_singleton] at hlen₂ ⊢; omega
  obtain ⟨a₀, ha₀, htr₀⟩ := hA (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve
  have hlast : ((Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve).val =
      ι.recrEnd s - 1 := rfl
  rw [hlast, ← hpre, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at ha₀
  cases ha₀
  have hfields := SimIota.fields_of_eval hmaj hcv
  have hcv₀ := hcv
  obtain ⟨C, usC, cv, psC, hC, hind, hcidx, hpsC, hfsC, rfl⟩ := hcv
  have hlenC : (psC ++ fs).length = cv.numParams + cv.numFields := by simp [hpsC, hfsC]
  obtain ⟨ι', η', s', c', lsC, psN, fds, rfsN, hBC, hnode⟩ :=
    SimInd.ctorNode_tr henv hsub hC hlenC htr₀
  rw [hind, hBT] at hBC
  cases hBC
  rw [hnode] at hmajT htr₀
  -- the dependencies of the minors' erasures
  have hdF' := hdF
  rw [← hFX] at hdF'
  have hdbody : ErasesDeps E B σ lenv (recBody direct indid (Rs s).numParams minors ws
      fun B => .bvar (B + 1)) := by
    cases hdF' with
    | fix hd =>
      have := hd _ (.head _)
      cases this with
      | lambda hb => exact hb
  have hdws := deps_recBody hdbody
  have hkm : k < minors.length := (List.getElem?_eq_some_iff.mp hmi).1
  have hkc : (k, mi, Array.replicate mi.fields.length ConstructorArgRelevance.keep) ∈
      recCs minors := by
    unfold recCs
    refine List.mem_map.2 ⟨k, List.mem_range.2 hkm, ?_⟩
    rw [List.getD_eq_getElem?_getD, hmi, Option.getD_some]
  have hwk : ws.getD k .box = ws[k]'(by omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hmkw : Erases E B lps σ .nil [] mk (ws.getD k .box) := by
    rw [hwk]; exact hwe k mk _ hmk (List.getElem?_eq_getElem _)
  have hdwk : ErasesDeps E B σ lenv (ws.getD k .box) := hdws _ hkc
  -- the constructor's minor binds its fields
  obtain ⟨hCi, hnpI⟩ := SimInd.ctor_block henv hsub hC (by rw [hind]; exact (RecWhred.recBlock?_single hall hblk).1)
  rw [hcidx] at hCi
  have hmif : mi.fields.length = fs.length := by
    obtain ⟨-, hcget⟩ := RecWhred.mapM_get hcvs
    obtain ⟨cv', hcv', hcvd⟩ := hcget k C hCi
    unfold EvalEnv.ctorOf? at hcvd
    rw [hC] at hcvd
    cases hcvd
    obtain ⟨mi', hmi', hmf⟩ := hfl k cv hcv'
    rw [hmi] at hmi'
    cases hmi'
    rw [hmf, hfsC]
  -- the continuation, given erasures of the fields
  have htail : ∀ fs' : List LBTerm, List.Forall₂ (ArgOK E B lps σ lenv) fs fs' →
      ∃ vb, Erases E B lps σ .nil [] v vb ∧ LBEval defaultFlags lenv
        (mkApps (ws.getD k .box) (fs' ++ mi.ihs.map fun h => .app FIX (fs'.getD h.field .box))) vb := by
    intro fs' hfa
    obtain ⟨hrlen, hrget⟩ := RecWhred.mapM_get hrfs
    have hdg : ∀ j, ErasesDeps E B σ lenv (fs'.getD j .box) := by
      intro j
      rw [List.getD_eq_getElem?_getD]
      cases hj : fs'[j]? with
      | none => exact .box
      | some f' =>
        exact SimIota.forall₂_right (fun _ _ h => h.2.2.2.1) hfa f' (List.mem_of_getElem? hj)
    -- the induction hypotheses' erasures
    have hIHer : ∀ (i : Nat) h rf, mi.ihs[i]? = some h → rfs[i]? = some rf →
        Erases E B lps σ .nil [] (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [rf]).toArray)
          (.app FIX (fs'.getD h.field .box)) := by
      intro i h rf hh hrf
      obtain ⟨y, hy, hfy⟩ := hrget i h hh
      rw [hrf] at hy
      cases hy
      obtain ⟨f', hf', hok'⟩ := CasesWhred.forall₂_getElem? hfa hfy
      have hfd : fs'.getD h.field .box = f' := by
        rw [List.getD_eq_getElem?_getD, hf', Option.getD_some]
      have h1 := Erases.recFix (ps := ps) (ms := ms) (mins := mvs) (is := []) (extra := [])
        (is' := []) (extra' := []) (maj := rf) (maj' := f') hcr hRFr hps hms (hlm ▸ hmins)
        hni.symm hwl hwe hwc rfl (fun _ _ _ h => by simp at h) hok'.2.1 rfl
        (fun _ _ _ h => by simp at h)
      simp only [List.append_nil, List.nil_append] at h1
      rw [hFIX, hFX] at h1
      rw [hfd]
      exact h1
    have hIH : ∀ i < ihvs.length, ∃ d : LBTerm × Metalean.Expr ζ lps.length 0,
        ∃ h rf w ih0, mi.ihs[i]? = some h ∧ rfs[i]? = some rf ∧ ihvs[i]? = some w ∧
          ihs₀[i]? = some ih0 ∧ Erases E B lps σ .nil [] w d.1 ∧
          LBEval defaultFlags lenv (.app FIX (fs'.getD h.field .box)) d.1 ∧
          TrM E B lps .nil [] w d.2 ∧ (∃ A, E[.nil] ⊢ ih0 ≡ d.2 : A) := by
      intro i hi
      obtain ⟨h, hh⟩ : ∃ h, mi.ihs[i]? = some h :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨rf, hrf⟩ : ∃ rf, rfs[i]? = some rf := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨w, hw⟩ : ∃ w, ihvs[i]? = some w := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨ih0, hih0, hTr⟩ := CasesWhred.forall₂_getElem? hihs₀
        (i := i) (a := mkAppN (.const c us) (ps ++ ms ++ mvs ++ [rf]).toArray)
        (by rw [List.getElem?_map, hrf]; rfl)
      obtain ⟨A, hA⟩ := htyped ih0 (List.mem_append_right _ (List.mem_of_getElem? hih0))
      obtain ⟨vb, hvb, hev⟩ := ihih i rf w hrf hw hTr ⟨A, hA⟩ (hIHer i h rf hh hrf)
        (.app hdF (hdg _))
      obtain ⟨ihv0, hTrw, hdd⟩ := SrcEval.defeq henv hE hsub hTr hA (hih i rf w hrf hw)
      exact ⟨(vb, ihv0), h, rf, w, ih0, hh, hrf, hw, hih0, hvb, hev, hTrw, ⟨A, hdd⟩⟩
    obtain ⟨ds, hdsl, hds⟩ := choose_list _ hIH
    have hlv : ihvs.length = (ds.map Prod.fst).length := by simp [hdsl]
    have hlv₂ : ihvs.length = (ds.map Prod.snd).length := by simp [hdsl]
    have hget : ∀ i (d : LBTerm × Metalean.Expr ζ lps.length 0), ds[i]? = some d →
        ∃ (h : RecIH) (rf w : Lean.Expr) (ih0 : Metalean.Expr ζ lps.length 0),
        mi.ihs[i]? = some h ∧ rfs[i]? = some rf ∧
        ihvs[i]? = some w ∧ ihs₀[i]? = some ih0 ∧ Erases E B lps σ .nil [] w d.1 ∧
        LBEval defaultFlags lenv (.app FIX (fs'.getD h.field .box)) d.1 ∧
        TrM E B lps .nil [] w d.2 ∧ (∃ A, E[.nil] ⊢ ih0 ≡ d.2 : A) := hds
    have hmap : ∀ {γ : Type} (g : LBTerm × Metalean.Expr ζ lps.length 0 → γ) (i : Nat) (y : γ),
        (ds.map g)[i]? = some y → ∃ d, ds[i]? = some d ∧ g d = y := by
      intro γ g i y hy
      rw [List.getElem?_map] at hy
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hy
      exact ⟨d, hd, rfl⟩
    have hTrs : List.Forall₂ (TrM E B lps .nil []) ihvs (ds.map Prod.snd) :=
      CasesWhred.forall₂_of_getElem? hlv₂ fun i w y hw hy => by
        obtain ⟨d, hd, rfl⟩ := hmap _ i y hy
        obtain ⟨_, _, w', _, _, _, hw', _, _, _, hT, _⟩ := hget i d hd
        rw [hw] at hw'; cases hw'; exact hT
    have hlen₀ : ihs₀.length = ihvs.length := by
      rw [← hihs₀.length_eq, List.length_map, hrl]
    have hDC : List.Forall₂ (DCong E False .nil .nil) ihs₀ (ds.map Prod.snd) :=
      CasesWhred.forall₂_of_getElem? (by rw [hlen₀, hlv₂]) fun i a y ha hy => by
        obtain ⟨d, hd, rfl⟩ := hmap _ i y hy
        obtain ⟨_, _, _, ih0, _, _, _, hih0, _, _, _, ⟨A, hdd⟩⟩ := hget i d hd
        rw [ha] at hih0; cases hih0; exact .leaf hdd
    have hOK : List.Forall₂ (ArgOK E B lps σ lenv) ihvs (ds.map Prod.fst) :=
      CasesWhred.forall₂_of_getElem? hlv fun i w y hw hy => by
        obtain ⟨d, hd, rfl⟩ := hmap _ i y hy
        obtain ⟨h, rf, w', _, _, hrf, hw', _, hvb, hev, hT, _⟩ := hget i d hd
        rw [hw] at hw'; cases hw'
        exact ⟨SrcEval.value (hih i rf w hrf hw), hvb, SimCases.closed0 hT hvb,
          ErasesDeps.eval (.app hdF (hdg _)) hev, LBEval.self hev⟩
    have hrep : List.Forall₂ (fun b c => LBEval defaultFlags lenv b c ∧ LBFixed c)
        (mi.ihs.map fun h => .app FIX (fs'.getD h.field .box)) (ds.map Prod.fst) :=
      CasesWhred.forall₂_of_getElem? (by rw [List.length_map, ← hlv, ← hrl, hrlen])
        fun i b y hb hy => by
        obtain ⟨d, hd, rfl⟩ := hmap _ i y hy
        obtain ⟨h, _, _, _, hh, _, _, _, _, hev, _, _⟩ := hget i d hd
        rw [List.getElem?_map, hh] at hb
        cases hb
        exact ⟨hev, LBEval.fixed hev⟩
    -- the continuation's translation
    have hcong : List.Forall₂ (DCong E False .nil .nil) (fs₀ ++ ihs₀) (fs₀ ++ ds.map Prod.snd) :=
      List.rel_append (List.forall₂_same.mpr fun x _ => DCong.refl) hDC
    have h1 := DCong.defeq hE not_false
      (TrDet.appList .refl hcong.length_eq (forall₂_getElem? hcong)) hok
      (DCong.CtxConv.refl hok) hd₃.right
    obtain ⟨G', hG', hdG', hevG'⟩ := appArgs henv hE hsub (List.rel_append hfs₀ hTrs)
      (List.rel_append hfa hOK) hmkw hdwk ha₁ ⟨_, h1.right⟩
    obtain ⟨t₄, ht₄, hred₄⟩ := TrM.apps ha₁ (List.rel_append hfs₀ hTrs)
    have hd₄ := WHRedS.defeq hE hok hred₄ h1.right
    obtain ⟨vb, hvb, hevb⟩ := ihv ht₄ ⟨_, hd₄.right⟩ hG' hdG'
    exact ⟨vb, hvb, eval_args_replace hrep fs' vb (hevG' vb hevb)⟩
  subst hFX
  have hcsl : (recCs minors).length = minors.length := by simp [recCs]
  have hnc : (Is s).ctors.length = ι.nctors s := by
    rw [(hIB.ind s).2.2.2.2.2.1, List.length_ofFn]
  by_cases hdir : direct = true ∧ (Is s).ctors.length = 1
  · -- the reduced form: the alternative applied to `□` for each field
    obtain ⟨hdt, h1⟩ := hdir
    subst hdt
    have hfe := SimIota.fields_erasable henv hE hsub hC hpsC hfsC htr₀ hmajT
      (by rw [hind]; exact hd2 rfl h1)
    have hfa : List.Forall₂ (ArgOK E B lps σ lenv) fs (List.replicate fs.length .box) :=
      CasesWhred.forall₂_of_getElem? (by simp) fun i f f' hf hf' => by
        rw [List.getElem?_replicate] at hf'
        split at hf' <;> cases hf'
        exact ⟨(hfields f (List.mem_of_getElem? hf)).1, .box (hfe f (List.mem_of_getElem? hf)), rfl,
          .box, .atom rfl⟩
    obtain ⟨vb, hvb, hev⟩ := htail _ hfa
    refine ⟨vb, hvb, eval_recFIX hsimple hwscl hFcl hevmb ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨c0, hc0⟩ : ∃ c0, recCs minors = [c0] :=
      List.length_eq_one_iff.1 (by rw [hcsl]; omega)
    have hc0' : c0 = (0, mi, Array.replicate mi.fields.length ConstructorArgRelevance.keep) := by
      rw [hc0] at hkc; exact (List.mem_singleton.1 hkc).symm
    subst hc0'
    rw [hc0]
    simp only [innerSD, altG, length_altNames]
    rw [foldl_app_eq_mkApps, ← length_altNames]
    refine eval_lams_boxes _ _ _ ?_
    have hus : ∀ u ∈ List.replicate fs.length LBTerm.box, closedn 0 u = true := fun u hu => by
      rw [List.eq_of_mem_replicate hu]; rfl
    have := substl_recAltS (closedn_getD hwscl 0) hFcl hus mi.ihs (by
      intro h hh; rw [List.length_replicate, ← hmif]
      exact ((hsimple _ (hc0 ▸ List.mem_singleton_self _)).2 h hh).2.2)
    rw [List.reverse_replicate, List.length_replicate] at this
    rw [length_altNames, hmif, this]
    exact hev
  · -- a λ□ `case` on the major's value
    have hnz : (E.get η).block.level{ls} ≠ .zero := by
      intro hz
      by_cases hdt : direct = true
      · have h1 : (Is s).ctors.length ≠ 1 := fun h => hdir ⟨hdt, h⟩
        have hind' := Defeq.indDF hps₀ his₀
        rw [hz] at hind'
        have hprf : IsProof E .nil (.ctor η s c' lsC psN fds rfsN) := ⟨_, hmajT, hind'⟩
        have := (hss ι η s hBT .nil c' lsC psN fds rfsN hE hok hprf).1
        have : k < (Is s).ctors.length := by omega
        omega
      · obtain ⟨l₀, hl₀, hnz₀⟩ := hd1 (by simpa using hdt)
        have hlev := rec_level henv hE (SrcDefeq.findDecl_sub hsub
          (RecWhred.recBlock?_single hall hblk).1) hBT hRL hTL l₀ hl₀
        have := SimInd.isNeverZero_tr hnz₀ hlev (fun _ => 0)
        rw [hz, Metalean.Level.eval_zero] at this
        omega
    rcases Erases.ctor_inv hC (by omega) hmb with ⟨rfl, hbx⟩ | ⟨iid, as', hid', rfl, hlen', hallE⟩
    · exfalso
      obtain ⟨w, hw, Tw, hwT, hwA⟩ := hbx
      exact SimIota.ind_not_erasable hE hmajT hnz
        (RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE hw htr₀ hwT hmajT) hwA)
    rw [hind, hid] at hid'
    cases hid'
    -- the λ□ inductive
    obtain ⟨T₁, hidT, hindT⟩ : ∃ T₁, IndIdOf σ T₁ = some indid ∧ ErasesInd E B σ lenv T₁ := by
      have hb := hdbody
      unfold recBody innerS at hb
      split at hb
      · rename_i c₁ hcs₁
        exact absurd ⟨rfl, by rw [← hmlC, ← hcsl, hcs₁]; rfl⟩ hdir
      · cases hb with
        | case hidT hindT _ _ => exact ⟨_, hidT, hindT⟩
    rw [SimInd.indIdOf_inj hbinj hidT hid] at hindT
    have hnp : ¬ PropInductive E B cv.induct := fun hp =>
      SimInd.mkApps_construct_ne_box (Erases.ctorProp_box hC hp (by omega) hmb)
    obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, hprop⟩ :=
      SimInd.lookupCtor_of henv hsub hC (by rw [hind]; exact hid) (by rw [hind]; exact hindT)
    have hpf : ob.propositional = false := by
      cases h : ob.propositional
      · rfl
      · exact absurd (hprop.mp h) hnp
    have hnpR : (Rs s).numParams = cv.numParams := by rw [hRnp, ← hInp, hnpI]
    -- the fields
    have hdmb := ErasesDeps.eval hdmaj hevmb
    obtain ⟨-, hdargs⟩ := SimInd.deps_mkApps hdmb
    have hfs' : (as'.drop cv.numParams).length = fs.length := by simp; omega
    have hfa : List.Forall₂ (ArgOK E B lps σ lenv) fs (as'.drop cv.numParams) := by
      refine CasesWhred.forall₂_of_getElem? hfs'.symm fun j f f' hf hf' => ?_
      have hf'' : as'[cv.numParams + j]? = some f' := by
        rw [List.getElem?_drop] at hf'; exact hf'
      have hpf' : (psC ++ fs)[cv.numParams + j]? = some f := by
        rw [List.getElem?_append_right (by omega), hpsC, Nat.add_sub_cancel_left]; exact hf
      have herf := hallE _ _ _ hpf' hf''
      obtain ⟨f₀, hf₀, hff₀⟩ := CasesWhred.forall₂_getElem? hfs₀ hf
      have hmem : f' ∈ as' := List.mem_of_getElem? hf''
      exact ⟨(hfields f (List.mem_of_getElem? hf)).1, herf, SimCases.closed0 hff₀ herf,
        hdargs f' hmem, construct_args_self hevmb rfl f' hmem⟩
    obtain ⟨vb, hvb, hev⟩ := htail _ hfa
    refine ⟨vb, hvb, eval_recFIX hsimple hwscl hFcl hevmb ?_⟩
    have hcase : innerSD direct indid (Rs s).numParams (recCs minors)
        (altG (fun gi _ => ws.getD gi .box) fun _ =>
          recFIX nm x direct indid (Rs s).numParams minors ws)
        (mkApps (.construct indid cv.cidx []) as') =
        .case (indid, (Rs s).numParams) (mkApps (.construct indid cv.cidx []) as')
          ((recCs minors).map (altG (fun gi _ => ws.getD gi .box) fun _ =>
            recFIX nm x direct indid (Rs s).numParams minors ws)) := by
      unfold innerSD
      split
      · rename_i c₁ hcs₁
        exact absurd ⟨rfl, by rw [← hmlC, ← hcsl, hcs₁]; rfl⟩ hdir
      · rfl
    rw [hcase]
    have hbr : ((recCs minors).map (altG (fun gi _ => ws.getD gi .box) fun _ =>
        recFIX nm x direct indid (Rs s).numParams minors ws))[cv.cidx]? =
        some (altNames mi, recAltS (ws.getD k .box) mi.fields.length
          (recFIX nm x direct indid (Rs s).numParams minors ws) mi.ihs) := by
      rw [List.getElem?_map, hcidx]
      unfold recCs
      rw [List.getElem?_map, List.getElem?_range hkm, Option.map_some, Option.map_some,
        List.getD_eq_getElem?_getD, hmi, Option.getD_some]
      rfl
    refine .iota (args := as') (cdecl := cb) rfl (LBEval.self hevmb) ?_ hbr ?_ ?_ ?_
    · show (lookupCtor lenv indid cv.cidx).map _ = _
      rw [hlk]
      simp [hpf, hnpars, hnpR]
    · rw [← hlen', hlenC, hnpR, hnargs]
    · rw [hnpR, hfs', length_altNames, hmif]
    · show LBEval defaultFlags lenv (substl (as'.drop (Rs s).numParams).reverse
        (recAltS (ws.getD k .box) mi.fields.length
          (recFIX nm x direct indid (Rs s).numParams minors ws) mi.ihs)) vb
      have hdrop : as'.drop (Rs s).numParams = as'.drop cv.numParams := by rw [hnpR]
      rw [hdrop]
      have hus : ∀ u ∈ as'.drop cv.numParams, closedn 0 u = true :=
        SimIota.forall₂_right (fun _ _ h => h.2.2.1) hfa
      have := substl_recAltS (closedn_getD hwscl k) hFcl hus mi.ihs (by
        intro h hh; rw [hfs', ← hmif]
        exact ((hsimple _ hkc).2 h hh).2.2)
      rw [← hfs'.trans hmif.symm, this]
      exact hev

/-! ## The `recIota` case -/

theorem kfv_of_fvarsIn {p : FVarId → Prop} : ∀ {e : Lean.Expr}, FVarsIn p e → Steps.KFV p e
  | .fvar _, h => h
  | .app f a, h => ⟨kfv_of_fvarsIn (e := f) h.1, kfv_of_fvarsIn (e := a) h.2⟩
  | .lam _ _ b _, h => kfv_of_fvarsIn (e := b) h.2
  | .letE _ _ v b _, h => ⟨kfv_of_fvarsIn (e := v) h.2.1, kfv_of_fvarsIn (e := b) h.2.2⟩
  | .mdata _ e, h => kfv_of_fvarsIn (e := e) h
  | .proj _ _ e, h => kfv_of_fvarsIn (e := e) h
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .forallE _ _ _ _, _ | .lit _, _ | .mvar _, _ => trivial

/-- An erasure of a term with a translation in the empty context has no free variable. -/
theorem noFVar_of_tr {e : Lean.Expr} {t : Metalean.Expr ζ lps.length 0} {tb : LBTerm}
    (he : TrM E B lps .nil [] e t) (h : Erases E B lps σ .nil [] e tb) :
    ∀ x, hasFVar x tb = false := by
  intro x
  cases hx : hasFVar x tb
  · rfl
  · have := Steps.Erases.hasFVar_of h _ (kfv_of_fvarsIn he.fvarsIn) x hx
    simp [MLCtx.findF] at this

/-- A recursor spine split as `Erases.recLet` and `Erases.recFix` read it, without indices. -/
theorem spine_split {ps ms mins ps' ms' mins' is extra : List Lean.Expr} {maj maj' : Lean.Expr}
    (h : ps ++ ms ++ mins ++ [maj] = ps' ++ ms' ++ mins' ++ is ++ [maj'] ++ extra)
    (h1 : ps.length = ps'.length) (h2 : ms.length = ms'.length) (h3 : mins.length = mins'.length)
    (h4 : is.length = 0) :
    ps = ps' ∧ ms = ms' ∧ mins = mins' ∧ is = [] ∧ maj = maj' ∧ extra = [] := by
  obtain rfl := List.eq_nil_of_length_eq_zero h4
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_singleton, List.length_nil] at hl
  obtain rfl : extra = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.append_nil] at h
  obtain ⟨h5, h6⟩ := List.append_inj h (by simp; omega)
  obtain ⟨h7, h8⟩ := List.append_inj h5 (by simp; omega)
  obtain ⟨h9, h10⟩ := List.append_inj h7 h1
  simp only [List.cons.injEq, and_true] at h6
  exact ⟨h9, h10, h8, rfl, h6, rfl⟩

/-- Typed translations of the arguments of a typed recursor spine. -/
theorem rec_args (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors : List RecMinor} {us : List Level} {as : List Lean.Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs))
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    {t T₀ : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (mkAppN (.const c us) as.toArray) t) (ht : E[.nil] ⊢ t : T₀) :
    ∀ (i : Nat) a, as[i]? = some a → ∃ (a₀ A : Metalean.Expr ζ lps.length 0),
      TrM E B lps .nil [] a a₀ ∧ E[.nil] ⊢ a₀ : A := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, rfl, rfl, rfl, -, hBc, hns, rfl⟩ :=
    RecWhred.rec_block henv hsub hcr hall hcT hblk
  obtain ⟨⟨_, _, _, _, hIB⟩, -⟩ := hb
  have hidO : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) mo,
      ((List.ofFn fun t => List.ofFn fun c => orders t c)[t.val]?.bind (·[c.val]?)) = some mo →
      mo = List.range ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) := by
    intro t c mo h
    simp only [List.getElem?_ofFn, t.isLt, c.isLt, ↓reduceDIte, Option.bind_some,
      Option.some.injEq] at h
    subst h
    obtain rfl : s = t := Fin.ext (by have := t.isLt; have := s.isLt; omega)
    exact RecWhred.orders_identity hIB s hns hshape hihs c
  obtain ⟨bs', hlenb, hargs, hsat⟩ := TrM.special_inv hBc rfl he
  have htyb := RecWhred.satTr_recr_typed hE hok hsat ht hidO
  intro i a ha
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, bs'[i]? = some a₀ :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlenb]; exact (List.getElem?_eq_some_iff.mp ha).1)⟩
  obtain ⟨A, hA⟩ := htyb a₀ (List.mem_of_getElem? ha₀)
  exact ⟨a₀, A, hargs i a a₀ ha ha₀, hA⟩

/-- The dependencies of a chain of `let`s. -/
theorem deps_letChain : ∀ {ms : List (LBTerm × RecMinor)} {b : LBTerm},
    ErasesDeps E B σ lenv (letChain ms b) →
      (∀ p ∈ ms, ErasesDeps E B σ lenv p.1) ∧ ErasesDeps E B σ lenv b
  | [], _, h => ⟨by simp, h⟩
  | (m, mi) :: ms, b, h => by
    cases h with
    | letIn hv hb =>
      obtain ⟨h1, h2⟩ := deps_letChain hb
      refine ⟨fun p hp => ?_, h2⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hv
      · exact h1 p hp

/-- A closed argument is left by closed substitutions. -/
theorem substl_app_closed {a : LBTerm} (ha : closedn 0 a = true) :
    ∀ (us : List LBTerm) (f : LBTerm), substl us (.app f a) = .app (substl us f) a
  | [], _ => rfl
  | u :: us, f => by
    show substl us (.app (csubst u 0 f) (csubst u 0 a)) = _
    rw [csubst_closedn u a 0 0 ha (Nat.le_refl _), substl_app_closed ha us]
    rfl

/-- The `recIota` case of `erases_correct`. The erasure is `□`, or the fixpoint under `let`s of
the erased minors, which λ□ evaluates to the minors' values, or the fixpoint with erasures of the
minors substituted, which are λ□ values, hence erasures of the minors' values; then
`SimRec.rec_core`. Reference: none (MetaRocq has no recursors; DV-30). -/
theorem erases_correct_recIota (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors : List RecMinor} {maj mj : Expr} {k : Nat}
    {mi : RecMinor} {mk : Expr} {us : List Level} {v : Expr}
    {ps ms mins mvs fs rfs ihvs : List Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hps : ps.length = rv.numParams) (hms : ms.length = rv.numMotives)
    (hmins : mins.length = rv.numMinors) (hlm : mins.length = mvs.length)
    (hmv : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → SrcEval σ m mv)
    (hmaj : SrcEval σ maj mj) (hcv : CtorValue σ T mj k fs) (hmi : minors[k]? = some mi)
    (hmk : mvs[k]? = some mk) (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs)
    (hrl : rfs.length = ihvs.length)
    (hih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      SrcEval σ (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (hv : SrcEval σ (mkAppN mk (fs ++ ihvs).toArray) v)
    (ihm : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → ErasesSim E B lps σ lenv m mv)
    (ihmaj : ErasesSim E B lps σ lenv maj mj)
    (ihih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      ErasesSim E B lps σ lenv (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihv : ErasesSim E B lps σ lenv (mkAppN mk (fs ++ ihvs).toArray) v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v := by
  intro t tb he ⟨T₀, ht⟩ her hdeps
  have hsrc : SrcEval σ (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v :=
    .recIota hcr hall hcT hblk hni hshape hihs hps hms hmins hlm hmv hmaj hcv hmi hmk hrfs hrl hih hv
  have hargs := rec_args henv hE hsub hcr hall hcT hblk hshape hihs he ht
  have hminT : ∀ (i : Nat) m, mins[i]? = some m → ∃ (a₀ A : Metalean.Expr ζ lps.length 0),
      TrM E B lps .nil [] m a₀ ∧ E[.nil] ⊢ a₀ : A := fun i m h =>
    hargs ((ps ++ ms).length + i) m (by
      have hi := (List.getElem?_eq_some_iff.mp h).1
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp),
        Nat.add_sub_cancel_left]
      exact h)
  have hmajT : ∃ (a₀ A : Metalean.Expr ζ lps.length 0), TrM E B lps .nil [] maj a₀ ∧
      E[.nil] ⊢ a₀ : A := hargs (ps ++ ms ++ mins).length maj (by simp)
  -- the minors' values with closed erasures that are λ□ values
  have hvalue : ∀ (i : Nat) m mv w, mins[i]? = some m → mvs[i]? = some mv →
      Erases E B lps σ .nil [] mv w → closedn 0 w = true ∧ (∀ x, hasFVar x w = false) := by
    intro i m mv w h1 h2 hw
    obtain ⟨a₀, A, hTr, hA⟩ := hminT i m h1
    obtain ⟨mv₀, hmv₀, -⟩ := SrcEval.defeq henv hE hsub hTr hA (hmv i m mv h1 h2)
    exact ⟨SimCases.closed0 hmv₀ hw, noFVar_of_tr hmv₀ hw⟩
  rcases Erases.rec_inv hcr her with ⟨rfl, hbx⟩ |
    ⟨minors', F, ps', ms', mins', is, maj', extra, minsE, is', majE, extra', hRF, has, hps', hms',
      hmins', his, hlmE, hminE, hli, -, hmajE, hle, -, rfl⟩ |
    ⟨minors', F, ps', ms', mins', is, maj', extra, ws, is', majE, extra', hRF, has, hps', hms',
      hmins', his, hlw, hwE, hws, hli, -, hmajE, hle, -, rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  · -- the fixpoint under `let`s of the erased minors
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      spine_split has (by omega) (by omega) (by omega) (by omega)
    obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by simpa using hli.symm)
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hle.symm)
    have hclE : ∀ (i : Nat) m m', mins[i]? = some m → minsE[i]? = some m' → closedn 0 m' = true :=
      fun i m m' h1 h2 => by
        obtain ⟨a₀, A, hTr, -⟩ := hminT i m h1
        exact SimCases.closed0 hTr (hminE i m m' h1 h2)
    have hclZ : ∀ p ∈ minsE.zip minors', closedn 0 p.1 = true := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      simp only [List.getElem_zip]
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m :=
        ⟨_, List.getElem?_eq_getElem (by simp at hi; omega)⟩
      exact hclE i m _ hm (List.getElem?_eq_getElem _)
    obtain ⟨a₀, A, hTm, hAm⟩ := hmajT
    have hclmaj : closedn 0 majE = true := SimCases.closed0 hTm hmajE
    simp only [List.nil_append, List.map_cons, List.map_nil, mkApps] at hdeps ⊢
    rw [RecLam.recLets_closed _ 0 _ hclZ, TargetLift.lbLift_closedn _ _ 0 hclmaj] at hdeps ⊢
    obtain ⟨hdZ, hdb⟩ := deps_letChain (ms := minsE.zip minors') hdeps
    cases hdb with
    | app hdF hdmaj =>
    have hdE : ∀ (i : Nat) m', minsE[i]? = some m' → ErasesDeps E B σ lenv m' := by
      intro i m' h
      have hi := (List.getElem?_eq_some_iff.mp h).1
      have hmem : (m', minors'[i]'(by
          have := (RecLam.RecFixOf.closed hRF).1; omega)) ∈ minsE.zip minors' := by
        rw [List.mem_iff_getElem?]
        exact ⟨i, by rw [List.getElem?_zip_eq_some]; exact ⟨h, List.getElem?_eq_getElem _⟩⟩
      exact hdZ _ hmem
    -- the minors' erasures evaluate to erasures of their values
    have hW : ∀ i < mins.length, ∃ w, ∃ m mv m', mins[i]? = some m ∧ mvs[i]? = some mv ∧
        minsE[i]? = some m' ∧ Erases E B lps σ .nil [] mv w ∧ LBEval defaultFlags lenv m' w := by
      intro i hi
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨mv, hmv'⟩ : ∃ mv, mvs[i]? = some mv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨m', hm'⟩ : ∃ m', minsE[i]? = some m' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨a₀, A, hTr, hA⟩ := hminT i m hm
      obtain ⟨w, hw, hev⟩ := ihm i m mv hm hmv' hTr ⟨A, hA⟩ (hminE i m m' hm hm') (hdE i m' hm')
      exact ⟨w, m, mv, m', hm, hmv', hm', hw, hev⟩
    obtain ⟨ws, hwl, hwsP⟩ := choose_list _ hW
    have hwget : ∀ (i : Nat) w, ws[i]? = some w → ∃ m mv m', mins[i]? = some m ∧
        mvs[i]? = some mv ∧ minsE[i]? = some m' ∧ Erases E B lps σ .nil [] mv w ∧
        LBEval defaultFlags lenv m' w := hwsP
    have hwe : ∀ (i : Nat) x x', mvs[i]? = some x → ws[i]? = some x' →
        Erases E B lps σ .nil [] x x' := fun i x x' h1 h2 => by
      obtain ⟨m, mv, m', -, hmv', -, hw, -⟩ := hwget i x' h2
      rw [h1] at hmv'; cases hmv'; exact hw
    have hwc : ∀ w ∈ ws, closedn 0 w = true ∧ (∀ x, hasFVar x w = false) ∧ LBFixed w := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      obtain ⟨m, mv, m', hm, hmv', -, hwE', hev⟩ := hwget i _ (List.getElem?_eq_getElem hi)
      obtain ⟨h1, h2⟩ := hvalue i m mv _ hm hmv' hwE'
      exact ⟨h1, h2, LBEval.fixed hev⟩
    have hdws : ∀ w ∈ ws, ErasesDeps E B σ lenv w := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      obtain ⟨m, mv, m', -, -, hm', -, hev⟩ := hwget i _ (List.getElem?_eq_getElem hi)
      exact ErasesDeps.eval (hdE i m' hm') hev
    have hdFs : ErasesDeps E B σ lenv (substl ws.reverse F) :=
      ErasesDeps.substl (fun w hw => hdws w (List.mem_reverse.1 hw)) hdF
    obtain ⟨vb, hvb, hevb⟩ := rec_core henv hE hsub hbinj hcr hall hcT hblk hni hshape hihs hps hms
      hmins hlm hmv hmaj hcv hmi hmk hrfs hrl hih ihmaj ihih ihv he ht hRF (by omega) hwe hwc hdFs
      hmajE hdmaj
    have hmn := (RecLam.RecFixOf.closed hRF).1
    refine ⟨vb, hvb, eval_letChain _ ws _ vb (by simp; omega) ?_ hclZ (fun w hw => (hwc w hw).1) ?_⟩
    · intro i p w hp hw
      obtain ⟨m, mv, m', -, -, hm', -, hev⟩ := hwget i w hw
      rw [List.getElem?_zip_eq_some] at hp
      obtain ⟨hp1, -⟩ := hp
      rw [hm'] at hp1
      cases hp1
      exact hev
    · have happ : substl ws.reverse (LBTerm.app F majE) = .app (substl ws.reverse F) majE :=
        substl_app_closed hclmaj _ _
      rw [happ]
      exact hevb
  · -- the fixpoint with erasures of the minors substituted
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      spine_split has (by omega) (by omega) (by omega) (by omega)
    obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by simpa using hli.symm)
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hle.symm)
    simp only [List.nil_append] at hdeps ⊢
    cases hdeps with
    | app hdF hdmaj =>
    -- the dependencies of the minors' erasures
    have hdws : ∀ (i : Nat) w, ws[i]? = some w → ErasesDeps E B σ lenv w := by
      obtain ⟨hmm, hmlN, -, -, hsimple, indid, direct, nm, x, -, rfl, -⟩ :=
        recFix_shape henv hsub hcr hall hcT hblk hni hshape hihs hRF
      subst minors'
      have hwscl : ∀ w ∈ ws, closedn 0 w = true := fun w hw => (hws w hw).1
      have hFIX := substl_recFix (N := rv.numMinors) (nm := nm) (x := x) (direct := direct)
        (indid := indid) (npars := rv.numParams) hsimple hmlN (by omega) hwscl
      rw [hFIX] at hdF
      have hdbody : ErasesDeps E B σ lenv (recBody direct indid rv.numParams minors ws
          fun B => .bvar (B + 1)) := by
        cases hdF with
        | fix hd =>
          have := hd _ (.head _)
          cases this with
          | lambda hb => exact hb
      have h1 := deps_recBody hdbody
      intro i w hw
      have hi := (List.getElem?_eq_some_iff.mp hw).1
      have hmem : (i, minors.getD i default,
          Array.replicate (minors.getD i default).fields.length ConstructorArgRelevance.keep) ∈
          recCs minors := List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
      have := h1 _ hmem
      rwa [List.getD_eq_getElem?_getD, hw, Option.getD_some] at this
    -- the erasures of the minors are erasures of their values
    have hwe : ∀ (i : Nat) x x', mvs[i]? = some x → ws[i]? = some x' →
        Erases E B lps σ .nil [] x x' := by
      intro i mv w h1 h2
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m :=
        ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp h1).1; omega)⟩
      obtain ⟨a₀, A, hTr, hA⟩ := hminT i m hm
      obtain ⟨w', hw', hev⟩ := ihm i m mv hm h1 hTr ⟨A, hA⟩ (hwE i m w hm h2) (hdws i w h2)
      obtain rfl := (hws w (List.mem_of_getElem? h2)).2.2 _ _ hev
      exact hw'
    exact rec_core henv hE hsub hbinj hcr hall hcT hblk hni hshape hihs hps hms hmins hlm hmv hmaj
      hcv hmi hmk hrfs hrl hih ihmaj ihih ihv he ht hRF (by omega) hwe hws hdF hmajE hdmaj

end SimRec

end EraseProof
