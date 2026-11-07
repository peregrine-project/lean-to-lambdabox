import EraseProof.Simulation.Iota
import EraseProof.Simulation.RecFix

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

end SimRec

end EraseProof
