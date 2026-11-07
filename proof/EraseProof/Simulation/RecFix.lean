import EraseProof.Simulation.RecEval

/-!
# The fixpoint of a recursor of a single inductive

`recFix` (`LeanToLambdaBox/Erasure.lean:787`) unfolded for a block of one member whose motive binds
only the major premise, whose fields are all kept and whose induction hypotheses take no
arguments: each alternative applies the minor premise (a bound variable above the fixpoint) to the
fields and to the recursive calls on the recursive fields (`RecFix.recAltS`). Closed substitutions
for the minors, the fixpoint's unfolding, the major premise and the fields move through this shape
(`RecFix.substl_recFix`, `RecFix.csubst_innerS`, `RecFix.substl_recAltS`).
-/

open Lean Erasure

namespace EraseProof

namespace RecFix

open TargetSubst TargetLift RecEval

/-- An alternative of `recFix`, as the shipping function builds it, for the block `members` of `n`
members under `N` minors, in a member with `k` indices. -/
def altF (N n k : Nat) (members : List RecMember) :
    Nat × RecMinor × ConstructorArgMask → List BinderName × LBTerm
  | (gi, mi, mask) =>
    let kept := (List.range mi.fields.length).filter (mask[·]? == some .keep)
    let B := kept.length
    let field (d f : Nat) : LBTerm := match kept.idxOf? f with
      | some p => .bvar (d + B - 1 - p)
      | none => .box
    let ih (h : RecIH) : LBTerm :=
      let L := h.binders.length
      let k' := ((members[h.member]?).map (·.binders.length - 1)).getD 0
      let call := (List.replicate k' LBTerm.box).foldl .app
        (.bvar (L + B + 1 + k + (n - 1 - h.member)))
      let arg := (List.range L).foldl (fun a y => .app a (.bvar (L - 1 - y))) (field L h.field)
      h.binders.foldr (fun y b => .lambda (binderNameOf y) b) (.app call arg)
    let args := (List.range mi.fields.length).map (field 0) ++ mi.ihs.map ih
    (kept.map fun f => binderNameOf (mi.fields.getD f .anonymous),
      args.foldl .app (.bvar (B + 1 + k + n + (N - 1 - gi))))

/-- The body of a member of `recFix` under its binders: the `case` on the major premise, or the
alternative applied to `□` (`direct`). -/
def innerS (direct : Bool) (indid : InductiveId) (npars : Nat)
    (cs : List (Nat × RecMinor × ConstructorArgMask))
    (alt : Nat × RecMinor × ConstructorArgMask → List BinderName × LBTerm) : LBTerm :=
  match direct, cs with
  | true, [c] => (List.replicate (alt c).1.length LBTerm.box).foldl .app
      ((alt c).1.foldr .lambda (alt c).2)
  | _, _ => .case (indid, npars) (.bvar 0) (cs.map alt)

theorem recFix_eq (N npars : Nat) (direct : Bool) (members : List RecMember) (j : Nat) :
    recFix N npars direct members j = .fix (members.map fun mem =>
      { name := fixDefName (mkRecName mem.name), principalArgIdx := mem.binders.length - 1,
        body := mem.binders.foldr (fun x b => .lambda (binderNameOf x) b)
          (innerS direct mem.indid npars mem.minors
            (altF N members.length (mem.binders.length - 1) members)) }) j := by
  unfold recFix innerS altF
  rfl

/-- The binder names of an alternative. -/
def altNames (mi : RecMinor) : List BinderName :=
  (List.range mi.fields.length).map fun f => binderNameOf (mi.fields.getD f .anonymous)

/-- An alternative's body: the head applied to the fields (the bound variables below `B`, first
field outermost) and to `fixv` applied to each recursive field. -/
def recAltS (H : LBTerm) (B : Nat) (fixv : LBTerm) (ihs : List RecIH) : LBTerm :=
  mkApps H ((List.range B).map (fun f => .bvar (B - 1 - f)) ++
    ihs.map fun h => .app fixv (.bvar (B - 1 - h.field)))

/-- The alternatives of `recFix` in the simple shape, for heads `H c B` and recursive calls
`fixv B`. -/
def altG (H : Nat → Nat → LBTerm) (fixv : Nat → LBTerm) :
    Nat × RecMinor × ConstructorArgMask → List BinderName × LBTerm
  | (gi, mi, _) => (altNames mi, recAltS (H gi mi.fields.length) mi.fields.length
      (fixv mi.fields.length) mi.ihs)

/-- The shape conditions on an alternative: every field kept, the induction hypotheses without
arguments, into the only member, on a field. -/
def SimpleAlt (c : Nat × RecMinor × ConstructorArgMask) : Prop :=
  c.2.2 = Array.replicate c.2.1.fields.length .keep ∧
    ∀ h ∈ c.2.1.ihs, h.binders = [] ∧ h.member = 0 ∧ h.field < c.2.1.fields.length

theorem filter_keep (nf : Nat) :
    (List.range nf).filter (fun x => (Array.replicate nf ConstructorArgRelevance.keep)[x]? ==
      some .keep) = List.range nf := by
  refine List.filter_eq_self.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  simp only [Array.getElem?_replicate, hx', ↓reduceIte]
  rfl

theorem idxOf?_range {nf f : Nat} (hf : f < nf) : (List.range nf).idxOf? f = some f := by
  rw [List.idxOf?_eq_some_iff]
  refine ⟨by simp [hf], by simp [List.getElem_range], fun j hj => ?_⟩
  simp [List.getElem_range]; omega

/-- In the simple shape, the shipping alternative is `altG` at the bound variables of the minor
(above the fields, the major premise and the fixpoint) and of the fixpoint. -/
theorem altF_simple (N : Nat) (m : RecMember) (hm : m.binders.length = 1)
    {c : Nat × RecMinor × ConstructorArgMask} (hc : SimpleAlt c) :
    altF N 1 0 [m] c = altG (fun gi B => .bvar (B + 2 + (N - 1 - gi))) (fun B => .bvar (B + 1)) c := by
  obtain ⟨gi, mi, mask⟩ := c
  obtain ⟨hmask, hih⟩ := hc
  dsimp only at hmask hih
  subst hmask
  simp only [altF, altG, filter_keep, List.length_range, altNames, recAltS]
  congr 1
  rw [← foldl_app_eq_mkApps]
  congr 1
  · congr 1
    · refine List.map_congr_left fun f hf => ?_
      rw [idxOf?_range (List.mem_range.1 hf)]
      simp only [Nat.zero_add]
    · refine List.map_congr_left fun h hh => ?_
      obtain ⟨hb, hmem, hf⟩ := hih h hh
      simp only [hb, hmem, List.length_nil, List.foldr_nil, List.range_zero, List.foldl_nil,
        idxOf?_range hf, Nat.zero_add, List.getElem?_cons_zero, Option.map_some, hm,
        Nat.sub_self, Option.getD_some, List.replicate_zero, Nat.add_zero]

/-- `innerS` depends on the alternatives only on its constructors. -/
theorem innerS_congr {direct : Bool} {indid : InductiveId} {npars : Nat}
    {cs : List (Nat × RecMinor × ConstructorArgMask)}
    {alt₁ alt₂ : Nat × RecMinor × ConstructorArgMask → List BinderName × LBTerm}
    (h : ∀ c ∈ cs, alt₁ c = alt₂ c) : innerS direct indid npars cs alt₁ = innerS direct indid npars cs alt₂ := by
  unfold innerS
  split
  · rw [h _ (.head _)]
  · congr 1
    exact List.map_congr_left h

/-! ## Substitutions -/

theorem length_altNames (mi : RecMinor) : (altNames mi).length = mi.fields.length := by
  simp [altNames]

theorem csubst_foldr_lambda (t : LBTerm) : ∀ (xs : List BinderName) (j : Nat) (b : LBTerm),
    csubst t j (xs.foldr .lambda b) = xs.foldr .lambda (csubst t (j + xs.length) b)
  | [], j, b => rfl
  | x :: xs, j, b => by
    show LBTerm.lambda x (csubst t (j + 1) (xs.foldr .lambda b)) = _
    rw [csubst_foldr_lambda t xs (j + 1) b]
    simp only [List.length_cons, List.foldr_cons, Nat.add_assoc, Nat.add_comm 1]

theorem csubst_foldl_app (t : LBTerm) (j : Nat) : ∀ (as : List LBTerm) (f : LBTerm),
    csubst t j (as.foldl .app f) = (as.map (csubst t j)).foldl .app (csubst t j f)
  | [], f => rfl
  | a :: as, f => by
    simp only [List.foldl_cons, List.map_cons]
    rw [csubst_foldl_app t j as (.app f a)]
    rfl

theorem csubstB_eq (t : LBTerm) (k : Nat) : ∀ bs : List (List BinderName × LBTerm),
    csubstB t k bs = bs.map fun p => (p.1, csubst t (k + p.1.length) p.2)
  | [] => rfl
  | (ns, b) :: bs => by rw [csubstB, csubstB_eq t k bs]; rfl

/-- A closed substitution above the fields moves to the head and the recursive call. -/
theorem csubst_recAltS {t : LBTerm} (H fixv : LBTerm) (B j : Nat) (ihs : List RecIH)
    (hih : ∀ h ∈ ihs, h.field < B) :
    csubst t (j + B) (recAltS H B fixv ihs) =
      recAltS (csubst t (j + B) H) B (csubst t (j + B) fixv) ihs := by
  unfold recAltS
  rw [RecLam.csubst_mkApps]
  congr 1
  simp only [List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun f hf => ?_
    have := List.mem_range.1 hf
    simp only [Function.comp_apply, csubst]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · refine List.map_congr_left fun h hh => ?_
    have := hih h hh
    simp only [Function.comp_apply, csubst]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A closed substitution at a positive index moves through `innerS` to the alternatives' heads and
recursive calls. -/
theorem csubst_innerS {t : LBTerm} (direct : Bool) (indid : InductiveId) (npars : Nat)
    (cs : List (Nat × RecMinor × ConstructorArgMask)) (H : Nat → Nat → LBTerm)
    (fixv : Nat → LBTerm) (d : Nat) (hd : 0 < d)
    (hcs : ∀ c ∈ cs, ∀ h ∈ c.2.1.ihs, h.field < c.2.1.fields.length) :
    csubst t d (innerS direct indid npars cs (altG H fixv)) =
      innerS direct indid npars cs (altG (fun c B => csubst t (d + B) (H c B))
        (fun B => csubst t (d + B) (fixv B))) := by
  unfold innerS
  split
  · rename_i c
    obtain ⟨gi, mi, mask⟩ := c
    simp only [altG]
    rw [csubst_foldl_app, csubst_foldr_lambda, length_altNames,
      csubst_recAltS _ _ _ d _ (hcs _ (.head _))]
    congr 1
    simp only [List.map_replicate, csubst]
  · simp only [csubst]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1
    rw [csubstB_eq, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨gi, mi, mask⟩ := c
    simp only [Function.comp_apply, altG, length_altNames]
    rw [csubst_recAltS _ _ _ d _ (hcs _ hc)]

/-- Closed substitutions in turn at a bound variable from the index `d` on. -/
theorem foldl_csubst_bvar : ∀ (us : List LBTerm) (d m : Nat), (∀ u ∈ us, closedn 0 u = true) →
    us.foldl (fun b u => csubst u d b) (.bvar (d + m)) =
      if h : m < us.length then us[m] else .bvar (d + m - us.length)
  | [], d, m, _ => by simp
  | u :: us, d, m, hus => by
    simp only [List.foldl_cons, csubst]
    by_cases hm : m = 0
    · subst hm
      simp only [Nat.add_zero, ↓reduceIte, List.length_cons, Nat.zero_lt_succ, ↓reduceDIte,
        List.getElem_cons_zero]
      have : ∀ (vs : List LBTerm) (x : LBTerm), closedn 0 x = true → (∀ v ∈ vs, closedn 0 v = true) →
          vs.foldl (fun b v => csubst v d b) x = x := by
        intro vs
        induction vs with
        | nil => intro x _ _; rfl
        | cons v vs ih =>
          intro x hx hvs
          simp only [List.foldl_cons]
          rw [csubst_closedn v x 0 d hx (Nat.zero_le _)]
          exact ih x hx fun w hw => hvs w (.tail _ hw)
      exact this us u (hus u (.head _)) fun v hv => hus v (.tail _ hv)
    · rw [ite_eq_right (by omega), ite_eq_left (by omega),
        show d + m - 1 = d + (m - 1) by omega,
        foldl_csubst_bvar us d (m - 1) fun v hv => hus v (.tail _ hv)]
      simp only [List.length_cons]
      by_cases hl : m - 1 < us.length
      · have hl' : m < us.length + 1 := by omega
        simp only [hl, hl', ↓reduceDIte, List.getElem_cons, hm]
      · have hl' : ¬ m < us.length + 1 := by omega
        simp only [hl, hl', ↓reduceDIte]
        congr 1
        omega

/-- `substl` at the top of a one-member fixpoint substitutes at index 2 in its body under the
major premise's λ. -/
theorem substl_fix1 (nm : BinderName) (xn : BinderName) (r : Nat) :
    ∀ (us : List LBTerm) (I : LBTerm), substl us (.fix [⟨nm, .lambda xn I, r⟩] 0) =
      .fix [⟨nm, .lambda xn (us.foldl (fun b u => csubst u 2 b) I), r⟩] 0
  | [], I => rfl
  | u :: us, I => by
    show substl us (csubst u 0 (.fix [⟨nm, .lambda xn I, r⟩] 0)) = _
    rw [show csubst u 0 (.fix [⟨nm, .lambda xn I, r⟩] 0) =
      .fix [⟨nm, .lambda xn (csubst u 2 I), r⟩] 0 from rfl, substl_fix1 nm xn r us]
    rfl

end RecFix

end EraseProof
