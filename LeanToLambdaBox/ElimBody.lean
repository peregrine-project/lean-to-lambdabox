import LeanToLambdaBox.IotaBridge
import LeanToLambdaBox.Semantics.Compute

/-!
# Eliminator and constructor bodies, and their ι/β theorems

The λ□ bodies a runtime library must give a constructor constant and an eliminator
constant, as **constructions**, together with the theorems that they reproduce the
reductions `[S Fig. 18]`'s side conditions ask for:

* `mkCtorBody` — the η-expanded constructor, and `mkCtorBody_beta`: applying it to a
  full argument list has the evaluations of the constructor spine itself;
* `mkElimBody` — the case-dispatching eliminator at the `casesOn` calling convention
  (`dp` dropped arguments, then the discriminant, then one minor per constructor), and
  `mkElimBody_iota_fwd`/`mkElimBody_iota_bwd`: applying it to a constructor spine
  evaluates as MetaRocq's `iota_red` does;
* `mkElimBodyRec` — the same dispatch under a guarded `fix` whose principal argument is
  the discriminant, and `ElimBody`, the two-shape syntactic predicate `Lower` keys its
  eliminator arms on.

Everything here is target-side: `LBTerm`, `WcbvEval` and the de Bruijn operations, with
no `Expr`, no `VEnv` and no run state.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Telescope helpers -/

/-- The arguments an alternative applies to its minor: `fieldArgs m = [.bvar (m-1), …,
.bvar 0]`, the `m` field binders of a `case` alternative in *source* order. -/
def fieldArgs : Nat → List LBTerm
  | 0 => []
  | m + 1 => .bvar m :: fieldArgs m

@[simp] theorem fieldArgs_length (m : Nat) : (fieldArgs m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fieldArgs, ih]

/-- `fieldArgs` is `Lower`'s `bvarsDesc`: the descending run of de Bruijn indices. -/
theorem fieldArgs_eq (m : Nat) : fieldArgs m = (List.range m).reverse.map LBTerm.bvar := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ]; simp [fieldArgs, ih]

theorem fieldArgs_lt {m : Nat} {t : LBTerm} (h : t ∈ fieldArgs m) : ∃ i, i < m ∧ t = .bvar i := by
  induction m with
  | zero => exact absurd h (by simp [fieldArgs])
  | succ m ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := ih h
        exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/-- The alternatives of `mkElimBody`: alternative `k` binds its `nfs[k]` fields and
applies the `k`-th minor — which sits `nfs[k] + (nfs.length - 1 - k)` binders out — to
them, in order. Written by recursion on the *remaining* field-count list, whose length is
exactly that distance. -/
def elimAlts : List Nat → List (List BinderName × LBTerm)
  | [] => []
  | m :: ms =>
      (List.replicate m .anon, LBTerm.mkApps (.bvar (m + ms.length)) (fieldArgs m))
        :: elimAlts ms

/-- The alternatives after the minors have been substituted: alternative `k` applies the
`k`-th minor *value*, lifted over the `nfs[k]` field binders, to the fields. -/
def elimAltsSub : List Nat → List LBTerm → List (List BinderName × LBTerm)
  | [], _ => []
  | _ :: _, [] => []
  | m :: ms, mv :: mvs =>
      (List.replicate m .anon, LBTerm.mkApps (LBTerm.shift m 0 mv) (fieldArgs m))
        :: elimAltsSub ms mvs

@[simp] theorem elimAlts_length (ms : List Nat) : (elimAlts ms).length = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [elimAlts, ih]

@[simp] theorem elimAltsSub_length (ms : List Nat) (mvs : List LBTerm) :
    (elimAltsSub ms mvs).length = min ms.length mvs.length := by
  induction ms generalizing mvs with
  | nil => simp [elimAltsSub]
  | cons m ms ih =>
      cases mvs with
      | nil => simp [elimAltsSub]
      | cons mv mvs => simp [elimAltsSub, ih]

/-! ## The bodies -/

/-- The λ□ body of a constructor constant: `λ x₁ … xₙ. c x₁ … xₙ`, the η-expansion the
eraser's `visitCtorEta` builds. -/
def mkCtorBody (iid : InductiveId) (k : Nat) (ns : List BinderName) : LBTerm :=
  mkLambdas ns (LBTerm.mkApps (.construct iid k []) (fieldArgs ns.length))

/-- The λ□ body of a non-recursive eliminator constant at the `casesOn` calling
convention: `dp` dropped arguments (parameters and motive), the discriminant, then one
minor per constructor, dispatched by a `case` node on the discriminant. -/
def mkElimBody (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm :=
  mkLambdas (List.replicate (dp + 1 + nfs.length) .anon)
    (.case (iid, np) (.bvar nfs.length) (elimAlts nfs))

/-- The λ□ body of a recursive eliminator constant: `mkElimBody`'s dispatch under a
guarded `fix` whose principal argument is the discriminant. The body is closed, so the
fix variable is unused: which fields carry a recursive call is not a function of the
field *counts* `nfs`, so no recursive call can be written at this signature. -/
def mkElimBodyRec (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm :=
  .fix [{ name := .anon, body := mkElimBody iid np dp nfs, principalArgIdx := dp }] 0

/-- The λ□ body of an eliminator constant, as a *syntactic* shape: one constructor per
shape, no semantic side condition. There is no propositional-singleton shape — the
emitted environment marks every inductive non-propositional, so a `□`-discriminant
`.case` is stuck at every flag point. -/
inductive ElimBody : InductiveId → Nat → Nat → List Nat → LBTerm → Prop
  | cases {iid : InductiveId} {np dp : Nat} {nfs : List Nat} :
      ElimBody iid np dp nfs (mkElimBody iid np dp nfs)
  /-- The recursive shape. Named `recur` because `ElimBody.rec` is the recursor. -/
  | recur {iid : InductiveId} {np dp : Nat} {nfs : List Nat} :
      ElimBody iid np dp nfs (mkElimBodyRec iid np dp nfs)

/-! ## Closedness -/

/-- Every field index is below the telescope it is read under. -/
theorem fieldArgs_closed {m k : Nat} (h : m ≤ k) : ∀ t ∈ fieldArgs m, LBClosed t k := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := fieldArgs_lt ht
  exact Nat.lt_of_lt_of_le hi h

/-- The alternatives are closed under `ms.length` binders: the `k`-th minor's index is
`nfs[k] + (nfs.length - 1 - k)`, the largest of which is `nfs[k] + nfs.length - 1`. -/
theorem elimAlts_closed : ∀ (ms : List Nat) {k : Nat}, ms.length ≤ k → LBClosedAlts (elimAlts ms) k
  | [], _, _ => trivial
  | m :: ms, k, h => by
      refine ⟨?_, elimAlts_closed ms (by simp only [List.length_cons] at h; omega)⟩
      simp only [List.length_replicate]
      refine LBClosed.mkApps ?_ (fun a ha => fieldArgs_closed (Nat.le_add_left m k) a ha)
      simp only [List.length_cons] at h
      show m + ms.length < k + m
      omega

theorem mkCtorBody_closed (iid : InductiveId) (k : Nat) (ns : List BinderName) :
    LBClosed (mkCtorBody iid k ns) 0 := by
  refine LBClosed.mkLambdas (LBClosed.mkApps (hd := .construct iid k []) trivial ?_)
  exact fun a ha => fieldArgs_closed (Nat.le_of_eq (Nat.zero_add ns.length).symm) a ha

theorem mkElimBody_closed (iid : InductiveId) (np dp : Nat) (nfs : List Nat) :
    LBClosed (mkElimBody iid np dp nfs) 0 := by
  refine LBClosed.mkLambdas ⟨?_, ?_⟩
  · show nfs.length < 0 + (List.replicate (dp + 1 + nfs.length) BinderName.anon).length
    simp only [List.length_replicate]
    omega
  · refine elimAlts_closed nfs ?_
    simp only [List.length_replicate]
    omega

theorem mkElimBodyRec_closed (iid : InductiveId) (np dp : Nat) (nfs : List Nat) :
    LBClosed (mkElimBodyRec iid np dp nfs) 0 :=
  ⟨(mkElimBody_closed iid np dp nfs).mono (Nat.zero_le 1), trivial⟩

/-- Both eliminator shapes are closed: what `Lower`'s `ElimBodyClosed` asks for. -/
theorem ElimBody.closed {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {h : LBTerm} :
    ElimBody iid np dp nfs h → LBClosed h 0
  | .cases => mkElimBody_closed iid np dp nfs
  | .recur => mkElimBodyRec_closed iid np dp nfs


/-! ## De Bruijn computations

The β-chain of a λ-telescope is `substTele`: the arguments are substituted outermost
first, each at the depth its own binder sits at. Unlike `LBTerm.substList` — the ι rule's
*sequential* substitution at depth `0` — it never substitutes into an argument already
placed, so it needs no closedness proviso. -/

/-- A zero shift is the identity. -/
theorem LBTerm.shift_zero (c : Nat) (t : LBTerm) : LBTerm.shift 0 c t = t := by
  induction t using LBTerm.recData generalizing c with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i => simp only [LBTerm.shift]; split <;> rfl
  | hlam n b ih => simp only [LBTerm.shift, ih]
  | hletIn n v b ihv ihb => simp only [LBTerm.shift, ihv, ihb]
  | happ f a ihf iha => simp only [LBTerm.shift, ihf, iha]
  | hconstruct iid k args ih =>
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
      rw [List.map_congr_left (fun x hx => ih x hx c), List.map_id_fun', id_eq]
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, ihd, LBTerm.shiftAlts_eq_map]
      rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
      rw [iha a ha (c + a.1.length)]
  | hproj p e ih => simp only [LBTerm.shift, ih]
  | hfix defs i ih =>
      simp only [LBTerm.shift]
      congr 1
      have key : ∀ (l : List (@FixDef LBTerm)),
          (∀ x ∈ l, LBTerm.shift 0 (c + defs.length) x.body = x.body) →
          LBTerm.shiftDefs 0 (c + defs.length) l = l := by
        intro l hl
        induction l with
        | nil => rfl
        | cons fd rest ihr =>
            simp only [LBTerm.shiftDefs, hl fd (List.mem_cons_self ..),
              ihr (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
      exact key defs (fun x hx => ih x hx (c + defs.length))

/-- `subst` distributes over an application spine. -/
theorem LBTerm.subst_spine (s : LBTerm) (d : Nat) (hd : LBTerm) (args : List LBTerm) :
    LBTerm.subst s d (LBTerm.mkApps hd args)
      = LBTerm.mkApps (LBTerm.subst s d hd) (args.map (LBTerm.subst s d)) := by
  induction args generalizing hd with
  | nil => rfl
  | cons a as ih => simpa [LBTerm.mkApps, LBTerm.subst] using ih (.app hd a)

/-- `substList` distributes over an application spine. -/
theorem LBTerm.substList_mkApps (l : List LBTerm) (hd : LBTerm) (args : List LBTerm) :
    LBTerm.substList l (LBTerm.mkApps hd args)
      = LBTerm.mkApps (LBTerm.substList l hd) (args.map (LBTerm.substList l)) := by
  induction l generalizing hd args with
  | nil =>
      show LBTerm.mkApps hd args = LBTerm.mkApps hd (args.map (LBTerm.substList []))
      congr 1
      rw [show LBTerm.substList [] = id from funext fun _ => rfl, List.map_id]
  | cons s l ih =>
      show LBTerm.substList l (LBTerm.subst1 s (LBTerm.mkApps hd args)) = _
      rw [LBTerm.subst1, LBTerm.subst_spine, ih, List.map_map]
      rfl

/-- The β-chain of a λ-telescope, under `o` further binders: `substTele o vs t`
substitutes `vs` into `t` outermost first, the `i`-th argument at depth
`(vs.length - 1 - i) + o`. -/
def substTele (o : Nat) : List LBTerm → LBTerm → LBTerm
  | [], t => t
  | v :: vs, t => substTele o vs (LBTerm.subst v (vs.length + o) t)

/-- A prefix of the telescope that lands entirely above the term's loose indices does
nothing. -/
theorem substTele_closed_prefix : ∀ (l₁ l₂ : List LBTerm) {o j : Nat} {t : LBTerm},
    LBClosed t j → j ≤ l₂.length + o → substTele o (l₁ ++ l₂) t = substTele o l₂ t
  | [], _, _, _, _, _, _ => rfl
  | v :: l₁, l₂, o, j, t, ht, hj => by
      show substTele o (l₁ ++ l₂) (LBTerm.subst v ((l₁ ++ l₂).length + o) t) = _
      rw [ht.subst_eq (by simp only [List.length_append]; omega) v]
      exact substTele_closed_prefix l₁ l₂ ht hj

/-- The telescope pushes into a `case`, each alternative's depth raised by its own field
binders. -/
theorem substTele_case (o : Nat) : ∀ (vs : List LBTerm) (ip : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)),
    substTele o vs (.case ip d alts)
      = .case ip (substTele o vs d) (alts.map fun a => (a.1, substTele (a.1.length + o) vs a.2))
  | [], _, _, alts => by simp [substTele]
  | v :: vs, ip, d, alts => by
      show substTele o vs (LBTerm.subst v (vs.length + o) (.case ip d alts)) = _
      rw [show LBTerm.subst v (vs.length + o) (LBTerm.case ip d alts)
            = .case ip (LBTerm.subst v (vs.length + o) d)
                (LBTerm.substAlts v (vs.length + o) alts) from rfl,
        substTele_case o vs, LBTerm.substAlts_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      show (a.1, substTele (a.1.length + o) vs (LBTerm.subst v (vs.length + o + a.1.length) a.2))
        = (a.1, substTele (a.1.length + o) (v :: vs) a.2)
      rw [show substTele (a.1.length + o) (v :: vs) a.2
            = substTele (a.1.length + o) vs (LBTerm.subst v (vs.length + (a.1.length + o)) a.2)
            from rfl,
        show vs.length + o + a.1.length = vs.length + (a.1.length + o) from by omega]

/-- The telescope cancels a matching shift. -/
theorem substTele_shift (o : Nat) : ∀ (vs : List LBTerm) (t : LBTerm),
    substTele o vs (LBTerm.shift (o + vs.length) 0 t) = LBTerm.shift o 0 t
  | [], t => by simp [substTele]
  | v :: vs, t => by
      show substTele o vs (LBTerm.subst v (vs.length + o) (LBTerm.shift (o + (vs.length + 1)) 0 t))
        = _
      rw [show o + (vs.length + 1) = (o + vs.length) + 1 by omega,
        LBTerm.subst_shift_cancel v (o + vs.length) 0 (vs.length + o) (Nat.zero_le _) (by omega),
        substTele_shift o vs]

/-! ### The eliminator body's alternatives under substitution -/

/-- Field indices are untouched by a substitution at or above their telescope. -/
theorem fieldArgs_subst_eq {m d : Nat} (h : m ≤ d) (s : LBTerm) :
    (fieldArgs m).map (LBTerm.subst s d) = fieldArgs m := by
  rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
  exact (fieldArgs_closed h a ha).subst_eq (Nat.le_refl _) s

/-- Substituting at or above the minors' telescope leaves the alternatives alone. -/
theorem substAlts_elimAlts (ms : List Nat) {s : LBTerm} {d : Nat} (h : ms.length ≤ d) :
    LBTerm.substAlts s d (elimAlts ms) = elimAlts ms := by
  rw [LBTerm.substAlts_eq_map]
  have hcl := (LBClosedAlts_iff (elimAlts ms) d).mp (elimAlts_closed ms h)
  rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
  rw [(hcl a ha).subst_eq (Nat.le_refl _) s]

/-- The minors still to be substituted only cancel the lift of the minor already placed. -/
theorem substTele_minor (m : Nat) : ∀ (vs : List LBTerm) (mv : LBTerm),
    substTele m vs (LBTerm.mkApps (LBTerm.shift (vs.length + m) 0 mv) (fieldArgs m))
      = LBTerm.mkApps (LBTerm.shift m 0 mv) (fieldArgs m)
  | [], mv => by
      show LBTerm.mkApps (LBTerm.shift (0 + m) 0 mv) (fieldArgs m) = _
      rw [Nat.zero_add]
  | v :: vs, mv => by
      show substTele m vs (LBTerm.subst v (vs.length + m)
        (LBTerm.mkApps (LBTerm.shift ((v :: vs).length + m) 0 mv) (fieldArgs m))) = _
      rw [LBTerm.subst_spine, fieldArgs_subst_eq (Nat.le_add_left m vs.length),
        show (v :: vs).length + m = (vs.length + m) + 1 by simp only [List.length_cons]; omega,
        LBTerm.subst_shift_cancel v (vs.length + m) 0 (vs.length + m) (Nat.zero_le _)
          (Nat.le_of_eq (Nat.zero_add _).symm),
        substTele_minor m vs]

/-- Substituting the minors turns `elimAlts` into `elimAltsSub`: alternative `k` applies
the `k`-th minor value, lifted over its own field binders, to the fields. -/
theorem elimAlts_map_substTele : ∀ (ms : List Nat) (mvs : List LBTerm), ms.length = mvs.length →
    (elimAlts ms).map (fun a => (a.1, substTele a.1.length mvs a.2)) = elimAltsSub ms mvs
  | [], _, _ => rfl
  | m :: ms, [], h => by simp at h
  | m :: ms, mv :: mvs, h => by
      have hlen : ms.length = mvs.length := by simpa using h
      show (_, substTele (List.replicate m BinderName.anon).length (mv :: mvs)
              (LBTerm.mkApps (.bvar (m + ms.length)) (fieldArgs m)))
            :: (elimAlts ms).map (fun a => (a.1, substTele a.1.length (mv :: mvs) a.2))
          = _
      rw [List.length_replicate]
      have hhead : substTele m (mv :: mvs) (LBTerm.mkApps (.bvar (m + ms.length)) (fieldArgs m))
          = LBTerm.mkApps (LBTerm.shift m 0 mv) (fieldArgs m) := by
        show substTele m mvs (LBTerm.subst mv (mvs.length + m)
          (LBTerm.mkApps (.bvar (m + ms.length)) (fieldArgs m))) = _
        rw [LBTerm.subst_spine, fieldArgs_subst_eq (Nat.le_add_left m mvs.length),
          LBTerm.subst_bvar, if_neg (by omega), if_pos (by omega), substTele_minor m mvs]
      have htail : (elimAlts ms).map (fun a => (a.1, substTele a.1.length (mv :: mvs) a.2))
          = elimAltsSub ms mvs := by
        rw [← elimAlts_map_substTele ms mvs hlen]
        refine List.map_congr_left (fun a ha => ?_)
        have hcl := (LBClosedAlts_iff (elimAlts ms) mvs.length).mp
          (elimAlts_closed ms (Nat.le_of_eq hlen))
        show (a.1, substTele a.1.length mvs (LBTerm.subst mv (mvs.length + a.1.length) a.2)) = _
        rw [(hcl a ha).subst_eq (Nat.le_refl _) mv]
      rw [hhead, htail]
      rfl

/-- The whole β-chain of `mkElimBody`, computed: the `dp` dropped values disappear, the
discriminant value lands in the `case` node, and the minors land in the alternatives. -/
theorem substTele_elimBody (iid : InductiveId) (np : Nat) (nfs : List Nat)
    (pv : List LBTerm) (dv : LBTerm) (mvs : List LBTerm) (hm : mvs.length = nfs.length) :
    substTele 0 (pv ++ dv :: mvs) (.case (iid, np) (.bvar nfs.length) (elimAlts nfs))
      = .case (iid, np) dv (elimAltsSub nfs mvs) := by
  have hcl : LBClosed (LBTerm.case (iid, np) (.bvar nfs.length) (elimAlts nfs)) (nfs.length + 1) :=
    ⟨Nat.lt_succ_self _, elimAlts_closed nfs (Nat.le_succ _)⟩
  rw [substTele_closed_prefix pv (dv :: mvs) hcl (by simp only [List.length_cons]; omega)]
  have hsub : LBTerm.subst dv (mvs.length + 0)
      (LBTerm.case (iid, np) (.bvar nfs.length) (elimAlts nfs))
      = .case (iid, np) (LBTerm.shift nfs.length 0 dv) (elimAlts nfs) := by
    show LBTerm.case (iid, np) (LBTerm.subst dv (mvs.length + 0) (.bvar nfs.length))
        (LBTerm.substAlts dv (mvs.length + 0) (elimAlts nfs)) = _
    rw [substAlts_elimAlts nfs (by omega), LBTerm.subst_bvar, if_neg (by omega),
      if_pos (by omega), hm, Nat.add_zero]
  show substTele 0 mvs (LBTerm.subst dv (mvs.length + 0) _) = _
  rw [hsub, substTele_case, ← hm,
    show LBTerm.shift mvs.length 0 dv = LBTerm.shift (0 + mvs.length) 0 dv by rw [Nat.zero_add],
    substTele_shift, LBTerm.shift_zero]
  congr 1
  rw [← elimAlts_map_substTele nfs mvs (hm ▸ rfl)]
  exact List.map_congr_left (fun a _ => by rw [Nat.add_zero])

/-- Reading alternative `k` of the substituted alternatives. -/
theorem elimAltsSub_getElem? : ∀ (ms : List Nat) (mvs : List LBTerm), ms.length = mvs.length →
    ∀ {k : Nat}, k < ms.length →
      (elimAltsSub ms mvs)[k]? = some (List.replicate ms[k]! .anon,
        LBTerm.mkApps (LBTerm.shift ms[k]! 0 mvs[k]!) (fieldArgs ms[k]!))
  | [], _, _, k, hk => absurd hk (by simp)
  | m :: ms, [], h, _, _ => by simp at h
  | m :: ms, mv :: mvs, h, 0, _ => rfl
  | m :: ms, mv :: mvs, h, k + 1, hk => by
      have hlen : ms.length = mvs.length := by simpa using h
      have hk' : k < ms.length := by simpa using hk
      show (elimAltsSub ms mvs)[k]? = _
      rw [elimAltsSub_getElem? ms mvs hlen hk']
      simp

/-- **The ι reduct of an `elimAltsSub` alternative.** The alternative's body applies the
lifted minor to the field binders; the ι rule's *sequential* `substList` of the reversed
fields cancels the lift and restores the fields in order — provided the fields are
closed, which is `EWcbvEval`'s own `closedn 0` convention (see
`wcbvEval_mkApps_mkLambdas_substList`). -/
theorem substList_reverse_fields : ∀ (fields : List LBTerm), (∀ f ∈ fields, LBClosed f 0) →
    ∀ (X : LBTerm),
      LBTerm.substList fields.reverse
          (LBTerm.mkApps (LBTerm.shift fields.length 0 X) (fieldArgs fields.length))
        = LBTerm.mkApps X fields
  | [], _, X => by
      show LBTerm.substList [] (LBTerm.shift 0 0 X) = X
      rw [LBTerm.shift_zero]; rfl
  | f :: rest, hcl, X => by
      have hrest : ∀ g ∈ rest, LBClosed g 0 := fun g hg => hcl g (List.mem_cons_of_mem _ hg)
      have hstep : LBTerm.mkApps (LBTerm.shift (f :: rest).length 0 X)
            (fieldArgs (f :: rest).length)
          = LBTerm.mkApps (LBTerm.shift rest.length 0 (.app (LBTerm.shift 1 0 X) (.bvar 0)))
              (fieldArgs rest.length) := by
        have hhd : LBTerm.shift rest.length 0 (LBTerm.app (LBTerm.shift 1 0 X) (LBTerm.bvar 0))
            = .app (LBTerm.shift (rest.length + 1) 0 X) (.bvar rest.length) := by
          show LBTerm.app (LBTerm.shift rest.length 0 (LBTerm.shift 1 0 X))
              (LBTerm.shift rest.length 0 (LBTerm.bvar 0)) = _
          rw [LBTerm.shift_shift 1 rest.length 0 0 (Nat.le_refl 0) (by omega),
            LBTerm.shift_bvar, if_pos (Nat.zero_le _),
            show 1 + rest.length = rest.length + 1 by omega, Nat.zero_add]
        show LBTerm.mkApps (.app (LBTerm.shift (rest.length + 1) 0 X) (.bvar rest.length))
            (fieldArgs rest.length)
          = LBTerm.mkApps (LBTerm.shift rest.length 0 (.app (LBTerm.shift 1 0 X) (.bvar 0)))
              (fieldArgs rest.length)
        rw [hhd]
      rw [hstep, List.reverse_cons, LBTerm.substList_concat,
        substList_reverse_fields rest hrest, LBTerm.subst1, LBTerm.subst_spine,
        List.map_congr_left (fun g hg => (hrest g hg).subst_eq (Nat.zero_le 0) f),
        List.map_id_fun', id_eq]
      show LBTerm.mkApps (.app (LBTerm.subst f 0 (LBTerm.shift 1 0 X))
          (LBTerm.subst f 0 (.bvar 0))) rest = _
      rw [LBTerm.subst_shift_cancel f 0 0 0 (Nat.le_refl 0) (Nat.le_refl 0), LBTerm.shift_zero,
        LBTerm.subst_bvar, if_neg (by omega), if_pos rfl, LBTerm.shift_zero]
      rfl

/-! ## Evaluation toolkit -/

/-- A value evaluates to itself. -/
theorem eval_self {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}
    (h : WcbvEval Γ fl t v) : WcbvEval Γ fl v v :=
  value_final (eval_to_value h)

/-- Pointwise evaluation of an argument list. -/
inductive EvalArgs (Γ : GlobalDeclarations) (fl : WcbvFlags) : List LBTerm → List LBTerm → Prop
  | nil : EvalArgs Γ fl [] []
  | cons {a v : LBTerm} {as vs : List LBTerm} :
      WcbvEval Γ fl a v → EvalArgs Γ fl as vs → EvalArgs Γ fl (a :: as) (v :: vs)

theorem EvalArgs.length_eq {Γ : GlobalDeclarations} {fl : WcbvFlags} {as vs : List LBTerm} :
    EvalArgs Γ fl as vs → as.length = vs.length
  | .nil => rfl
  | .cons _ h => by simp [h.length_eq]

theorem EvalArgs.append {Γ : GlobalDeclarations} {fl : WcbvFlags} {as bs us ws : List LBTerm} :
    EvalArgs Γ fl as us → EvalArgs Γ fl bs ws → EvalArgs Γ fl (as ++ bs) (us ++ ws)
  | .nil, h => h
  | .cons ha hrest, h => .cons ha (hrest.append h)

theorem EvalArgs.append_inv {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {as bs vs : List LBTerm}, EvalArgs Γ fl (as ++ bs) vs →
      ∃ us ws, vs = us ++ ws ∧ EvalArgs Γ fl as us ∧ EvalArgs Γ fl bs ws
  | [], _, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | a :: as, bs, _, .cons ha hrest => by
      obtain ⟨us, ws, rfl, h1, h2⟩ := hrest.append_inv
      exact ⟨_ :: us, ws, rfl, .cons ha h1, h2⟩

theorem EvalArgs.get {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {as vs : List LBTerm}, EvalArgs Γ fl as vs → ∀ {k : Nat}, k < as.length →
      WcbvEval Γ fl as[k]! vs[k]!
  | _, _, .nil, k, hk => absurd hk (by simp)
  | _, _, .cons ha _, 0, _ => by simpa using ha
  | _, _, .cons _ hrest, k + 1, hk => by
      have := hrest.get (k := k) (by simpa using hk)
      simpa using this

/-- Argument lists that evaluate somewhere have a value list. -/
theorem EvalArgs.of_forall_exists {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (as : List LBTerm), (∀ a ∈ as, ∃ av, WcbvEval Γ fl a av) → ∃ vs, EvalArgs Γ fl as vs
  | [], _ => ⟨[], .nil⟩
  | a :: as, h => by
      obtain ⟨av, hav⟩ := h a (List.mem_cons_self ..)
      obtain ⟨vs, hvs⟩ := EvalArgs.of_forall_exists as (fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact ⟨av :: vs, .cons hav hvs⟩

/-- Both parts of an application evaluate: every `.app` rule evaluates function and
argument. -/
theorem wcbvEval_app_inv {Γ : GlobalDeclarations} {fl : WcbvFlags} {f a v : LBTerm}
    (h : WcbvEval Γ fl (.app f a) v) :
    (∃ fv, WcbvEval Γ fl f fv) ∧ (∃ av, WcbvEval Γ fl a av) := by
  cases h with
  | beta hf ha _ => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | app_box hf ha => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | construct_app _ hf _ _ ha => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | fix_guarded _ hf ha _ _ _ => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | fix_stuck _ hf ha _ _ => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | fix_unguarded _ hf _ ha _ => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩
  | app_cong hf _ ha => exact ⟨⟨_, hf⟩, ⟨_, ha⟩⟩

/-- Head and every argument of an evaluating application spine evaluate. -/
theorem wcbvEval_mkApps_inv {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (as : List LBTerm) {f r : LBTerm}, WcbvEval Γ fl (LBTerm.mkApps f as) r →
      (∃ fv, WcbvEval Γ fl f fv) ∧ (∀ a ∈ as, ∃ av, WcbvEval Γ fl a av)
  | [], f, r, h => ⟨⟨r, h⟩, by simp⟩
  | a :: as, f, r, h => by
      obtain ⟨⟨w, hw⟩, hargs⟩ := wcbvEval_mkApps_inv as (f := .app f a) h
      obtain ⟨hf, ⟨av, ha⟩⟩ := wcbvEval_app_inv hw
      refine ⟨hf, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨av, ha⟩
      · exact hargs x hx

/-- One β step, with the argument's value fixed in advance. -/
theorem wcbvEval_beta_step {Γ : GlobalDeclarations} {fl : WcbvFlags} {n : BinderName}
    {b a av v : LBTerm} (ha : WcbvEval Γ fl a av) :
    WcbvEval Γ fl (.app (.lambda n b) a) v ↔ WcbvEval Γ fl (LBTerm.subst1 av b) v := by
  constructor
  · intro hv
    cases hv with
    | @beta _ _ n' b' av' _ hfun harg hbody =>
        have hlam := eval_deterministic (WcbvEval.lam n b) hfun
        injection hlam with _ hb
        subst hb
        rw [eval_deterministic ha harg]
        exact hbody
    | app_box hfun _ =>
        exact absurd (eval_deterministic (WcbvEval.lam n b) hfun) (by simp)
    | construct_app _ hfun _ _ _ =>
        exact absurd (congrArg LBTerm.spineHead (eval_deterministic (WcbvEval.lam n b) hfun))
          (by simp [LBTerm.spineHead_mkApps])
    | fix_guarded _ hfun _ _ _ _ =>
        exact absurd (congrArg LBTerm.spineHead (eval_deterministic (WcbvEval.lam n b) hfun))
          (by simp [LBTerm.spineHead_mkApps])
    | fix_stuck _ hfun _ _ _ =>
        exact absurd (congrArg LBTerm.spineHead (eval_deterministic (WcbvEval.lam n b) hfun))
          (by simp [LBTerm.spineHead_mkApps])
    | fix_unguarded _ hfun _ _ _ =>
        exact absurd (eval_deterministic (WcbvEval.lam n b) hfun) (by simp)
    | app_cong hfun hstuck _ =>
        rw [← eval_deterministic (WcbvEval.lam n b) hfun] at hstuck
        exact absurd hstuck (by simp [isStuckApp, isLambda])
  · intro hv
    exact .beta (.lam n b) ha hv

/-- Replacing a spine's head by one with the same value preserves evaluation. -/
theorem wcbvEval_mkApps_head_swap {Γ : GlobalDeclarations} {fl : WcbvFlags} {g h w : LBTerm}
    (hg : WcbvEval Γ fl g w) (hh : WcbvEval Γ fl h w) (as : List LBTerm) {r : LBTerm} :
    WcbvEval Γ fl (LBTerm.mkApps g as) r → WcbvEval Γ fl (LBTerm.mkApps h as) r :=
  wcbvEval_mkApps_head_congr as (fun hv => (eval_deterministic hg hv) ▸ hh)

/-- Replacing an argument by one with the same value preserves evaluation. -/
theorem wcbvEval_app_arg_swap {Γ : GlobalDeclarations} {fl : WcbvFlags} {f a a' w v : LBTerm}
    (h1 : WcbvEval Γ fl a w) (h2 : WcbvEval Γ fl a' w) :
    WcbvEval Γ fl (.app f a) v → WcbvEval Γ fl (.app f a') v := by
  intro h
  cases h with
  | beta hf ha hb => exact .beta hf ((eval_deterministic h1 ha) ▸ h2) hb
  | app_box hf ha => exact .app_box hf ((eval_deterministic h1 ha) ▸ h2)
  | construct_app hb hf hc hlt ha =>
      exact .construct_app hb hf hc hlt ((eval_deterministic h1 ha) ▸ h2)
  | fix_guarded hg hf ha hs hp hu =>
      exact .fix_guarded hg hf ((eval_deterministic h1 ha) ▸ h2) hs hp hu
  | fix_stuck hg hf ha hs hlt =>
      exact .fix_stuck hg hf ((eval_deterministic h1 ha) ▸ h2) hs hlt
  | fix_unguarded hg hf hs ha hu =>
      exact .fix_unguarded hg hf hs ((eval_deterministic h1 ha) ▸ h2) hu
  | app_cong hf hst ha => exact .app_cong hf hst ((eval_deterministic h1 ha) ▸ h2)

/-- Replacing every argument by one with the same value preserves evaluation. -/
theorem wcbvEval_mkApps_args_swap {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {as bs vs : List LBTerm}, EvalArgs Γ fl as vs → EvalArgs Γ fl bs vs →
      ∀ {f r : LBTerm}, WcbvEval Γ fl (LBTerm.mkApps f as) r →
        WcbvEval Γ fl (LBTerm.mkApps f bs) r
  | _, _, _, .nil, .nil, _, _, h => h
  | _, _, _, .cons ha hrest, .cons hb hrest', f, r, h =>
      wcbvEval_mkApps_args_swap hrest hrest'
        (wcbvEval_mkApps_head_congr _ (fun hv => wcbvEval_app_arg_swap ha hb hv) h)

/-- Inverting a `case` at applied-constructor flags on a non-propositional inductive:
only the ι rule applies. -/
theorem wcbvEval_case_inv {Γ : GlobalDeclarations} {fl : WcbvFlags} {iid : InductiveId}
    {np : Nat} {d : LBTerm} {alts : List (List BinderName × LBTerm)} {r : LBTerm}
    (hbl : fl.with_constructor_as_block = false)
    (hprop : isPropositionalInductive Γ iid = false)
    (h : WcbvEval Γ fl (.case (iid, np) d alts) r) :
    ∃ (k : Nat) (args : List LBTerm) (names : List BinderName) (body : LBTerm),
      WcbvEval Γ fl d (LBTerm.mkApps (.construct iid k []) args) ∧
        alts[k]? = some (names, body) ∧ (args.drop np).length = names.length ∧
        WcbvEval Γ fl (LBTerm.substList ((args.drop np).reverse) body) r := by
  cases h with
  | iota _ _ hd hsel hlen hbody => exact ⟨_, _, _, _, hd, hsel, hlen, hbody⟩
  | iota_block hb _ _ _ _ _ => rw [hbl] at hb; exact absurd hb (by simp)
  | iota_sing _ hp _ _ => rw [hprop] at hp; exact absurd hp (by simp)

/-! ### The β-chain of a λ-telescope -/

/-- Applying a λ-telescope to a full argument list: the arguments evaluate and the body
follows with them substituted. -/
theorem wcbvEval_mkLambdas_fwd {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (as : List LBTerm) {ns : List BinderName} {body : LBTerm}, ns.length = as.length →
      ∀ {r : LBTerm}, WcbvEval Γ fl (LBTerm.mkApps (mkLambdas ns body) as) r →
        ∃ vs, EvalArgs Γ fl as vs ∧ WcbvEval Γ fl (substTele 0 vs body) r
  | [], ns, body, hlen, r, h => by
      obtain rfl : ns = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact ⟨[], .nil, h⟩
  | a :: as, ns, body, hlen, r, h => by
      cases ns with
      | nil => simp at hlen
      | cons n ns =>
          have hlen' : ns.length = as.length := by simpa using hlen
          rw [mkLambdas, LBTerm.mkApps] at h
          obtain ⟨⟨w, hw⟩, -⟩ := wcbvEval_mkApps_inv as h
          obtain ⟨-, ⟨av, hav⟩⟩ := wcbvEval_app_inv hw
          have h2 := wcbvEval_mkApps_head_congr as
            (fun hv => (wcbvEval_beta_step hav).mp hv) h
          rw [LBTerm.subst1, subst_mkLambdas, Nat.zero_add] at h2
          obtain ⟨vs, hvs, hres⟩ := wcbvEval_mkLambdas_fwd as (ns := ns)
            (body := LBTerm.subst av ns.length body) hlen' h2
          refine ⟨av :: vs, .cons hav hvs, ?_⟩
          show WcbvEval Γ fl (substTele 0 vs (LBTerm.subst av (vs.length + 0) body)) r
          rw [Nat.add_zero, ← hvs.length_eq, ← hlen']
          exact hres

/-- The converse: a value list for the arguments turns the substituted body's evaluation
into the application's. -/
theorem wcbvEval_mkLambdas_bwd {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {as vs : List LBTerm}, EvalArgs Γ fl as vs → ∀ {ns : List BinderName} {body r : LBTerm},
      ns.length = as.length → WcbvEval Γ fl (substTele 0 vs body) r →
        WcbvEval Γ fl (LBTerm.mkApps (mkLambdas ns body) as) r
  | [], _, .nil, ns, body, r, hlen, h => by
      obtain rfl : ns = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact h
  | a :: as, _, .cons (v := v) (vs := vs) hav hrest, ns, body, r, hlen, h => by
      cases ns with
      | nil => simp at hlen
      | cons n ns =>
          have hlen' : ns.length = as.length := by simpa using hlen
          have h' : WcbvEval Γ fl (substTele 0 vs (LBTerm.subst v ns.length body)) r := by
            rw [hlen', hrest.length_eq]
            exact h
          have hres := wcbvEval_mkLambdas_bwd hrest (body := LBTerm.subst v ns.length body)
            hlen' h'
          rw [mkLambdas, LBTerm.mkApps]
          refine wcbvEval_mkApps_head_congr as (fun hv => ?_) hres
          refine (wcbvEval_beta_step hav).mpr ?_
          rw [LBTerm.subst1, subst_mkLambdas, Nat.zero_add]
          exact hv

/-- The β-chain fills the field slots of a spine whose head is lifted over them. -/
theorem substTele_fields : ∀ (vs : List LBTerm) (H : LBTerm),
    substTele 0 vs (LBTerm.mkApps (LBTerm.shift vs.length 0 H) (fieldArgs vs.length))
      = LBTerm.mkApps H vs
  | [], H => by
      show LBTerm.mkApps (LBTerm.shift 0 0 H) [] = _
      rw [LBTerm.shift_zero]
  | v :: vs, H => by
      show substTele 0 vs (LBTerm.subst v (vs.length + 0)
        (LBTerm.mkApps (.app (LBTerm.shift (vs.length + 1) 0 H) (.bvar vs.length))
          (fieldArgs vs.length))) = _
      rw [Nat.add_zero, LBTerm.subst_spine, fieldArgs_subst_eq (Nat.le_refl _)]
      show substTele 0 vs (LBTerm.mkApps (.app (LBTerm.subst v vs.length
        (LBTerm.shift (vs.length + 1) 0 H)) (LBTerm.subst v vs.length (.bvar vs.length)))
          (fieldArgs vs.length)) = _
      rw [LBTerm.subst_shift_cancel v vs.length 0 vs.length (Nat.zero_le _)
          (Nat.le_of_eq (Nat.zero_add _).symm),
        LBTerm.subst_bvar, if_neg (by omega), if_pos rfl,
        show LBTerm.app (LBTerm.shift vs.length 0 H) (LBTerm.shift vs.length 0 v)
          = LBTerm.shift vs.length 0 (.app H v) from rfl,
        substTele_fields vs (.app H v)]
      rfl

theorem EvalArgs.self {Γ : GlobalDeclarations} {fl : WcbvFlags} {as vs : List LBTerm} :
    EvalArgs Γ fl as vs → EvalArgs Γ fl vs vs
  | .nil => .nil
  | .cons ha hr => .cons (eval_self ha) hr.self

/-! ## The β and ι theorems -/

/-- **The η-expanded constructor body is the constructor.** Applying `mkCtorBody` to a
full argument list has exactly the evaluations of the applied-form constructor spine. -/
theorem mkCtorBody_beta {Γ : GlobalDeclarations} {fl : WcbvFlags} {iid : InductiveId} {k : Nat}
    {ns : List BinderName} {args : List LBTerm} {r : LBTerm} (h : args.length = ns.length) :
    WcbvEval Γ fl (LBTerm.mkApps (mkCtorBody iid k ns) args) r ↔
      WcbvEval Γ fl (LBTerm.mkApps (.construct iid k []) args) r := by
  have hctor : ∀ vs : List LBTerm,
      substTele 0 vs (LBTerm.mkApps (.construct iid k []) (fieldArgs vs.length))
        = LBTerm.mkApps (.construct iid k []) vs :=
    fun vs => substTele_fields vs (.construct iid k [])
  constructor
  · intro hev
    rw [mkCtorBody] at hev
    obtain ⟨vs, hvs, hres⟩ := wcbvEval_mkLambdas_fwd args h.symm hev
    have hlen : vs.length = ns.length := by rw [← hvs.length_eq, h]
    rw [← hlen, hctor vs] at hres
    exact wcbvEval_mkApps_args_swap hvs.self hvs hres
  · intro hev
    obtain ⟨-, hargs⟩ := wcbvEval_mkApps_inv args hev
    obtain ⟨vs, hvs⟩ := EvalArgs.of_forall_exists args hargs
    have hres : WcbvEval Γ fl (LBTerm.mkApps (.construct iid k []) vs) r :=
      wcbvEval_mkApps_args_swap hvs hvs.self hev
    have hlen : vs.length = ns.length := by rw [← hvs.length_eq, h]
    rw [mkCtorBody]
    refine wcbvEval_mkLambdas_bwd hvs h.symm ?_
    rw [← hlen, hctor vs]
    exact hres

/-- **`mkElimBody` reproduces `iota_red`, forwards.** A saturated application of the
eliminator body to a constructor spine evaluates like the selected minor applied to the
constructor's fields. Four guards beyond the side condition itself: the spine has the
eliminator's shape (`hplen`, `hmlen`); the discriminant spine is a value (`hval`), else
the ι rule sees the arguments' *values*; the fields are closed (`hfields`), else the
sequential `substList` captures a field in a later one
(`mkElimBody_iota_needs_closed_fields`). -/
theorem mkElimBody_iota_fwd {Γ : GlobalDeclarations} {fl : WcbvFlags} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {k : Nat} {args minors pre : List LBTerm} {r : LBTerm}
    (hbl : fl.with_constructor_as_block = false)
    (hplen : pre.length = dp) (hmlen : minors.length = nfs.length)
    (hk : k < nfs.length) (harity : (args.drop np).length = nfs[k]!)
    (hfields : ∀ a ∈ args.drop np, LBClosed a 0)
    (hval : WcbvEval Γ fl (LBTerm.mkApps (.construct iid k []) args)
              (LBTerm.mkApps (.construct iid k []) args))
    (hprop : isPropositionalInductive Γ iid = false) :
    WcbvEval Γ fl (LBTerm.mkApps (mkElimBody iid np dp nfs)
        (pre ++ LBTerm.mkApps (.construct iid k []) args :: minors)) r →
      WcbvEval Γ fl (LBTerm.mkApps minors[k]! (args.drop np)) r := by
  intro h
  rw [mkElimBody] at h
  obtain ⟨vs, hvs, hres⟩ := wcbvEval_mkLambdas_fwd _
    (by simp only [List.length_replicate, List.length_append, List.length_cons, hplen, hmlen];
        omega) h
  obtain ⟨pv, ws, rfl, -, hws⟩ := hvs.append_inv
  cases hws with
  | @cons _ dv _ mvs hdisc hmvs =>
      have hdv : LBTerm.mkApps (.construct iid k []) args = dv := eval_deterministic hval hdisc
      subst hdv
      have hm : mvs.length = nfs.length := by rw [← hmvs.length_eq, hmlen]
      have hk' : k < minors.length := by rw [hmlen]; exact hk
      rw [substTele_elimBody iid np nfs pv _ mvs hm] at hres
      obtain ⟨k', args', names, body, hd, hsel, -, hbody⟩ := wcbvEval_case_inv hbl hprop hres
      obtain ⟨-, rfl, rfl⟩ := LBTerm.mkApps_construct_inj (eval_deterministic hval hd)
      rw [elimAltsSub_getElem? nfs mvs hm.symm hk] at hsel
      injection Option.some.inj hsel with hnames hbodyeq
      subst hnames
      subst hbodyeq
      rw [← harity, substList_reverse_fields (args.drop np) hfields] at hbody
      exact wcbvEval_mkApps_head_swap (eval_self (hmvs.get hk')) (hmvs.get hk') _ hbody

/-- **`mkElimBody` reproduces `iota_red`, backwards.** The direction a forward simulation
consumes. β evaluates every argument, so the dropped arguments and the non-selected
minors must evaluate (`hpre`, `hmin`); the other guards are `mkElimBody_iota_fwd`'s. -/
theorem mkElimBody_iota_bwd {Γ : GlobalDeclarations} {fl : WcbvFlags} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {k : Nat} {args minors pre : List LBTerm} {r : LBTerm}
    (hbl : fl.with_constructor_as_block = false)
    (hplen : pre.length = dp) (hmlen : minors.length = nfs.length)
    (hk : k < nfs.length) (harity : (args.drop np).length = nfs[k]!)
    (hfields : ∀ a ∈ args.drop np, LBClosed a 0)
    (hval : WcbvEval Γ fl (LBTerm.mkApps (.construct iid k []) args)
              (LBTerm.mkApps (.construct iid k []) args))
    (hprop : isPropositionalInductive Γ iid = false)
    (hpre : ∀ a ∈ pre, ∃ av, WcbvEval Γ fl a av)
    (hmin : ∀ m ∈ minors, ∃ mv, WcbvEval Γ fl m mv) :
    WcbvEval Γ fl (LBTerm.mkApps minors[k]! (args.drop np)) r →
      WcbvEval Γ fl (LBTerm.mkApps (mkElimBody iid np dp nfs)
        (pre ++ LBTerm.mkApps (.construct iid k []) args :: minors)) r := by
  intro h
  obtain ⟨pv, hpv⟩ := EvalArgs.of_forall_exists pre hpre
  obtain ⟨mvs, hmvs⟩ := EvalArgs.of_forall_exists minors hmin
  have hm : mvs.length = nfs.length := by rw [← hmvs.length_eq, hmlen]
  have hk' : k < minors.length := by rw [hmlen]; exact hk
  have h1 : WcbvEval Γ fl (LBTerm.mkApps mvs[k]! (args.drop np)) r :=
    wcbvEval_mkApps_head_swap (hmvs.get hk') (eval_self (hmvs.get hk')) _ h
  have h2 : WcbvEval Γ fl (LBTerm.substList ((args.drop np).reverse)
      (LBTerm.mkApps (LBTerm.shift nfs[k]! 0 mvs[k]!) (fieldArgs nfs[k]!))) r := by
    rw [← harity, substList_reverse_fields (args.drop np) hfields]
    exact h1
  have h3 : WcbvEval Γ fl (.case (iid, np) (LBTerm.mkApps (.construct iid k []) args)
      (elimAltsSub nfs mvs)) r :=
    .iota hbl hprop hval (elimAltsSub_getElem? nfs mvs hm.symm hk)
      (by simp only [List.length_replicate]; exact harity) h2
  rw [mkElimBody]
  refine wcbvEval_mkLambdas_bwd (hpv.append (.cons hval hmvs))
    (by simp only [List.length_replicate, List.length_append, List.length_cons, hplen, hmlen];
        omega) ?_
  rw [substTele_elimBody iid np nfs pv _ mvs hm]
  exact h3

/-! ## Checked instances

Three eliminators of the shipping fragment, at the `(np, dp, nfs)` their Lean
declarations have, each with its `ElimBody` shape and its ι theorem **fired** on a
concrete constructor — so the alternatives' de Bruijn arithmetic is exercised, not only
stated. `Decidable.casesOn` carries a parameter, so its ι drops one argument before the
fields.
-/

/-- `Nat`: no parameters, `zero` with no fields, `succ` with one. -/
def natIid : InductiveId := { mutualBlockName := rootKername "Nat", idx := 0 }

def natΓ : GlobalDeclarations :=
  [(rootKername "Nat", .inductiveDecl
      { npars := 0,
        bodies := [{ name := "Nat", ctors := [{ name := "zero", nargs := 0 },
                                              { name := "succ", nargs := 1 }],
                     projs := [] }] })]

/-- `Nat.casesOn`: one dropped argument (the motive), two minors of `0` and `1` fields. -/
theorem natCasesOn_elimBody : ElimBody natIid 0 1 [0, 1] (mkElimBody natIid 0 1 [0, 1]) := .cases

/-- The `succ` branch of `Nat.casesOn` fires and receives the field: applying the body to
a motive, `succ □`, the zero minor `□` and the successor minor `λ n. n` yields `□`. -/
theorem natCasesOn_iota_fires :
    WcbvEval natΓ eraseFlags
      (LBTerm.mkApps (mkElimBody natIid 0 1 [0, 1])
        [.box, LBTerm.mkApps (.construct natIid 1 []) [.box], .box,
          .lambda (.named "n") (.bvar 0)]) .box := by
  have harity : constructorArity natΓ natIid 1 = some 1 := rfl
  have hval : WcbvEval natΓ eraseFlags (LBTerm.mkApps (.construct natIid 1 []) [.box])
      (LBTerm.mkApps (.construct natIid 1 []) [.box]) :=
    WcbvEval.construct_app (Γ := natΓ) (fl := eraseFlags) (a := .box) (args := [])
      rfl (.construct_atom rfl harity) harity (by decide) .box
  refine mkElimBody_iota_bwd (Γ := natΓ) (fl := eraseFlags) (iid := natIid) (np := 0) (dp := 1)
    (nfs := [0, 1]) (pre := [.box]) (minors := [.box, .lambda (.named "n") (.bvar 0)])
    (args := [.box]) (k := 1) rfl rfl rfl (by decide) rfl ?_ hval rfl ?_ ?_ ?_
  · intro a ha; rw [List.mem_singleton.mp ha]; trivial
  · intro a ha; rw [List.mem_singleton.mp ha]; exact ⟨.box, .box⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨.box, .box⟩
    · rw [List.mem_singleton.mp hm]; exact ⟨_, .lam _ _⟩
  · exact .beta (.lam _ _) .box .box

/-- `Bool`: no parameters, two field-free constructors. -/
def boolIid : InductiveId := { mutualBlockName := rootKername "Bool", idx := 0 }

def boolΓ : GlobalDeclarations :=
  [(rootKername "Bool", .inductiveDecl
      { npars := 0,
        bodies := [{ name := "Bool", ctors := [{ name := "false", nargs := 0 },
                                               { name := "true", nargs := 0 }],
                     projs := [] }] })]

/-- `Bool.casesOn`: one dropped argument, two field-free minors. -/
theorem boolCasesOn_elimBody : ElimBody boolIid 0 1 [0, 0] (mkElimBody boolIid 0 1 [0, 0]) :=
  .cases

/-- The `false` branch of `Bool.casesOn` fires: the first minor is returned and the
second is not. -/
theorem boolCasesOn_iota_fires :
    WcbvEval boolΓ eraseFlags
      (LBTerm.mkApps (mkElimBody boolIid 0 1 [0, 0])
        [.box, .construct boolIid 0 [], .lambda (.named "x") .box, .box])
      (.lambda (.named "x") .box) := by
  have harity : constructorArity boolΓ boolIid 0 = some 0 := rfl
  refine mkElimBody_iota_bwd (Γ := boolΓ) (fl := eraseFlags) (iid := boolIid) (np := 0) (dp := 1)
    (nfs := [0, 0]) (pre := [.box]) (minors := [.lambda (.named "x") .box, .box])
    (args := []) (k := 0) rfl rfl rfl (by decide) rfl ?_ (.construct_atom rfl harity) rfl
    ?_ ?_ ?_
  · intro a ha; exact absurd ha (by simp)
  · intro a ha; rw [List.mem_singleton.mp ha]; exact ⟨.box, .box⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, .lam _ _⟩
    · rw [List.mem_singleton.mp hm]; exact ⟨.box, .box⟩
  · exact .lam _ _

/-- `Decidable`: one parameter, `isFalse` and `isTrue`, each with one field. -/
def decIid : InductiveId := { mutualBlockName := rootKername "Decidable", idx := 0 }

def decΓ : GlobalDeclarations :=
  [(rootKername "Decidable", .inductiveDecl
      { npars := 1,
        bodies := [{ name := "Decidable", ctors := [{ name := "isFalse", nargs := 1 },
                                                    { name := "isTrue", nargs := 1 }],
                     projs := [] }] })]

/-- `Decidable.casesOn`: two dropped arguments (the parameter and the motive), two minors
of one field each. -/
theorem decCasesOn_elimBody : ElimBody decIid 1 2 [1, 1] (mkElimBody decIid 1 2 [1, 1]) := .cases

/-- The `isTrue` branch of `Decidable.casesOn` fires and receives the *field* only: the
constructor's parameter is dropped by `np = 1` before the fields reach the minor. -/
theorem decCasesOn_iota_fires :
    WcbvEval decΓ eraseFlags
      (LBTerm.mkApps (mkElimBody decIid 1 2 [1, 1])
        [.box, .box, LBTerm.mkApps (.construct decIid 1 []) [.box, .box], .box,
          .lambda (.named "h") (.bvar 0)]) .box := by
  have harity : constructorArity decΓ decIid 1 = some 2 := rfl
  have h1 : WcbvEval decΓ eraseFlags (LBTerm.mkApps (.construct decIid 1 []) [.box])
      (LBTerm.mkApps (.construct decIid 1 []) [.box]) :=
    WcbvEval.construct_app (Γ := decΓ) (fl := eraseFlags) (a := .box) (args := [])
      rfl (.construct_atom rfl harity) harity (by decide) .box
  have hval : WcbvEval decΓ eraseFlags (LBTerm.mkApps (.construct decIid 1 []) [.box, .box])
      (LBTerm.mkApps (.construct decIid 1 []) [.box, .box]) :=
    WcbvEval.construct_app (Γ := decΓ) (fl := eraseFlags) (a := .box) (args := [.box])
      rfl h1 harity (by decide) .box
  refine mkElimBody_iota_bwd (Γ := decΓ) (fl := eraseFlags) (iid := decIid) (np := 1) (dp := 2)
    (nfs := [1, 1]) (pre := [.box, .box])
    (minors := [.box, .lambda (.named "h") (.bvar 0)]) (args := [.box, .box]) (k := 1)
    rfl rfl rfl (by decide) rfl ?_ hval rfl ?_ ?_ ?_
  · intro a ha; rw [List.mem_singleton.mp ha]; trivial
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨.box, .box⟩
    · rw [List.mem_singleton.mp ha]; exact ⟨.box, .box⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨.box, .box⟩
    · rw [List.mem_singleton.mp hm]; exact ⟨_, .lam _ _⟩
  · exact .beta (.lam _ _) .box .box

/-! ## The ι theorems' extra guards are not slack

Two of `mkElimBody_iota_fwd`'s guards are refuted as removable by computation, through
`lbEval` and `lbEval_sound`: the spine-shape guard `hmlen` and the field-closedness guard
`hfields`. (The third added guard, `hval`, is what makes the theorem's `args` the fields
the ι rule actually sees rather than terms evaluating to them.)
-/

def ceKn : Kername := { mp := .MPfile [], id := "CE" }

def ceIid : InductiveId := { mutualBlockName := ceKn, idx := 0 }

/-- One inductive, one constructor, two fields. -/
def ceΓ : GlobalDeclarations :=
  [(ceKn, .inductiveDecl
      { npars := 0,
        bodies := [{ name := "CE", ctors := [{ name := "mk", nargs := 2 }], projs := [] }] })]

/-- Two field values, the second with a loose de Bruijn index: a `WcbvEval` value that is
not `LBClosed`. -/
def ceArgs : List LBTerm := [.box, .lambda (.named "z") (.bvar 1)]

/-- The minor that returns its *second* field. -/
def ceMinor : LBTerm := .lambda (.named "a") (.lambda (.named "b") (.bvar 0))

/-- **`hfields` is necessary.** With a field carrying a loose index, the ι rule's
sequential `substList` substitutes the first field *into* the second: the eliminator
application yields `λ z. □` while the minor applied to the fields yields `λ z. #1`. -/
theorem mkElimBody_iota_needs_closed_fields :
    WcbvEval ceΓ eraseFlags
        (LBTerm.mkApps (mkElimBody ceIid 0 0 [2])
          [LBTerm.mkApps (.construct ceIid 0 []) ceArgs, ceMinor])
        (.lambda (.named "z") .box) ∧
      ¬ WcbvEval ceΓ eraseFlags (LBTerm.mkApps ceMinor ceArgs) (.lambda (.named "z") .box) := by
  refine ⟨lbEval_sound (n := 20) rfl, fun h => ?_⟩
  have h2 : WcbvEval ceΓ eraseFlags (LBTerm.mkApps ceMinor ceArgs)
      (.lambda (.named "z") (.bvar 1)) := lbEval_sound (n := 20) rfl
  exact absurd (eval_deterministic h h2) (by simp)

/-- The same inductive with a field-free constructor. -/
def ce2Γ : GlobalDeclarations :=
  [(ceKn, .inductiveDecl
      { npars := 0,
        bodies := [{ name := "CE", ctors := [{ name := "mk", nargs := 0 }], projs := [] }] })]

/-- **`hmlen` is necessary.** With no minors supplied for a one-constructor inductive the
application is under-applied and evaluates to a λ, while the conclusion's
`minors[k]!` is the `Inhabited` default `□`. -/
theorem mkElimBody_iota_needs_minor_count :
    WcbvEval ce2Γ eraseFlags
        (LBTerm.mkApps (mkElimBody ceIid 0 0 [0]) ([] ++ (.construct ceIid 0 []) :: []))
        (.lambda .anon (.case (ceIid, 0) (.construct ceIid 0 []) [([], .bvar 0)])) ∧
      ¬ WcbvEval ce2Γ eraseFlags (LBTerm.mkApps ([] : List LBTerm)[0]! (([] : List LBTerm).drop 0))
        (.lambda .anon (.case (ceIid, 0) (.construct ceIid 0 []) [([], .bvar 0)])) := by
  refine ⟨lbEval_sound (n := 20) rfl, fun h => ?_⟩
  have h' : WcbvEval ce2Γ eraseFlags .box
      (.lambda .anon (.case (ceIid, 0) (.construct ceIid 0 []) [([], .bvar 0)])) := h
  cases h'

end LeanToLambdaBox
