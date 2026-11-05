import EraseProof.Oracle.Whnf
import EraseProof.Bridge.CasesWhred

/-!
# The oracle's type of a saturated recursor spine

`Pure.inferType_recr`: on a spine of a recursor with exactly its `recrEnd` arguments, the oracle's
type is the motive applied to the indices and the major, which translates to the type of the
Metalean recursor node. The oracle instantiates the recursor's declared type one argument at a time;
the declared type has `recrEnd` syntactic `Π`s over `motive_s indices major` (`IndBlock.recrType`),
so each `whnf` it takes leaves the `Π` unchanged and the result is that body with the arguments
substituted (`spine_type`). No argument needs a type: the minors, which the node holds wrapped by
`wrapCase`, do not occur in the result.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRed WHRedS)

namespace EraseProof

namespace OracleInfer

/-! ## Instantiation of the leading binders of a type -/

/-- Instantiating at depth `s + d` a term lifted by `d + 1` from `s` lowers it by one. -/
theorem inst_lift (a : Expr) : ∀ (x : Expr) (s d : Nat),
    (x.liftLooseBVars' s (d + 1)).instantiate1' a (s + d) = x.liftLooseBVars' s d
  | .bvar i, s, d => by
    by_cases hi : i < s
    · simp [Expr.liftLooseBVars', Expr.instantiate1', hi, show i < s + d by omega]
    · simp only [Expr.liftLooseBVars', hi, ite_false, Expr.instantiate1',
        show ¬ i + (d + 1) < s + d by omega, show ¬ i + (d + 1) = s + d by omega]
      all_goals congr 1
  | .app f b, s, d => by simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a f, inst_lift a b]
  | .lam _ t b _, s, d => by
    have hb := inst_lift a b (s + 1) d
    rw [show s + 1 + d = s + d + 1 by omega] at hb
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a t, hb]
  | .forallE _ t b _, s, d => by
    have hb := inst_lift a b (s + 1) d
    rw [show s + 1 + d = s + d + 1 by omega] at hb
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a t, hb]
  | .letE _ t v b _, s, d => by
    have hb := inst_lift a b (s + 1) d
    rw [show s + 1 + d = s + d + 1 by omega] at hb
    simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a t, inst_lift a v, hb]
  | .mdata _ e, s, d => by simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a e]
  | .proj _ _ e, s, d => by simp only [Expr.liftLooseBVars', Expr.instantiate1', inst_lift a e]
  | .const .., _, _ | .sort _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .lit _, _, _ => rfl

/-- The body of a type under `k` binders after their instantiation with `as` (first argument
outermost), `d` binders remaining above: `as` substituted for the bound variables `d …
d + as.length - 1`. -/
def instSeq (body : Expr) : List Expr → Nat → Expr
  | [], _ => body
  | a :: as, d => instSeq (body.instantiate1' a (d + as.length)) as d

/-- `instSeq` of one more argument: the last one is substituted at the depth `d`. -/
theorem instSeq_append (a : Expr) : ∀ (as : List Expr) (body : Expr) (d : Nat),
    instSeq body (as ++ [a]) d = (instSeq body as (d + 1)).instantiate1' a d
  | [], _, _ => rfl
  | x :: as, body, d => by
    simp only [List.cons_append, instSeq, List.length_append, List.length_singleton]
    rw [instSeq_append a as, show d + (as.length + 1) = d + 1 + as.length by omega]

/-- A term lifted over the substituted binders is unchanged by `instSeq` but for the lift. -/
theorem instSeq_lift (x : Expr) : ∀ (as : List Expr) (d : Nat),
    instSeq (x.liftLooseBVars' 0 (d + as.length)) as d = x.liftLooseBVars' 0 d
  | [], _ => by simp [instSeq]
  | y :: as, d => by
    simp only [instSeq, List.length_cons]
    have h := inst_lift y x 0 (d + as.length)
    rw [Nat.zero_add] at h
    rw [show d + (as.length + 1) = d + as.length + 1 by omega, h, instSeq_lift x as d]

/-- `instSeq` on a bound variable of the substituted range is its argument, lifted by `d`. -/
theorem instSeq_bvar : ∀ (as : List Expr) (d j : Nat) (hj : d ≤ j) (hl : j < d + as.length),
    instSeq (.bvar j) as d =
      (as[as.length - 1 - (j - d)]'(by omega)).liftLooseBVars' 0 d
  | [], _, _, hj, hl => by simp at hl; omega
  | x :: as, d, j, hj, hl => by
    simp only [instSeq, List.length_cons] at hl ⊢
    by_cases hlt : j < d + as.length
    · have h1 : (Expr.bvar j).instantiate1' x (d + as.length) = .bvar j := by
        simp [Expr.instantiate1', hlt]
      rw [h1, instSeq_bvar as d j hj hlt]
      have hi : as.length + 1 - 1 - (j - d) = (as.length - 1 - (j - d)) + 1 := by omega
      simp only [hi, List.getElem_cons_succ]
    · have hj' : j = d + as.length := by omega
      subst hj'
      have h1 : (Expr.bvar (d + as.length)).instantiate1' x (d + as.length) =
          x.liftLooseBVars' 0 (d + as.length) := by
        simp [Expr.instantiate1']
      rw [h1, instSeq_lift]
      simp

/-- `instSeq` commutes with application. -/
theorem instSeq_app : ∀ (as : List Expr) (f b : Expr) (d : Nat),
    instSeq (.app f b) as d = .app (instSeq f as d) (instSeq b as d)
  | [], _, _, _ => rfl
  | x :: as, f, b, d => by simp only [instSeq, Expr.instantiate1']; exact instSeq_app as _ _ d

/-- `instSeq` commutes with application spines. -/
theorem instSeq_mkAppN (as : List Expr) (d : Nat) : ∀ (xs : List Expr) (h : Expr),
    instSeq (mkAppN h xs.toArray) as d = mkAppN (instSeq h as d) (xs.map (instSeq · as d)).toArray
  | [], _ => rfl
  | x :: xs, h => by
    have := instSeq_mkAppN as d xs (.app h x)
    simp only [mkAppN_eq_foldl, List.foldl_cons, List.map_cons] at this ⊢
    rw [this, instSeq_app]

/-! ## `peelForalls` -/

/-- `peelForalls 0` is the type itself. -/
theorem peelForalls_zero (e : Expr) : peelForalls 0 e = some e := rfl

/-- `peelForalls` of a `Π` enters its body. -/
theorem peelForalls_forallE (k : Nat) (x : Name) (A b : Expr) (bi : BinderInfo) :
    peelForalls (k + 1) (.forallE x A b bi) = peelForalls k b := by
  simp only [peelForalls, Function.iterate_succ_apply]
  rfl

/-- A type with `k + 1` leading `Π`s is a `Π` whose body has `k`. -/
theorem peelForalls_succ {k : Nat} {e body : Expr} (h : peelForalls (k + 1) e = some body) :
    ∃ x A b bi, e = .forallE x A b bi ∧ peelForalls k b = some body := by
  cases e with
  | forallE x A b bi => exact ⟨x, A, b, bi, rfl, by rwa [peelForalls_forallE] at h⟩
  | _ =>
    simp only [peelForalls, Function.iterate_succ_apply] at h
    simp only [Option.bind_some, Expr.isForall, Bool.false_eq_true, ite_false] at h
    rw [Function.iterate_fixed rfl] at h
    cases h

/-- `peelForalls` commutes with instantiation (the depth grows by the binders entered). -/
theorem peelForalls_inst (a : Expr) : ∀ (k : Nat) (e body : Expr) (d : Nat),
    peelForalls k e = some body →
      peelForalls k (e.instantiate1' a d) = some (body.instantiate1' a (d + k))
  | 0, e, body, d, h => by cases h; rfl
  | k + 1, e, body, d, h => by
    obtain ⟨x, A, b, bi, rfl, hb⟩ := peelForalls_succ h
    simp only [Expr.instantiate1']
    rw [peelForalls_forallE, peelForalls_inst a k b body (d + 1) hb]
    congr 2; omega

/-- `peelForalls` commutes with universe instantiation. -/
theorem peelForalls_instLevels (ps : List Name) (us : List Level) :
    ∀ (k : Nat) (e body : Expr), peelForalls k e = some body →
      peelForalls k (Pure.instLevels ps us e) = some (Pure.instLevels ps us body)
  | 0, e, body, h => by cases h; rfl
  | k + 1, e, body, h => by
    obtain ⟨x, A, b, bi, rfl, hb⟩ := peelForalls_succ h
    simp only [Pure.instLevels]
    rw [peelForalls_forallE, peelForalls_instLevels ps us k b body hb]

/-! ## The oracle on a spine whose head's type has enough `Π`s -/

/-- `whnf` leaves a `Π` unchanged. -/
theorem whnf_forallE {cx : Pure.Ctx} {f : Nat} {ls : List Local} {x : Name} {A b w : Expr}
    {bi : BinderInfo} (h : Pure.whnf cx f ls (.forallE x A b bi) = .ok w) :
    w = .forallE x A b bi := by
  cases f with
  | zero => simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | succ f => simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; exact h.symm

/-- The oracle's type of `c as`, when `c`'s declared type has at least `as.length` leading `Π`s:
the declared type with the arguments substituted for the leading binders. -/
theorem spine_type {cx : Pure.Ctx} {ls : List Local} {Γo : List Expr} {c : Name} {us : List Level}
    {k : Nat} {body : Expr}
    (hc : ∀ ci, findConst cx.decls c = some ci → us.length = ci.levelParams.length →
      peelForalls k (Pure.instLevels ci.levelParams us ci.type) = some body) :
    ∀ (as : List Expr) {f : Nat} {T : Expr}, as.length ≤ k →
      Pure.inferType cx f ls Γo (mkAppN (.const c us) as.toArray) = .ok T →
      peelForalls (k - as.length) T = some (instSeq body as (k - as.length)) := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro f T _ h
    cases f with
    | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
    | succ f =>
      simp only [mkAppN_eq_foldl, List.foldl_nil, Pure.inferType] at h
      split at h
      · rename_i ci hci
        split at h
        · rename_i hl
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simpa [instSeq] using hc ci hci (by simpa using hl)
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  | append_singleton as a ih =>
    intro f T hk h
    simp only [List.length_append, List.length_singleton] at hk ⊢
    have happ : mkAppN (.const c us) (as ++ [a]).toArray = .app (mkAppN (.const c us) as.toArray) a := by
      simp only [mkAppN_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [happ] at h
    cases f with
    | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
    | succ f =>
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
      have hp := ih (by omega) h1
      rw [show k - as.length = (k - (as.length + 1)) + 1 by omega] at hp
      obtain ⟨x, A, b, bi, rfl, hb⟩ := peelForalls_succ hp
      have hW := whnf_forallE h2
      subst hW
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [peelForalls_inst a _ b _ 0 hb, instSeq_append, Nat.zero_add]

/-! ## The recursor declarations of the program -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- A weakened recursor binding is a recursor binding. -/
private theorem wk_eq_recr {sig : Metalean.Sig} {ι : Metalean.IndSig} {b : MBinding ζ}
    {η : Metalean.Head (ζ.snoc sig) (.inductive ι)} {s : Fin ι.nsorts} {os : List (List (List Nat))}
    (h : b.wk = .recr η s os) : ∃ η₀ : Metalean.Head ζ (.inductive ι), b = .recr η₀ s os := by
  cases b with
  | recr η₀ s₀ os₀ => simp only [MBinding.wk] at h; cases h; exact ⟨_, rfl⟩
  | _ => cases h

/-- A declaration whose name the table binds to a recursor is a recursor declaration with the
kernel's type shape (`IndBlock.recrType`). -/
theorem ProgEnv.recrType {c : Name} {ci : ConstantInfo} (h : ProgEnv P ζ E B)
    (hc : findDecl P c = some ci) :
    ∀ {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {os : List (List (List Nat))}, B c = some (.recr η s os) →
      ∃ rv, ci = .recInfo rv ∧ peelForalls (ι.recrEnd s) rv.type = some (mkAppN
        (.bvar (ι.recrEnd s - 1 - (ι.nparams + s.val)))
        ((List.range (ι.nindices s + 1)).reverse.map .bvar).toArray) := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ _ _ _ _ _ ih | @defn _ _ _ _ v _ _ _ _ _ _ _ _ _ ih
  | @thm _ _ _ _ v _ _ _ _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ _ _ _ _ _ _ ih =>
    intro ι η s os hB
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      rw [← hn] at hB
      simp only [Binds.set] at hB
      split at hB
      · cases hB
      · exact absurd rfl ‹_›
    · rw [set_wk_ne (Ne.symm ‹_›)] at hB
      obtain ⟨b, hb, hbw⟩ := Option.map_eq_some_iff.mp hB
      obtain ⟨η₀, rfl⟩ := wk_eq_recr hbw
      exact ih hc hb
  | @induct _ _ _ _ ι' _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    intro ι η s os hB
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci' =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨t, hs⟩ | ⟨t, k, hs⟩ | ⟨t, hs⟩ <;> subst hs
      · rw [← hn, CasesWhred.name_recInfo, (hblk.recr t).2.1] at hB
        cases hB
        exact ⟨_, rfl, hblk.recrType t⟩
      · rw [← hn, CasesWhred.name_ctorInfo, (hblk.ctor t k).1] at hB
        cases hB
      · rw [← hn, CasesWhred.name_inductInfo, (hblk.ind t).1] at hB
        cases hB
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      rw [hext c hnot, Binds.wk] at hB
      obtain ⟨b, hb, hbw⟩ := Option.map_eq_some_iff.mp hB
      obtain ⟨η₀, rfl⟩ := wk_eq_recr hbw
      exact ih hc hb
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext hq ih =>
    intro ι η s os hB
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci' =>
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      simp only [List.mem_map, List.mem_reverse] at hm
      obtain ⟨q, hqm, rfl⟩ := hm
      rw [← hn, show (ConstantInfo.quotInfo q).name = q.name from rfl, (hq q hqm).1] at hB
      cases hB
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      rw [hext c hnot, Binds.wk] at hB
      obtain ⟨b, hb, hbw⟩ := Option.map_eq_some_iff.mp hB
      obtain ⟨η₀, rfl⟩ := wk_eq_recr hbw
      exact ih hc hb

end

/-- The binder counts of a recursor. -/
theorem recrEnd_eq (ι : Metalean.IndSig) (s : Fin ι.nsorts) :
    ι.recrEnd s = ι.casesEnd + ι.nindices s + 1 ∧
      ι.casesEnd = ι.nparams + ι.nsorts + Fin.sum ι.nctors := ⟨rfl, rfl⟩

/-- The recursor's type body with the arguments substituted: the motive applied to the indices and
the major. -/
theorem instSeq_recr {ι : Metalean.IndSig} {s : Fin ι.nsorts} (as : List Expr)
    (hlen : as.length = ι.recrEnd s) :
    instSeq (mkAppN (.bvar (ι.recrEnd s - 1 - (ι.nparams + s.val)))
        ((List.range (ι.nindices s + 1)).reverse.map .bvar).toArray) as 0 =
      mkAppN (as[ι.nparams + s.val]'(by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; have := s.isLt; omega))
        ((List.ofFn fun i : Fin (ι.nindices s + 1) =>
          as[ι.casesEnd + i.val]'(by have h1 := (recrEnd_eq ι s).1; have := i.isLt; omega)).toArray) := by
  rw [instSeq_mkAppN, instSeq_bvar as 0 _ (Nat.zero_le _) (by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; omega),
    liftLooseBVars'_zero]
  congr 1
  · congr 1; have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; omega
  · congr 1
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.length_map, List.length_reverse, List.length_range] at hi1
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.getElem_ofFn]
    rw [instSeq_bvar as 0 _ (Nat.zero_le _) (by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; simp only [List.length_range]; omega), liftLooseBVars'_zero]
    congr 1; have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; simp only [List.length_range]; omega

end OracleInfer

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
  {P : List ConstantInfo}

open Metalean OracleInfer in
/-- The oracle's type of a spine of a recursor with exactly `recrEnd` arguments translates to a type
of the spine's image: by `IndBlock.recrType` it is the motive applied to the indices and the major
(`spine_type`, `instSeq_recr`), whose translation (`TrM.apps`) reduces from the type
`motiveResult` of the recursor node (`recr_inv`). The minors are not typed. Reference:
`type_of_typing` (`MR S/PCUICSafeRetyping.v:806`); the kernel's recursor type
(`declare_recursors`, `src/kernel/inductive.cpp`). -/
theorem Pure.inferType_recr (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    {c : Name} {us : List Level} {as : List Lean.Expr} {ι : IndSig} {η : Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {os : List (List (List Nat))} {t T : Expr ζ lps.length n}
    {fuel : Nat} {ls : List Local} {Γo : List Lean.Expr} {A : Lean.Expr}
    (hB : B c = some (.recr η s os)) (hlen : as.length = ι.recrEnd s)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T)
    (h : Pure.inferType cx fuel ls Γo (mkAppN (.const c us) as.toArray) = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A' := by
  have hp := spine_type (k := ι.recrEnd s) (body := mkAppN
      (.bvar (ι.recrEnd s - 1 - (ι.nparams + s.val)))
      ((List.range (ι.nindices s + 1)).reverse.map .bvar).toArray) (fun ci hci _ => by
    obtain ⟨rv, rfl, hrv⟩ := ProgEnv.recrType henv (OracleWhnf.findConst_sub hsub hci) hB
    have := peelForalls_instLevels rv.levelParams us _ _ _ hrv
    simp only [ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.toConstantVal]
    rw [this, mkAppN_eq_foldl, instLevels_foldl, List.map_map]
    rfl) as (by omega) h
  rw [hlen, Nat.sub_self, peelForalls_zero, Option.some.injEq, instSeq_recr as hlen] at hp
  subst hp
  obtain ⟨ls', l, mo, Aimg, mins, harg, -, -, rfl, -⟩ := CasesWhred.trM_recr_inv hB hlen he
  have hget : ∀ i (hi : i < ι.recrEnd s), TrM E B lps Γ Δ (as[i]'(by omega)) (Aimg ⟨i, hi⟩) := by
    intro i hi
    obtain ⟨a, ha, htr⟩ := harg ⟨i, hi⟩
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at ha
    exact ha ▸ htr
  have hmot : TrM E B lps Γ Δ (as[ι.nparams + s.val]'(by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; have := s.isLt; omega))
      (Aimg (IndSig.RecrBinder.motive (s := s) s).resolve) := hget _ (by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; have := s.isLt; omega)
  have hidx : List.Forall₂ (TrM E B lps Γ Δ)
      (List.ofFn fun i : Fin (ι.nindices s + 1) => as[ι.casesEnd + i.val]'(by have h1 := (recrEnd_eq ι s).1; have h2 := (recrEnd_eq ι s).2; have := i.isLt; omega))
      (List.ofFn (fun i => Aimg (IndSig.RecrBinder.index (s := s) i).resolve) ++
        [Aimg (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve]) := by
    refine CasesWhred.forall₂_of_getElem? (by simp) fun i a b ha hb => ?_
    rw [List.getElem?_ofFn] at ha
    split at ha
    · rename_i hi
      cases ha
      by_cases hin : i < ι.nindices s
      · rw [List.getElem?_append_left (by simpa using hin), List.getElem?_ofFn] at hb
        simp only [hin, ↓reduceDIte, Option.some.injEq] at hb
        subst hb
        exact hget _ _
      · rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hb
        simp only [List.length_ofFn, show i - ι.nindices s = 0 by omega] at hb
        cases hb
        have hi' : ι.casesEnd + i = ι.recrEnd s - 1 := by
          have h1 := (recrEnd_eq ι s).1; omega
        have hm : (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve =
            ⟨ι.casesEnd + i, by have h1 := (recrEnd_eq ι s).1; omega⟩ := by
          ext; simp only [IndSig.RecrBinder.resolve, Fin.val_last]; omega
        rw [hm]
        exact hget _ _
    · cases ha
  obtain ⟨A', hA', hred⟩ := TrM.apps hmot hidx
  refine ⟨A', hA', ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hres, hT⟩ := ht.recr_inv
  have ht' := (hT.trans (TypeEq.ofDefEq hres)).conv ht
  have hm : Inductive.motiveResult (Aimg (IndSig.RecrBinder.motive (s := s) s).resolve)
      (fun i => Aimg (IndSig.RecrBinder.index (s := s) i).resolve)
      (Aimg (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve) =
      (Aimg (IndSig.RecrBinder.motive (s := s) s).resolve).appList
        (List.ofFn (fun i => Aimg (IndSig.RecrBinder.index (s := s) i).resolve) ++
          [Aimg (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve]) := by
    rw [TrApps.appList_append, appList_ofFn]; rfl
  rw [hm] at ht' hres
  exact (TypeEq.ofDefEq (WHRedS.defeq hE hΓ hred hres.right)).conv ht'

end

end EraseProof
