import EraseProof.Bridge.Det
import EraseProof.Bridge.InstL

/-!
# Saturation of translated spines

Applying a translation to translated arguments: the translation of the Lean application is
reached from the Metalean application by weak-head reduction (`TrM.apps`). For heads that do not
saturate, the two are equal; a saturating spine that already has its arity takes the new
arguments as extra arguments; a partial spine, whose image is the translator's η-term applied
(`indTerm`, `ctorTerm`, `recrTerm`, `quotTerm`, `ML Frontend/Translate.lean:103-224`), reduces by
β to the node once the arguments reach the arity (`SatTr.append`).
-/

open Lean Erasure
open Metalean (WHRed WHRedS)

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ : Nat}

namespace TrApps

/-- Weak-head reduction under extra arguments. -/
theorem whredS_appList {n : Nat} {x y : Metalean.Expr ζ ℓ n} (h : WHRedS E x y) :
    ∀ rest : List (Metalean.Expr ζ ℓ n), WHRedS E (x.appList rest) (y.appList rest)
  | [] => h
  | a :: rest => whredS_appList (Metalean.WHRedS.frame (.app a) h) rest

/-- A closed λ-telescope, weakened into any context and applied to one argument per binder,
reduces by β to its body with the arguments substituted. -/
theorem closed_lam_apps {n : Nat} : ∀ {k : Nat} (Δ : Metalean.Ctx ζ ℓ 0 k)
    (body : Metalean.Expr ζ ℓ k) (xs : Fin k → Metalean.Expr ζ ℓ n),
    WHRedS E ((Δ.lam body).wkClosed.apps xs) (body.subst xs)
  | 0, .nil, body, xs => by
    simp only [Metalean.Expr.apps_zero, Metalean.Expr.subst_closed]
    exact .refl
  | k + 1, .snoc Δ t, body, xs => by
    rw [Metalean.Expr.apps_last]
    refine (Metalean.WHRedS.frame (.app (xs (Fin.last k)))
      (closed_lam_apps Δ (.lam t body) fun i => xs i.castSucc)).tail ?_
    have h := WHRed.beta (E := E) (t := t.subst fun i => xs i.castSucc)
      (e' := body.subst (Metalean.Subst.lift fun i => xs i.castSucc)) (a := xs (Fin.last k))
    rw [Metalean.Expr.inst_subst_lift] at h
    have hx : Metalean.Subst.extend (fun i : Fin k => xs i.castSucc) (xs (Fin.last k)) = xs :=
      Fin.snoc_init_self xs
    rw [hx] at h
    exact h

/-- Application to two lists in turn. -/
theorem appList_append {n : Nat} (e : Metalean.Expr ζ ℓ n) (l₁ l₂ : List (Metalean.Expr ζ ℓ n)) :
    e.appList (l₁ ++ l₂) = (e.appList l₁).appList l₂ :=
  List.foldl_append ..

/-- A list with at least `K` entries is its first `K` entries followed by the rest. -/
theorem ofFn_take {α : Type} (args : List α) (K : Nat) (h : K ≤ args.length) :
    args = List.ofFn (fun i : Fin K => args[i.val]) ++ args.drop K := by
  conv => lhs; rw [← List.take_append_drop K args]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp

/-- A spine of an η-term past its arity reduces to the body under the first arguments, applied to
the rest. -/
theorem eta_appList {n K : Nat} (Δ : Metalean.Ctx ζ ℓ 0 K) (body : Metalean.Expr ζ ℓ K)
    (args : List (Metalean.Expr ζ ℓ n)) (h : K ≤ args.length) :
    WHRedS E ((Δ.lam body).wkClosed.appList args)
      ((body.subst fun i : Fin K => args[i.val]).appList (args.drop K)) := by
  conv => lhs; rw [ofFn_take args K h]
  rw [appList_append, appList_ofFn]
  exact whredS_appList (closed_lam_apps Δ body _) _

/-- The split of a list at `K` used by `eta_appList`. -/
theorem split_at {α : Type} (args : List α) (K : Nat) (h : K ≤ args.length) :
    ∃ (xs : Fin K → α) (rest : List α), (fun i : Fin K => args[i.val]) = xs ∧ args.drop K = rest ∧
      args = List.ofFn xs ++ rest :=
  ⟨_, _, rfl, rfl, ofFn_take args K h⟩

end TrApps

section
variable {lps : List Name}
open TrApps

/-- `indTerm` (`ML Frontend/Translate.lean:103`) applied past its arity reduces to the type former
node. -/
theorem indEta_sat {n : Nat} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {us : List Level} {ls : Fin ι.nlevels → Metalean.Level lps.length}
    (hls : TrLevels lps us ι.nlevels = some ls) (args : List (Metalean.Expr ζ lps.length n))
    (hK : ι.nparams + ι.nindices s ≤ args.length) :
    ∃ t', SatTr E lps (.ind η s) us args t' ∧
      WHRedS E ((Metalean.Frontend.indTerm (E.get η).block η s ls).wkClosed.appList args) t' := by
  have hr := eta_appList (E := E) (((E.get η).block.argTele s){ls})
    (.ind η s ls (fun p => .var ⟨p.val, by omega⟩) fun i => .var ⟨ι.nparams + i.val, by omega⟩)
    args hK
  obtain ⟨xs, rest, hxs, hrest, hsplit⟩ := split_at args _ hK
  rw [hxs, hrest] at hr
  refine ⟨_, ?_, hr⟩
  rw [hsplit, List.ofFn_add]
  exact SatTr.indSat _ _ rest hls

/-- `quotTerm` (`ML Frontend/Translate.lean:197`) applied past its arity reduces to the quotient
node. -/
theorem quotEta_sat {n : Nat} {η : Metalean.Head ζ .quot} {kind : Metalean.Export.QuotKind}
    {us : List Level} {ls' : List (Metalean.Level lps.length)} {t₀ : Metalean.Expr ζ lps.length 0}
    (hu : us.mapM (TrLevel lps) = some ls')
    (ht : Metalean.Frontend.quotTerm η (E.get η).eqHead kind ls' = .ok t₀)
    (args : List (Metalean.Expr ζ lps.length n)) (hK : quotArity kind ≤ args.length) :
    ∃ t', SatTr E lps (.quot η kind) us args t' ∧ WHRedS E (t₀.wkClosed.appList args) t' := by
  rcases ls' with _ | ⟨u, _ | ⟨v, _ | ⟨w, ls'⟩⟩⟩ <;> cases kind <;> try cases ht
  all_goals
    simp only [quotArity] at hK
    refine ⟨_, ?_, eta_appList _ _ args hK⟩
    obtain ⟨xs, rest, hxs, hrest, hsplit⟩ := split_at args _ hK
    rw [hxs, hrest, hsplit]
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append]
  · exact .quotType hu
  · exact .quotMk hu
  · exact .quotInd hu
  · exact .quotLift hu

/-- The inverse map of `orderMaps?` (`ML Frontend/Translate.lean:73`) reads the order. -/
theorem orderMaps_inv {mo : List Nat} {k : Nat} {π πinv : Fin k → Option (Fin k)}
    (h : Metalean.Frontend.orderMaps? mo k = some (π, πinv)) :
    mo.length = k ∧ ∀ o j, πinv o = some j → mo[o.val]? = some j.val := by
  unfold Metalean.Frontend.orderMaps? at h
  split at h
  · rename_i hl
    cases h
    refine ⟨hl, fun o j hj => ?_⟩
    simp only [Option.bind_eq_some_iff] at hj
    obtain ⟨j', hj', hj⟩ := hj
    split at hj
    · cases hj; exact hj'
    · cases hj
  · cases h

/-- `ctorTerm` (`ML Frontend/Translate.lean:109`) applied past its arity reduces to the constructor
node with the fields in Metalean's order. -/
theorem ctorEta_sat {n : Nat} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {order : List Nat} {us : List Level}
    {ls : Fin ι.nlevels → Metalean.Level lps.length} {t₀ : Metalean.Expr ζ lps.length 0}
    (hls : TrLevels lps us ι.nlevels = some ls)
    (ht : Metalean.Frontend.ctorTerm (E.get η).block η s c ls order = .ok t₀)
    (args : List (Metalean.Expr ζ lps.length n))
    (hK : ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) ≤ args.length) :
    ∃ t', SatTr E lps (.ctor η s c order) us args t' ∧ WHRedS E (t₀.wkClosed.appList args) t' := by
  unfold Metalean.Frontend.ctorTerm at ht
  dsimp only at ht
  rcases hπ : Metalean.Frontend.orderMaps? order
        ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with _ | ⟨π, πinv⟩
  · rw [hπ] at ht; cases ht
  rw [hπ] at ht
  dsimp only at ht
  obtain ⟨hlen, hinv⟩ := orderMaps_inv hπ
  obtain ⟨x, hx⟩ : ∃ x, Metalean.Ctx.permute? (k := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
      (by simp [Nat.add_assoc]) π πinv (((E.get η).block.ctors s c).fieldTele η ls
        (fun p => .var p)) = x := ⟨_, rfl⟩
  rw [hx] at ht
  rcases x with _ | fields'
  · cases ht
  dsimp only at ht
  obtain ⟨y, hy⟩ : ∃ y, Fin.mapM (m := Option) (fun f : Fin (ι.ctors s c).nfields =>
      (do let j ← πinv (Fin.castAdd (ι.ctors s c).nrecFields f)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ lps.length
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, Fin.mapM (m := Option) (fun r : Fin (ι.ctors s c).nrecFields =>
      (do let j ← πinv (Fin.natAdd (ι.ctors s c).nfields r)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ lps.length
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = z := ⟨_, rfl⟩
  rw [hy, hz] at ht
  rcases y with _ | fds
  · cases ht
  rcases z with _ | recFds
  · cases ht
  dsimp only at ht
  cases ht
  have hfds := mapM_option_eq_some hy
  have hrec := mapM_option_eq_some hz
  refine ⟨_, ?_, eta_appList _ _ args hK⟩
  obtain ⟨xs, rest, hxs, hrest, hsplit⟩ := split_at args _ hK
  rw [hxs, hrest, hsplit, List.ofFn_add]
  have hvar : ∀ o (j : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)), πinv o = some j →
      order[o.val]? = some j.val ∧
        (List.ofFn fun i : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) =>
          xs (Fin.natAdd ι.nparams i))[j.val]? = some (xs (Fin.natAdd ι.nparams j)) :=
    fun o j hj => ⟨hinv o j hj, by simp⟩
  refine SatTr.ctorSat _ _ rest (fun f => (fds f).subst xs) (fun r => (recFds r).subst xs) hls
    (by simp) hlen fun o => ?_
  refine Fin.addCases (fun f => ?_) (fun r => ?_) o
  · have h := hfds f
    rcases hj : πinv (Fin.castAdd _ f) with _ | j
    · rw [hj] at h; cases h
    rw [hj] at h
    have h' := Option.some.inj h
    obtain ⟨h₁, h₂⟩ := hvar _ j hj
    exact ⟨j.val, _, h₁, h₂, by simp only [Fin.append_left]; rw [← h']; rfl⟩
  · have h := hrec r
    rcases hj : πinv (Fin.natAdd _ r) with _ | j
    · rw [hj] at h; cases h
    rw [hj] at h
    have h' := Option.some.inj h
    obtain ⟨h₁, h₂⟩ := hvar _ j hj
    exact ⟨j.val, _, h₁, h₂, by simp only [Fin.append_right]; rw [← h']; rfl⟩

/-- `recrTerm` (`ML Frontend/Translate.lean:171`) applied past its arity reduces to the recursor
node with its minors wrapped by `wrapCase`. -/
theorem recrEta_sat {n : Nat} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {orders : List (List (List Nat))} {us us' : List Level}
    {ls : Fin ι.nlevels → Metalean.Level lps.length} {l : Metalean.Level lps.length}
    {mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat} {t₀ : Metalean.Expr ζ lps.length 0}
    (hRL : RecrLevels (E.get η).block lps us l us') (hls : TrLevels lps us' ι.nlevels = some ls)
    (hmo : ∀ t c, (orders[t.val]?.bind (·[c.val]?)) = some (mo t c))
    (ht : Metalean.Frontend.recrTerm (E.get η).block η s ls l mo = .ok t₀)
    (args : List (Metalean.Expr ζ lps.length n)) (hK : ι.recrEnd s ≤ args.length) :
    ∃ t', SatTr E lps (.recr η s orders) us args t' ∧ WHRedS E (t₀.wkClosed.appList args) t' := by
  unfold Metalean.Frontend.recrTerm at ht
  obtain ⟨cs, -, ht⟩ := except_bind_eq_ok ht
  dsimp only at ht
  obtain ⟨m, hm⟩ : ∃ m, Fin.mapM (m := Option)
      (α := fun t => (c : Fin (ι.nctors t)) → Metalean.Expr ζ lps.length (ι.recrEnd s))
      (fun t => Fin.mapM (m := Option) (α := fun _ => Metalean.Expr ζ lps.length (ι.recrEnd s))
        fun c =>
        (Metalean.Frontend.wrapCase (E.get η).block η ls
          (fun p => .var (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => .var (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
          (.var (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve)).toOption) = m := ⟨_, rfl⟩
  rw [hm] at ht
  rcases m with _ | minsB
  · cases ht
  dsimp only at ht
  cases ht
  have hw : ∀ t c, Metalean.Frontend.wrapCase (E.get η).block η ls
      (fun p => .var (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => .var (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
      (.var (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve) = .ok (minsB t c) :=
    fun t c => toOption_eq_some (mapM_option_eq_some (mapM_option_eq_some hm t) c)
  refine ⟨_, ?_, eta_appList _ _ args hK⟩
  obtain ⟨xs, rest, hxs, hrest, hsplit⟩ := split_at args _ hK
  rw [hxs, hrest, hsplit]
  exact SatTr.recrSat mo xs rest (fun t c => (minsB t c).subst xs) hRL hls hmo
    fun t c => wrapCase_subst _ _ _ _ _ _ _ _ xs (hw t c)

/-- A saturating spine with more arguments: its image applied to the new arguments reduces to the
image of the longer spine. -/
theorem SatTr.append {n : Nat} {b : MBinding ζ} {us : List Level}
    {bs : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us bs t) (as : List (Metalean.Expr ζ lps.length n)) :
    ∃ t', SatTr E lps b us (bs ++ as) t' ∧ WHRedS E (t.appList as) t' := by
  cases h with
  | indSat ps is rest hls =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using SatTr.indSat (E := E) ps is (rest ++ as) hls
  | ctorSat ps fs rest fds recFds hls hfs hord hperm =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using
      SatTr.ctorSat (E := E) ps fs (rest ++ as) fds recFds hls hfs hord hperm
  | recrSat mo A rest mins hRL hls hmo hw =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using
      SatTr.recrSat (E := E) mo A (rest ++ as) mins hRL hls hmo hw
  | quotType hu =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using SatTr.quotType (E := E) (rest := _ ++ as) hu
  | quotMk hu =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using SatTr.quotMk (E := E) (rest := _ ++ as) hu
  | quotLift hu =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using SatTr.quotLift (E := E) (rest := _ ++ as) hu
  | quotInd hu =>
    refine ⟨_, ?_, by rw [← appList_append]; exact .refl⟩
    simpa only [List.append_assoc] using SatTr.quotInd (E := E) (rest := _ ++ as) hu
  | @indEta _ _ ι η s _ hls hlt =>
    rw [← appList_append]
    by_cases hk : (bs ++ as).length < ι.nparams + ι.nindices s
    · exact ⟨_, .indEta hls hk, .refl⟩
    · exact indEta_sat hls _ (by omega)
  | @ctorEta _ _ _ ι η s c _ _ hls hlt ht =>
    rw [← appList_append]
    by_cases hk : (bs ++ as).length < ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
    · exact ⟨_, .ctorEta hls hk ht, .refl⟩
    · exact ctorEta_sat hls ht _ (by omega)
  | @recrEta _ _ _ _ ι η s _ _ mo _ hRL hls hmo hlt ht =>
    rw [← appList_append]
    by_cases hk : (bs ++ as).length < ι.recrEnd s
    · exact ⟨_, .recrEta mo hRL hls hmo hk ht, .refl⟩
    · exact recrEta_sat hRL hls hmo ht _ (by omega)
  | @quotEta kind _ _ _ _ _ hu hlt ht =>
    rw [← appList_append]
    by_cases hk : (bs ++ as).length < quotArity kind
    · exact ⟨_, .quotEta hu hk ht, .refl⟩
    · exact quotEta_sat hu ht _ (by omega)

end

section
variable {B : Binds ζ} {lps : List Name}
open TrApps

/-- `Forall₂` relates the entries at each index. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ (i : Nat) a b, l₁[i]? = some a → l₂[i]? = some b → R a b := by
  induction h with
  | nil => intro i a b ha; simp at ha
  | cons hr _ ih =>
    intro i a b ha hb
    cases i with
    | zero => simp at ha hb; subst ha hb; exact hr
    | succ i => exact ih i a b (by simpa using ha) (by simpa using hb)

/-- A term whose head is a constant is a spine of it. -/
theorem eq_mkAppN_of_getAppFn {c : Name} {us : List Level} :
    ∀ {e : Expr}, e.getAppFn = .const c us → ∃ bs : List Expr, e = mkAppN (.const c us) bs.toArray
  | .app f a, h => by
    obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn (e := f) h
    exact ⟨bs ++ [a], by simp only [mkAppN_eq_foldl, List.foldl_append]; rfl⟩
  | .const _ _, h => by cases h; exact ⟨[], rfl⟩
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h | .letE .., h
  | .lit _, h | .mdata .., h | .proj .., h => by cases h

/-- Inversion of the translation of a spine of a saturating constant. -/
theorem TrM.special_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {c : Name} {us : List Level} {bs : List Expr} {b : MBinding ζ}
    {t : Metalean.Expr ζ lps.length n} (hb : B c = some b) (hs : b.isSpecial = true)
    (h : TrM E B lps Γ Δ (mkAppN (.const c us) bs.toArray) t) :
    ∃ bs' : List (Metalean.Expr ζ lps.length n), bs.length = bs'.length ∧
      (∀ (i : Nat) a a', bs[i]? = some a → bs'[i]? = some a' → TrM E B lps Γ Δ a a') ∧
      SatTr E lps b us bs' t := by
  generalize hm : mkAppN (Expr.const c us) bs.toArray = m at h
  cases h with
  | const hc =>
    rw [mkAppN_eq_foldl] at hm
    obtain ⟨rfl, rfl, -⟩ := foldl_app_const_inj (as' := []) hm
    rw [hb] at hc; cases hc; cases hs
  | special hb₂ _ hlen hargs hsat =>
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hm
    obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj hm
    rw [hb] at hb₂; cases hb₂
    exact ⟨_, hlen, hargs, hsat⟩
  | app hns => exact absurd (specialHead_of_app hm.symm hb hs) hns
  | _ => exact absurd hm (ne_mkAppN_const fun _ _ h => by cases h).symm

/-- Applying a translation to translated arguments: the translation of the Lean application is
reached by weak-head reduction (β through an η-term whose spine reaches its arity). -/
theorem TrM.apps {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {f : Expr} {as : List Expr} {f' : Metalean.Expr ζ lps.length n}
    {as' : List (Metalean.Expr ζ lps.length n)} (hf : TrM E B lps Γ Δ f f')
    (has : List.Forall₂ (TrM E B lps Γ Δ) as as') :
    ∃ t, TrM E B lps Γ Δ (mkAppN f as.toArray) t ∧ WHRedS E (f'.appList as') t := by
  by_cases hsp : SpecialHead B f
  · obtain ⟨c, us, b, hfn, hb, hs⟩ := hsp
    obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
    obtain ⟨bs', hlen, hargs, hsat⟩ := TrM.special_inv hb hs hf
    obtain ⟨t, hsat', hred⟩ := hsat.append as'
    refine ⟨t, ?_, hred⟩
    have happ : mkAppN (mkAppN (Expr.const c us) bs.toArray) as.toArray =
        mkAppN (.const c us) (bs ++ as).toArray := by
      simp only [mkAppN_eq_foldl, List.foldl_append]
    rw [happ]
    refine .special hb hs (by simp [hlen, has.length_eq]) (fun i a a' ha ha' => ?_) hsat'
    by_cases hi : i < bs.length
    · rw [List.getElem?_append_left hi] at ha
      rw [List.getElem?_append_left (by omega)] at ha'
      exact hargs i a a' ha ha'
    · rw [List.getElem?_append_right (by omega)] at ha
      rw [List.getElem?_append_right (by omega), ← hlen] at ha'
      exact forall₂_getElem? has _ a a' ha ha'
  · induction has generalizing f f' with
    | nil => exact ⟨f', hf, .refl⟩
    | @cons a a' as as' ha _ ih =>
      have hns : ¬ SpecialHead B (.app f a) := fun ⟨c, us, b, h, hb, hs⟩ =>
        hsp ⟨c, us, b, h, hb, hs⟩
      have e₁ : mkAppN f (a :: as).toArray = mkAppN (.app f a) as.toArray := by
        rw [mkAppN_eq_foldl, mkAppN_eq_foldl]; rfl
      rw [e₁]
      exact ih (.app hsp hf ha) hns

end

end

end EraseProof
