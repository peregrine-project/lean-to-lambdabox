import EraseProof.Oracle.Rename
import EraseProof.Statements

/-!
# The marking is a function of its input

`markOf_det`: over a closed closure, a closed input has at most one marking at no locals. The two
markings may open their binders with different fresh variables, so the proof shows more: a marking
of a term renamed by `ρ`, under locals that are the renamed locals on the term's scope
(`RenScope`), is the renamed marking (`MarkOf.det_ren`). Under a binder the renaming is extended by
the two fresh variables (`RenScope.cons`); the oracle's answers, types and sort levels commute with
the renaming (`Oracle/Rename.lean`), so the two derivations apply the same rules.
-/

open Lean Erasure

namespace EraseProof

/-- The scope of a renaming: `S` is closed under the locals `ls₁` and holds only their variables,
and on `S` the locals `ls₂` are `ls₁` renamed by `ρ`. Reference: none. -/
def RenScope (S : FVarId → Prop) (ρ : FVarId → FVarId) (ls₁ ls₂ : List Local) : Prop :=
  LocalsSupport S ls₁ ∧ (∀ y, S y → ∃ l, Pure.findLocal ls₁ y = some l) ∧ LocalsRen ρ S ls₁ ls₂

namespace OracleRen

theorem foldr_app_inj {f f' : Expr} (hf : f.isApp = false) (hf' : f'.isApp = false) :
    ∀ {r r' : List Expr}, r.foldr (fun a g => Expr.app g a) f = r'.foldr (fun a g => Expr.app g a) f' →
      f = f' ∧ r = r'
  | [], [], h => ⟨h, rfl⟩
  | [], _ :: _, h => by rw [List.foldr_nil] at h; rw [h] at hf; simp [Expr.isApp] at hf
  | _ :: _, [], h => by rw [List.foldr_nil] at h; rw [← h] at hf'; simp [Expr.isApp] at hf'
  | _ :: _, _ :: _, h => by
    simp only [List.foldr_cons, Expr.app.injEq] at h
    obtain ⟨h1, h2⟩ := foldr_app_inj hf hf' h.1
    exact ⟨h1, by rw [h.2, h2]⟩

theorem foldl_app_inj {f f' : Expr} {as as' : List Expr} (hf : f.isApp = false)
    (hf' : f'.isApp = false) (h : as.foldl .app f = as'.foldl .app f') : f = f' ∧ as = as' := by
  rw [List.foldl_eq_foldr_reverse, List.foldl_eq_foldr_reverse] at h
  obtain ⟨h1, h2⟩ := foldr_app_inj hf hf' h
  exact ⟨h1, List.reverse_inj.1 h2⟩

/-- Spines with heads that are not applications are equal only with equal heads and arguments. -/
theorem mkAppN_inj {f f' : Expr} {as as' : List Expr} (h : mkAppN f as.toArray = mkAppN f' as'.toArray)
    (hf : f.isApp = false) (hf' : f'.isApp = false) : f = f' ∧ as = as' :=
  foldl_app_inj hf hf' (by rwa [mkAppN_toArray, mkAppN_toArray] at h)

/-- A spine that is not an application has no argument. -/
theorem mkAppN_notApp {f E : Expr} {as : List Expr} (h : mkAppN f as.toArray = E)
    (hf : f.isApp = false) (hE : E.isApp = false) : f = E ∧ as = [] :=
  foldl_app_inj (as' := []) hf hE (by rw [← mkAppN_toArray]; exact h)

theorem renFV_isApp (ρ : FVarId → FVarId) : ∀ e : Expr, (renFV ρ e).isApp = e.isApp := by
  intro e; cases e <;> rfl

theorem renFV_ne_const {ρ : FVarId → FVarId} {f : Expr} (h : ∀ c us, f ≠ .const c us) :
    ∀ c us, renFV ρ f ≠ .const c us := by
  intro c us hf; cases f <;> simp [renFV] at hf; exact h _ _ (by rw [hf.1, hf.2])

theorem renFV_congr {ρ ρ' : FVarId → FVarId} : ∀ {e : Expr}, FVarsIn (fun y => ρ y = ρ' y) e →
    renFV ρ e = renFV ρ' e := by
  intro e; induction e <;> intro h <;> simp_all [renFV, FVarsIn]

theorem beq_false_of_ne {x y : FVarId} (h : x ≠ y) : (x == y) = false :=
  Bool.eq_false_iff.2 fun h' => h ((fvarId_beq_iff _ _).1 h')

theorem findLocal_spec {ls : List Local} {x : FVarId} {l : Local}
    (h : Pure.findLocal ls x = some l) : l ∈ ls ∧ l.fvarId = x := by
  unfold Pure.findLocal at h
  have h' := List.find?_some (p := fun l : Local => l.fvarId == x) h
  exact ⟨List.mem_of_find?_eq_some h, (fvarId_beq_iff _ _).1 h'⟩

/-- `ρ` extended by `x ↦ x'` renames a term without `x` as `ρ` does. -/
theorem renFV_upd {S : FVarId → Prop} {ρ : FVarId → FVarId} {x x' : FVarId} (hx : ¬ S x)
    {e : Expr} (he : FVarsIn S e) : renFV (fun y => if y == x then x' else ρ y) e = renFV ρ e :=
  renFV_congr (fvarsIn_mono (fun y hy => by
    rw [beq_false_of_ne fun h : y = x => hx (h ▸ hy)]; rfl) he)

/-- Abstracting the fresh variable after the extended renaming is renaming after abstracting. -/
theorem absFV_ren {S : FVarId → Prop} {ρ : FVarId → FVarId} {x x' : FVarId}
    (hρ : ∀ y, S y → ρ y ≠ x') : ∀ {e : Expr} {d : Nat}, FVarsIn (fun y => S y ∨ y = x) e →
    absFV x' d (renFV (fun y => if y == x then x' else ρ y) e) = renFV ρ (absFV x d e) := by
  intro e
  induction e with
  | fvar y =>
    intro d h
    by_cases hy : y = x
    · subst hy
      have h1 : (y == y) = true := (fvarId_beq_iff _ _).2 rfl
      have h2 : (x' == x') = true := (fvarId_beq_iff _ _).2 rfl
      simp only [renFV, absFV, h1, h2, ↓reduceIte]
    · have h1 := beq_false_of_ne (hρ y (h.resolve_right hy))
      have h2 := beq_false_of_ne hy
      simp only [renFV, absFV, h1, h2, Bool.false_eq_true, ↓reduceIte]
  | _ => intro d h; simp_all [renFV, absFV, FVarsIn]

end OracleRen

open OracleRen

/-! ## The scope of a renaming -/

theorem RenScope.not_mem {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₁ ls₂ : List Local}
    {x : FVarId} (h : RenScope S ρ ls₁ ls₂) (hx : ∀ l ∈ ls₁, l.fvarId ≠ x) : ¬ S x := by
  intro hs
  obtain ⟨l, hl⟩ := h.2.1 x hs
  exact hx l (findLocal_spec hl).1 (findLocal_spec hl).2

theorem RenScope.ne {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₁ ls₂ : List Local}
    {x' : FVarId} (h : RenScope S ρ ls₁ ls₂) (hx' : ∀ l ∈ ls₂, l.fvarId ≠ x') :
    ∀ y, S y → ρ y ≠ x' := by
  intro y hs hy
  obtain ⟨l, hl⟩ := h.2.1 y hs
  have h2 := h.2.2 y hs
  rw [hl, Option.map_some] at h2
  exact hx' _ (findLocal_spec h2).1 ((findLocal_spec h2).2.trans hy)

/-- Opening a binder in both runs, with `x` resp. `x'` fresh: the renaming extended by `x ↦ x'`
renames the extended locals on the extended scope. -/
theorem RenScope.cons {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₁ ls₂ : List Local}
    {x x' : FVarId} {n : Name} {D : Expr} {val : Option Expr} (h : RenScope S ρ ls₁ ls₂)
    (hx : ∀ l ∈ ls₁, l.fvarId ≠ x) (hx' : ∀ l ∈ ls₂, l.fvarId ≠ x') (hD : FVarsIn S D)
    (hv : ∀ v, val = some v → FVarsIn S v) :
    RenScope (fun y => S y ∨ y = x) (fun y => if y == x then x' else ρ y)
      (⟨x, n, D, val⟩ :: ls₁) (⟨x', n, renFV ρ D, val.map (renFV ρ)⟩ :: ls₂) := by
  have hnx := h.not_mem hx
  have hval : val.map (renFV (fun y => if y == x then x' else ρ y)) = val.map (renFV ρ) := by
    cases hvl : val with
    | none => rfl
    | some v => simp only [Option.map_some, renFV_upd hnx (hv v hvl)]
  refine ⟨localsSupport_open h.1 hD hv, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [Pure.findLocal, List.find?_cons]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      rcases hy with hy | rfl
      · exact h.2.1 y hy
      · rw [(fvarId_beq_iff _ _).2 rfl] at hne; cases hne
  · by_cases hyx : y = x
    · subst hyx
      have h1 : (y == y) = true := (fvarId_beq_iff _ _).2 rfl
      have h2 : (x' == x') = true := (fvarId_beq_iff _ _).2 rfl
      simp only [Pure.findLocal, List.find?_cons, h1, h2, ↓reduceIte, Option.map_some, renLocal,
        renFV_upd hnx hD, hval]
    · have hS := hy.resolve_right hyx
      have hne := h.ne hx' y hS
      have h1 := beq_false_of_ne (Ne.symm hne)
      have h2 := beq_false_of_ne (Ne.symm hyx)
      have h3 := beq_false_of_ne hyx
      have e2 := h.2.2 y hS
      simp only [Pure.findLocal] at e2 ⊢
      simp only [List.find?_cons, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, e2]
      cases hl : List.find? (fun l => l.fvarId == y) ls₁ with
      | none => rfl
      | some l =>
        have ⟨hT, hV⟩ := h.1 y hS l hl
        have hly : l.fvarId = y := (findLocal_spec hl).2
        have hlv : l.value?.map (renFV (fun y => if y == x then x' else ρ y)) =
            l.value?.map (renFV ρ) := by
          cases hv' : l.value? with
          | none => rfl
          | some v => simp only [Option.map_some, renFV_upd hnx (hV v hv')]
        simp only [Option.map_some, renLocal, hly, h3, Bool.false_eq_true, ↓reduceIte,
          renFV_upd hnx hT, hlv]

/-! ## The marking up to a renaming -/

section
variable {decls : List ConstantInfo} {cfg : ErasureConfig}

theorem OracleRen.oracle_tf {ls : List Local} {e : Expr} (h : oracle decls ls e = .ok true)
    (h' : oracle decls ls e = .ok false) : False := by
  rw [h] at h'; cases h'

/-- A marking is the `erase` mark, or the oracle answers `false`. -/
theorem MarkOf.erase_or {ls : List Local} {e ê : Expr} (h : MarkOf decls cfg ls e ê) :
    ê = markErase e ∨ oracle decls ls e = .ok false := by
  cases h
  · exact .inl rfl
  all_goals exact .inr ‹_›

/-- A recognized `casesOn` has a `casesInfo?`. -/
theorem OracleRen.casesOnOf_casesInfo {c : Name} {iv : InductiveVal} (h : casesOnOf? decls c = some iv)
    (h' : casesInfo? decls c = none) : False := by
  simp [casesOnOf?, h'] at h

/-- Two lists of markings of the same arguments, the second of the renamed arguments, related at
every index by the renaming, are related by it. -/
theorem OracleRen.list_det {ρ : FVarId → FVarId} {as âs âs' : List Expr} (hlen : as.length = âs.length)
    (hlen' : as.length = âs'.length)
    (h : ∀ (i : Nat) a â â', as[i]? = some a → âs[i]? = some â → âs'[i]? = some â' → â' = renFV ρ â) :
    âs' = âs.map (renFV ρ) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < as.length
  · rw [List.getElem?_eq_getElem (hlen' ▸ hi), List.getElem?_eq_getElem (hlen ▸ hi)]
    exact congrArg some (h i _ _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem _))
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl

/-- Opening a binder with `x`, then renaming with `x ↦ x'`, is opening the renamed body with `x'`. -/
theorem OracleRen.open_ren {S : FVarId → Prop} {ρ : FVarId → FVarId} {x x' : FVarId} (hx : ¬ S x) {b : Expr}
    (hb : FVarsIn S b) : renFV (fun y => if y == x then x' else ρ y) (b.instantiate1' (.fvar x)) =
      (renFV ρ b).instantiate1' (.fvar x') := by
  rw [renFV_inst, renFV_upd hx hb]
  simp only [renFV, (fvarId_beq_iff x x).2 rfl, ↓reduceIte]

/-- Closes a case of the inversion of a marking whose rule does not apply to the term: `he` equates
the renamed term with the rule's term, `ho` is the oracle's answer `false` on the renamed term. -/
local macro "mismatch " he:ident ho:ident : tactic => `(tactic| first
  | (cases $he:ident; done)
  | (subst $he:ident; exact (oracle_tf ‹_› $ho).elim)
  | exact nomatch (mkAppN_notApp (Eq.symm $he) rfl rfl).1
  | exact absurd (mkAppN_notApp (Eq.symm $he) ‹_› rfl).2 ‹_›
  | exact nomatch (mkAppN_notApp $he rfl rfl).1
  | exact (‹∀ c us, _ ≠ Expr.const c us› _ _ (mkAppN_inj $he rfl ‹_›).1.symm).elim
  | (obtain ⟨h1, -, -⟩ := mkAppN_const_inj $he
     subst h1
     exact nomatch ‹markArity? _ _ _ = none›.symm.trans ‹markArity? _ _ _ = some _›))

/-- Closes a case of the inversion of a saturated spine whose rule does not apply to the head. -/
local macro "sat_mismatch" : tactic => `(tactic| first
  | exact (casesOnOf_casesInfo ‹_› ‹_›).elim
  | exact nomatch ‹ctorArity? _ _ = some _›.symm.trans ‹ctorArity? _ _ = none›
  | exact nomatch ‹findDecl _ _ = some (.quotInfo _)›.symm.trans ‹findDecl _ _ = some (.recInfo _)›
  | exact nomatch ‹findDecl _ _ = some (.recInfo _)›.symm.trans ‹findDecl _ _ = some (.quotInfo _)›)

variable (hcl : ClosedDecls decls = true)
include hcl

/-- The oracle's answer `false` survives the renaming. -/
theorem OracleRen.oracle_ren {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₁ ls₂ : List Local}
    (h : RenScope S ρ ls₁ ls₂) {e : Expr} (he : FVarsIn S e) (ho : oracle decls ls₁ e = .ok false) :
    oracle decls ls₂ (renFV ρ e) = .ok false :=
  (Pure.isErasable_ren (cx := ⟨decls⟩) hcl h.1 h.2.2 oracleFuel e he).trans ho

/-- `inferType_ren` at no binder types, on a run that returns. -/
theorem OracleRen.inferType_ren' {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₁ ls₂ : List Local}
    (h : RenScope S ρ ls₁ ls₂) {e T : Expr} (he : FVarsIn S e)
    (hT : Pure.inferType ⟨decls⟩ oracleFuel ls₁ [] e = .ok T) :
    Pure.inferType ⟨decls⟩ oracleFuel ls₂ [] (renFV ρ e) = .ok (renFV ρ T) := by
  have := (inferType_ren (cx := ⟨decls⟩) hcl h.1 h.2.2 oracleFuel [] e he (by simp)).1
  rw [hT] at this; exact this

mutual
/-- The marking of a renamed term under the renamed locals is the renamed marking. -/
theorem MarkOf.det_ren {ls₁ : List Local} {e ê : Expr} :
    MarkOf decls cfg ls₁ e ê → ∀ {S : FVarId → Prop} {ρ : FVarId → FVarId} {ls₂ : List Local}
      {e₂ ê' : Expr}, RenScope S ρ ls₁ ls₂ → FVarsIn S e → renFV ρ e = e₂ →
      MarkOf decls cfg ls₂ e₂ ê' → ê' = renFV ρ ê
  | .erase ho, _, _, _, _, _, hsc, he, he₂, D2 => by
    subst he₂
    rcases D2.erase_or with rfl | ho₂
    · rfl
    · exact (oracle_tf ho
        ((Pure.isErasable_ren (cx := ⟨decls⟩) hcl hsc.1 hsc.2.2 oracleFuel _ he).symm.trans ho₂)).elim
  | .fvar ho, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | fvar _ => cases he₂; rfl
    | _ => mismatch he₂ ho₂
  | .mdata ho h, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂
    cases D2 with
    | mdata _ h' => cases he₂; exact MarkOf.det_ren h hsc he rfl h'
    | _ => mismatch he₂ ho₂
  | .lam (n := n) ho hfr h, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | lam _ hfr' h' =>
      have hx := fun l (hl : l ∈ _) => (hfr.1 l hl).1
      have hx' := fun l (hl : l ∈ _) => (hfr'.1 l hl).1
      have hnx := hsc.not_mem hx
      have hsc' := hsc.cons (n := n) (val := none) hx hx' he.1 (fun _ h => nomatch h)
      have hbM := MarkOf.fvarsIn hcl h hsc'.1 (fvarsIn_open he.2)
      have hne := hsc.ne hx'
      cases he₂
      rw [MarkOf.det_ren h hsc' (fvarsIn_open he.2) (open_ren hnx he.2) h', absFV_ren hne hbM]
    | _ => mismatch he₂ ho₂
  | .letE (n := n) (T := T) (v := v) (x := x) ho hfr hv hb, S, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | letE _ hfr' hv' hb' =>
      have hx := fun l (hl : l ∈ _) => (hfr.1 l hl).1
      have hx' := fun l (hl : l ∈ _) => (hfr'.1 l hl).1
      have hnx := hsc.not_mem hx
      have hvv : ∀ w, some v = some w → FVarsIn S w := fun _ h => by cases h; exact he.2.1
      have hsc' := hsc.cons (n := n) (val := some v) hx hx' he.1 hvv
      have hvS : LocalsSupport S (⟨x, n, T, some v⟩ :: ls₁) :=
        localsSupport_cons hsc.1 he.1 hvv (fun _ h => h) (fun _ h => .inr h)
      have hvM := MarkOf.fvarsIn hcl hv hvS he.2.1
      have hbM := MarkOf.fvarsIn hcl hb hsc'.1 (fvarsIn_open he.2.2)
      have hne := hsc.ne hx'
      cases he₂
      rw [MarkOf.det_ren hv hsc' (fvarsIn_mono (fun _ => .inl) he.2.1) (renFV_upd hnx he.2.1) hv',
        MarkOf.det_ren hb hsc' (fvarsIn_open he.2.2) (open_ren hnx he.2.2) hb',
        renFV_upd hnx hvM, absFV_ren hne hbM]
    | _ => mismatch he₂ ho₂
  | .proj ho _ h, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | proj _ _ h' => cases he₂; rw [MarkOf.det_ren h hsc he rfl h']
    | _ => mismatch he₂ ho₂
  | .litZero ho _, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | litZero _ _ => rfl
    | _ => mismatch he₂ ho₂
  | .litSucc ho _ _ _, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV] at he₂ ho₂ ⊢
    cases D2 with
    | litSucc _ _ _ _ => cases he₂; rfl
    | _ => mismatch he₂ ho₂
  | .app ho hne hfa hfc hf hlen hargs, _, ρ, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    rw [renFV_mkAppN] at he₂ ho₂ ⊢
    rw [fvarsIn_mkAppN] at he
    have hfa₂ := (renFV_isApp ρ _).trans hfa
    have hfc₂ := renFV_ne_const (ρ := ρ) hfc
    cases D2 with
    | app _ _ hfa' _ hf' hlen' hargs' =>
      obtain ⟨rfl, rfl⟩ := mkAppN_inj he₂ hfa₂ hfa'
      rw [MarkOf.det_ren hf hsc he.1 rfl hf', list_det hlen (by simpa using hlen')
        fun i a â â' ha hâ hâ' => MarkOf.det_ren (hargs i a â ha hâ) hsc
          (he.2 a (List.mem_of_getElem? ha)) rfl (hargs' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
    | _ => first
      | mismatch he₂ ho₂
      | exact (hne (List.map_eq_nil_iff.1 (mkAppN_notApp he₂ hfa₂ rfl).2)).elim
      | exact (hfc₂ _ _ (mkAppN_inj he₂ hfa₂ rfl).1).elim
  | .constApp ho _ hlen hargs, _, ρ, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    simp only [renFV_mkAppN, renFV] at he₂ ho₂ ⊢
    rw [fvarsIn_mkAppN] at he
    cases D2 with
    | constApp _ _ hlen' hargs' =>
      obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj he₂
      rw [list_det hlen (by simpa using hlen') fun i a â â' ha hâ hâ' => MarkOf.det_ren
        (hargs i a â ha hâ) hsc (he.2 a (List.mem_of_getElem? ha)) rfl
        (hargs' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
    | _ => mismatch he₂ ho₂
  | .special ho har hT hη, _, _, _, _, _, hsc, he, he₂, D2 => by
    have ho₂ := oracle_ren hcl hsc he ho
    have hT₂ := inferType_ren' hcl hsc he hT
    have hTS := fvarsIn_oracle_ty hcl hsc.1 he hT
    simp only [renFV_mkAppN, renFV] at he₂ ho₂ hT₂
    rw [fvarsIn_mkAppN] at he
    cases D2 with
    | special _ har' hT' hη' =>
      obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj he₂
      rw [har] at har'; cases har'
      rw [hT₂] at hT'; cases hT'
      exact MarkEta.det_ren hη hsc hTS he.2 hη'
    | _ => mismatch he₂ ho₂

/-- `MarkOf.det_ren` for the η-expansion of a spine. -/
theorem MarkEta.det_ren {ls₁ : List Local} {ar : Nat} {T : Expr} {c : Name} {us : List Level}
    {as : List Expr} {ê : Expr} :
    MarkEta decls cfg ls₁ ar T c us as ê → ∀ {S : FVarId → Prop} {ρ : FVarId → FVarId}
      {ls₂ : List Local} {ê' : Expr}, RenScope S ρ ls₁ ls₂ → FVarsIn S T → (∀ a ∈ as, FVarsIn S a) →
      MarkEta decls cfg ls₂ ar (renFV ρ T) c us (as.map (renFV ρ)) ê' → ê' = renFV ρ ê
  | .sat hle hs, _, _, _, _, hsc, _, has, D2 => by
    cases D2 with
    | sat _ hs' => exact MarkSat.det_ren hs hsc has rfl hs'
    | intro hlt _ _ _ => rw [List.length_map] at hlt; omega
  | .intro (y := y) (x := x) hlt hv hfr hη, S, ρ, _, _, hsc, hT, has, D2 => by
    cases D2 with
    | sat hle _ => rw [List.length_map] at hle; omega
    | @intro _ _ _ _ _ _ _ x' _ _ _ _ _ hv' hfr' hη' =>
      have ⟨hD, hC⟩ := fvarsIn_view hcl hsc.1 hT hv
      have hx := fun l (hl : l ∈ _) => (hfr.1 l hl).1
      have hx' := fun l (hl : l ∈ _) => (hfr'.1 l hl).1
      have hnx := hsc.not_mem hx
      have hsc' := hsc.cons (n := y) (val := none) hx hx' hD (fun _ h => nomatch h)
      have hasS : ∀ a ∈ as ++ [Expr.fvar x], FVarsIn (fun y => S y ∨ y = x) a := by
        simp only [List.forall_mem_append, List.forall_mem_singleton]
        exact ⟨fun a ha => fvarsIn_mono (fun _ => .inl) (has a ha), Or.inr rfl⟩
      have hmap : (as ++ [Expr.fvar x]).map (renFV (fun y => if y == x then x' else ρ y)) =
          as.map (renFV ρ) ++ [.fvar x'] := by
        simp only [List.map_append, List.map_cons, List.map_nil, renFV, (fvarId_beq_iff x x).2 rfl,
          ↓reduceIte]
        exact congrArg (· ++ _) (List.map_congr_left fun a ha => renFV_upd hnx (has a ha))
      have hêS := MarkEta.fvarsIn hcl hη hsc'.1 (fvarsIn_open hC) hasS
      have hne := hsc.ne hx'
      have hCo := open_ren (x' := x') (ρ := ρ) hnx hC
      rw [(forallView?_ren hcl hsc.1 hsc.2.2 _ hT).1, hv] at hv'
      cases hv'
      rw [← hCo, ← hmap] at hη'
      rw [MarkEta.det_ren hη hsc' (fvarsIn_open hC) hasS hη']
      simp only [renFV]
      rw [absFV_ren hne hêS]

/-- `MarkOf.det_ren` for the saturated spines. -/
theorem MarkSat.det_ren {ls₁ : List Local} {c : Name} {us : List Level} {as : List Expr} {ê : Expr} :
    MarkSat decls cfg ls₁ c us as ê → ∀ {S : FVarId → Prop} {ρ : FVarId → FVarId}
      {ls₂ : List Local} {as₂ : List Expr} {ê' : Expr}, RenScope S ρ ls₁ ls₂ →
      (∀ a ∈ as, FVarsIn S a) → as.map (renFV ρ) = as₂ → MarkSat decls cfg ls₂ c us as₂ ê' →
      ê' = renFV ρ ê
  | .casesProp hcs hfd hlp, _, _, _, _, _, _, _, he₂, D2 => by
    cases D2 with
    | casesProp _ _ _ => subst he₂; simp only [renFV, renFV_mkAppN]
    | casesReduced hcs' hfd' hlp' _ _ _ _ _ _ _ _ _ =>
      rw [hcs] at hcs'; cases hcs'; rw [hfd] at hfd'; cases hfd'; exact (hlp' hlp).elim
    | cases hcs' hfd' hlp' _ _ _ _ _ _ _ _ _ _ _ =>
      rw [hcs] at hcs'; cases hcs'; rw [hfd] at hfd'; cases hfd'; exact (hlp' hlp).elim
    | _ => sat_mismatch
  | .casesReduced hcs hfd hlp hpre htl hnz hctors _ _ halt hlen hextra, _, ρ, _, _, _, hsc, has,
      he₂, D2 => by
    cases D2 with
    | casesProp hcs' hfd' hlp' =>
      rw [hcs] at hcs'; cases hcs'; rw [hfd] at hfd'; cases hfd'; exact (hlp hlp').elim
    | casesReduced hcs' _ _ hpre' _ _ _ _ _ halt' hlen' hextra' =>
      rw [hcs] at hcs'; cases hcs'
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] at he₂
      obtain ⟨rfl, h⟩ := List.append_inj he₂ (by simp [hpre, hpre'])
      cases h
      rw [MarkOf.det_ren halt hsc (has _ (by simp)) rfl halt', list_det hlen (by simpa using hlen')
        fun i a â â' ha hâ hâ' => MarkOf.det_ren (hextra i a â ha hâ) hsc
          (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hextra' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV, List.map_append, List.map_cons, List.map_nil]
    | cases hcs' _ _ hpre' _ htl' hnz' _ _ _ _ _ _ _ =>
      rw [hcs] at hcs'; cases hcs'
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] at he₂
      obtain ⟨-, h⟩ := List.append_inj he₂ (by simp [hpre, hpre'])
      rw [← (List.cons.inj h).1, Pure.typeLevel_ren (cx := ⟨decls⟩) hcl hsc.1 hsc.2.2 _ _
        (has _ (by simp)), htl] at htl'
      cases htl'
      exact ((hnz' hnz).1 (by rw [hctors]; rfl)).elim
    | _ => sat_mismatch
  | .cases hcs hfd hlp hpre halen htl hnz hd hlen hctors htys halts hlen' hextra, _, ρ, _, _, _,
      hsc, has, he₂, D2 => by
    cases D2 with
    | casesProp hcs' hfd' hlp' =>
      rw [hcs] at hcs'; cases hcs'; rw [hfd] at hfd'; cases hfd'; exact (hlp hlp').elim
    | casesReduced hcs' _ _ hpre' htl' hnz' hctors' _ _ _ _ _ =>
      rw [hcs] at hcs'; cases hcs'
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] at he₂
      obtain ⟨-, h⟩ := List.append_inj he₂ (by simp [hpre, hpre'])
      rw [← (List.cons.inj h).1, Pure.typeLevel_ren (cx := ⟨decls⟩) hcl hsc.1 hsc.2.2 _ _
        (has _ (by simp)), htl] at htl'
      cases htl'
      exact ((hnz hnz').1 (by rw [hctors']; rfl)).elim
    | cases hcs' _ _ hpre' halen' _ _ hd' hlen₂ _ _ halts' hlen₂' hextra' =>
      rw [hcs] at hcs'; cases hcs'
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] at he₂
      obtain ⟨rfl, h1⟩ := List.append_inj he₂ (by simp [hpre, hpre'])
      obtain ⟨rfl, h2⟩ := List.cons.inj h1
      obtain ⟨rfl, rfl⟩ := List.append_inj h2 (by simp [halen, halen'])
      rw [MarkOf.det_ren hd hsc (has _ (by simp)) rfl hd',
        list_det hlen ((List.length_map _).symm.trans hlen₂) fun i a â â' ha hâ hâ' => by
          have haS := has a (by simp [List.mem_of_getElem? ha])
          obtain ⟨T, hT⟩ := htys i a ha
          have hi := halen ▸ (List.getElem?_eq_some_iff.1 ha).1
          obtain ⟨cv, hcv⟩ := hctors i _ (List.getElem?_eq_getElem hi)
          exact MarkAlt.det_ren (halts i _ cv a â T (List.getElem?_eq_getElem hi) hcv ha hâ hT) hsc
            haS (fvarsIn_oracle_ty hcl hsc.1 haS hT) rfl
            (halts' i _ cv _ â' _ (List.getElem?_eq_getElem hi) hcv
              (by rw [List.getElem?_map, ha]; rfl) hâ' (inferType_ren' hcl hsc haS hT)),
        list_det hlen' (by simpa using hlen₂') fun i a â â' ha hâ hâ' => MarkOf.det_ren
          (hextra i a â ha hâ) hsc (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hextra' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV, List.map_append, List.map_cons, List.map_nil]
    | _ => sat_mismatch
  | .ctor _ _ hlen hargs, _, ρ, _, _, _, hsc, has, he₂, D2 => by
    cases D2 with
    | ctor _ _ hlen' hargs' =>
      subst he₂
      rw [list_det hlen (by simpa using hlen') fun i a â â' ha hâ hâ' => MarkOf.det_ren
        (hargs i a â ha hâ) hsc (has a (List.mem_of_getElem? ha)) rfl
        (hargs' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV]
    | _ => sat_mismatch
  | .quotMk _ _ hfd hk ha hlen hextra, _, ρ, _, _, _, hsc, has, he₂, D2 => by
    cases D2 with
    | quotMk _ _ _ _ ha' hlen' hextra' =>
      simp only [List.map_cons, List.cons_append, List.nil_append] at he₂
      cases he₂
      rw [MarkOf.det_ren ha hsc (has _ (by simp)) rfl ha', list_det hlen (by simpa using hlen')
        fun i a â â' ha hâ hâ' => MarkOf.det_ren (hextra i a â ha hâ) hsc
          (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hextra' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV, List.map_append, List.map_cons, List.map_nil]
    | quotLift _ _ hfd' hk' _ _ _ _ =>
      rw [hfd] at hfd'; cases hfd'; rw [hk] at hk'; cases hk'
    | _ => sat_mismatch
  | .quotLift _ _ hfd hk hf hq hlen hextra, _, ρ, _, _, _, hsc, has, he₂, D2 => by
    cases D2 with
    | quotMk _ _ hfd' hk' _ _ _ =>
      rw [hfd] at hfd'; cases hfd'; rw [hk] at hk'; cases hk'
    | quotLift _ _ _ _ hf' hq' hlen' hextra' =>
      simp only [List.map_cons, List.cons_append, List.nil_append] at he₂
      cases he₂
      rw [MarkOf.det_ren hf hsc (has _ (by simp)) rfl hf', MarkOf.det_ren hq hsc (has _ (by simp)) rfl hq',
        list_det hlen (by simpa using hlen')
        fun i a â â' ha hâ hâ' => MarkOf.det_ren (hextra i a â ha hâ) hsc
          (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hextra' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV, List.map_append, List.map_cons, List.map_nil]
    | _ => sat_mismatch
  | .recr _ _ hfd _ _ _ hps hms hmins his _ hlm hminsM hli hisM hmaj hle hextra, _, ρ, _, _, _,
      hsc, has, he₂, D2 => by
    cases D2 with
    | recr _ _ hfd' _ _ _ hps' hms' hmins' his' _ hlm' hminsM' hli' hisM' hmaj' hle' hextra' =>
      rw [hfd] at hfd'; cases hfd'
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] at he₂
      obtain ⟨rfl, h1⟩ := List.append_inj he₂ (by simp [hps, hps'])
      obtain ⟨rfl, h2⟩ := List.append_inj h1 (by simp [hms, hms'])
      obtain ⟨rfl, h3⟩ := List.append_inj h2 (by simp [hmins, hmins'])
      obtain ⟨rfl, h4⟩ := List.append_inj h3 (by simp [his, his'])
      obtain ⟨rfl, rfl⟩ := List.cons.inj h4
      rw [list_det hlm (by simpa using hlm') fun i a â â' ha hâ hâ' => MarkOf.det_ren
          (hminsM i a â ha hâ) hsc (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hminsM' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ'),
        list_det hli (by simpa using hli') fun i a â â' ha hâ hâ' => MarkOf.det_ren
          (hisM i a â ha hâ) hsc (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hisM' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ'),
        MarkOf.det_ren hmaj hsc (has _ (by simp)) rfl hmaj',
        list_det hle (by simpa using hle') fun i a â â' ha hâ hâ' => MarkOf.det_ren
          (hextra i a â ha hâ) hsc (has a (by simp [List.mem_of_getElem? ha])) rfl
          (hextra' i _ â' (by rw [List.getElem?_map, ha]; rfl) hâ')]
      simp only [renFV_mkAppN, renFV, List.map_append, List.map_cons, List.map_nil]
    | _ => sat_mismatch

/-- `MarkOf.det_ren` for the alternatives of a `casesOn`. -/
theorem MarkAlt.det_ren {ls₁ : List Local} {k : Nat} {e T ê : Expr} :
    MarkAlt decls cfg ls₁ k e T ê → ∀ {S : FVarId → Prop} {ρ : FVarId → FVarId}
      {ls₂ : List Local} {e₂ ê' : Expr}, RenScope S ρ ls₁ ls₂ → FVarsIn S e → FVarsIn S T →
      renFV ρ e = e₂ → MarkAlt decls cfg ls₂ k e₂ (renFV ρ T) ê' → ê' = renFV ρ ê
  | .done h, _, _, _, _, _, hsc, he, _, he₂, D2 => by
    cases D2 with
    | done h' => exact MarkOf.det_ren h hsc he he₂ h'
  | .lam (y := y) hv hfr h, S, ρ, _, _, _, hsc, he, hT, he₂, D2 => by
    simp only [renFV] at he₂ ⊢
    cases D2 with
    | @lam _ _ _ _ _ _ x' _ _ _ _ _ _ hv' hfr' h' =>
      have ⟨hD, hC⟩ := fvarsIn_view hcl hsc.1 hT hv
      have hx := fun l (hl : l ∈ _) => (hfr.1 l hl).1
      have hx' := fun l (hl : l ∈ _) => (hfr'.1 l hl).1
      have hnx := hsc.not_mem hx
      have hsc' := hsc.cons (n := y) (val := none) hx hx' hD (fun _ h => nomatch h)
      have hbM := MarkAlt.fvarsIn hcl h hsc'.1 (fvarsIn_open he.2) (fvarsIn_open hC)
      have hne := hsc.ne hx'
      have hCo := open_ren (x' := x') (ρ := ρ) hnx hC
      have hbo := open_ren (x' := x') (ρ := ρ) hnx he.2
      rw [(forallView?_ren hcl hsc.1 hsc.2.2 _ hT).1, hv] at hv'
      cases hv'
      cases he₂
      rw [← hCo] at h'
      rw [MarkAlt.det_ren h hsc' (fvarsIn_open he.2) (fvarsIn_open hC) hbo h',
        absFV_ren hne hbM]
    | intro hnl _ _ _ => subst he₂; exact absurd rfl (hnl _ _ _ _)
  | .intro (y := y) (x := x) hnl hv hfr h, S, ρ, _, _, _, hsc, he, hT, he₂, D2 => by
    cases D2 with
    | lam _ _ _ =>
      obtain ⟨_, _, rfl⟩ := renFV_eq_lam he₂
      exact absurd rfl (hnl _ _ _ _)
    | @intro _ _ _ _ _ _ _ x' _ _ _ hv' hfr' h' =>
      subst he₂
      have ⟨hD, hC⟩ := fvarsIn_view hcl hsc.1 hT hv
      have hx := fun l (hl : l ∈ _) => (hfr.1 l hl).1
      have hx' := fun l (hl : l ∈ _) => (hfr'.1 l hl).1
      have hnx := hsc.not_mem hx
      have hsc' := hsc.cons (n := y) (val := none) hx hx' hD (fun _ h => nomatch h)
      have heS : FVarsIn (fun y => S y ∨ y = x) (.app e (.fvar x)) :=
        ⟨fvarsIn_mono (fun _ => .inl) he, Or.inr rfl⟩
      have happ : renFV (fun y => if y == x then x' else ρ y) (.app e (.fvar x)) =
          .app (renFV ρ e) (.fvar x') := by
        simp only [renFV, renFV_upd hnx he, (fvarId_beq_iff x x).2 rfl, ↓reduceIte]
      have hbM := MarkAlt.fvarsIn hcl h hsc'.1 heS (fvarsIn_open hC)
      have hne := hsc.ne hx'
      have hCo := open_ren (x' := x') (ρ := ρ) hnx hC
      rw [(forallView?_ren hcl hsc.1 hsc.2.2 _ hT).1, hv] at hv'
      cases hv'
      rw [← hCo] at h'
      rw [MarkAlt.det_ren h hsc' heS (fvarsIn_open hC) happ h']
      simp only [renFV]
      rw [absFV_ren hne hbM]
end

end

/-- Over a closed closure, a closed term has at most one marking at no locals. Reference: none
(DV-32). -/
theorem markOf_det : markOf_det_statement := by
  intro decls cfg e ê ê' hcl he h₁ h₂
  have := MarkOf.det_ren hcl h₁ (S := fun _ => False) (ρ := id)
    ⟨fun _ h => h.elim, fun _ h => h.elim, localsRen_id⟩ he (renFV_id e) h₂
  rw [this, renFV_id]

end EraseProof
