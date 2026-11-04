import EraseProof.Bridge.ProgEnv
import EraseProof.Relation.Extend

/-!
# No declaration of a program is recursive for the traversal

`visitMutual` takes its fix branch on a declaration whose block has more than one member or whose
value mentions its own name (`Erasure.isRecursiveDecl`). In a program related to a Metalean
environment (`ProgEnv`), every declaration with a value is alone in its block, and its value does
not mention it: a definition's value is translated in the table of the earlier declarations, whose
names are fresh, and a theorem's or an opaque's value does not mention the declaration by
`ProgEnv`'s premise (`isRecursiveDecl_false`).
-/

open Lean Erasure

namespace EraseProof

namespace NonRec

open Extend

/-- `ConstsIn` is monotone in the predicate. -/
theorem ConstsIn_mono {p q : Name → Prop} (hpq : ∀ c, p c → q c) :
    ∀ {e : Expr}, ConstsIn p e → ConstsIn q e
  | .const c _, h => hpq c h
  | .app f a, h => ⟨ConstsIn_mono hpq (e := f) h.1, ConstsIn_mono hpq (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨ConstsIn_mono hpq (e := t) h.1, ConstsIn_mono hpq (e := b) h.2⟩
  | .letE _ t v b _, h =>
    ⟨ConstsIn_mono hpq (e := t) h.1, ConstsIn_mono hpq (e := v) h.2.1,
      ConstsIn_mono hpq (e := b) h.2.2⟩
  | .mdata _ e, h => ConstsIn_mono hpq (e := e) h
  | .proj S _ e, h => ⟨hpq S h.1, ConstsIn_mono hpq (e := e) h.2⟩
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lit _, h => h

/-- Every member of a list with a pointwise relation of the same length to another satisfies `Q`
when every related pair does. -/
theorem forall_mem_of_rel {α β : Type} {Q : α → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → Q a) : ∀ a ∈ as, Q a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact h i _ bs[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}

/-- The constants of a translated term, and the structures of its projections, are bound in the
table. -/
theorem TrM.consts {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ e t) : ConstsIn (fun c => B c ≠ none) e := by
  induction h with
  | special hc _ hlen _ _ ih =>
    exact ConstsIn_mkAppN.2 ⟨by simp [ConstsIn, hc], forall_mem_of_rel hlen ih⟩
  | bvar | fvar | sort | lit => trivial
  | const hc => simp [ConstsIn, hc]
  | app _ _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ ihA ihb | forallE _ _ ihA ihb => exact ⟨ihA, ihb⟩
  | letE _ _ _ ihT ihv ihb => exact ⟨ihT, ihv, ihb⟩
  | mdata _ ih => exact ih
  | projStruct _ _ hS _ _ ih => exact ⟨by simp [hS], ih⟩
  | projProof _ hS _ _ _ _ _ _ _ ih => exact ⟨by simp [hS], ih⟩

/-- A name that no constant of `e` is does not occur in `e` for the traversal. -/
theorem nameOccurs_false {n : Name} : ∀ {e : Expr}, ConstsIn (· ≠ n) e → nameOccurs n e = false
  | .const c _, h => by
    simp only [nameOccurs]
    exact Bool.eq_false_iff.2 fun h' => h (beq_iff_eq.1 h').symm
  | .lam _ _ b _, h => nameOccurs_false (e := b) h.2
  | .mdata _ e, h => nameOccurs_false (e := e) h
  | .proj _ _ e, h => nameOccurs_false (e := e) h.2
  | .app f a, h => by
    simp only [nameOccurs, nameOccurs_false h.1, nameOccurs_false h.2, Bool.or_self]
  | .letE _ _ v b _, h => by
    simp only [nameOccurs, nameOccurs_false h.2.1, nameOccurs_false h.2.2, Bool.or_self]
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .forallE .., _ | .lit _, _ => rfl

/-- A declaration of the program with a value is alone in its block, and its value does not
mention it. -/
theorem ProgEnv.scoped {P : List ConstantInfo} (h : ProgEnv P ζ E B) {ci : ConstantInfo}
    (hm : ci ∈ P) {v : Expr} (hv : ci.value? (allowOpaque := true) = some v) :
    ci.all = [ci.name] ∧ ConstsIn (· ≠ ci.name) v := by
  induction h with
  | nil => cases hm
  | «axiom» _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hv
    · exact ih hm
  | defn hP hfr _ _ hall _ hval ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hv
      refine ⟨hall, ConstsIn_mono (fun c hc hce => ?_) (TrM.consts hval)⟩
      subst hce
      exact not_mem_of_findDecl_none hfr (hP.bound hc)
    · exact ih hm
  | thm _ _ _ hall hsc _ _ ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hv
      exact ⟨hall, hsc⟩
    · exact ih hm
  | «opaque» _ _ _ _ hall hsc _ ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hv
      exact ⟨hall, hsc⟩
    · exact ih hm
  | induct _ _ _ _ _ _ _ ih =>
    rcases List.mem_append.1 hm with hm | hm
    · rcases IndBlock.mem_decls hm with ⟨s, rfl⟩ | ⟨s, c, rfl⟩ | ⟨s, rfl⟩ <;> cases hv
    · exact ih hm
  | quot _ _ _ _ _ _ _ ih =>
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
      cases hv
    · exact ih hm

end NonRec

open NonRec in
/-- No declaration of a Metalean program is recursive for the traversal: the fix branch of
`visitMutual` is dead on the pure path. Reference: none (DV-7 does not arise). -/
theorem isRecursiveDecl_false {P : List ConstantInfo} {ζ : Metalean.Sigs} {E : Metalean.Env ζ}
    {B : Binds ζ} {c : Name} {ci : ConstantInfo} {v : Expr} (henv : ProgEnv P ζ E B)
    (hc : findDecl P c = some ci) (hv : ci.value? (allowOpaque := true) = some v) :
    isRecursiveDecl ci = false := by
  obtain ⟨hall, hsc⟩ := ProgEnv.scoped henv (findDecl_eq_some hc).1 hv
  have hval : ci.value! (allowOpaque := true) = v := by
    cases ci <;> cases hv <;> rfl
  unfold isRecursiveDecl
  rw [hall, hval, nameOccurs_false hsc]
  rfl

end EraseProof
