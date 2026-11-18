import EraseProof.Bridge.Apps
import EraseProof.Bridge.Basic
import EraseProof.Bridge.Cases
import EraseProof.Bridge.InstL
import EraseProof.Bridge.WkEnv

/-!
# Reduction of a recognized `casesOn` on a constructor value

A saturated recognized `T.casesOn` whose major premise is a constructor value of `T` translates to
a Metalean term that reduces by δ (the `casesOn` definition), β (its λ's), ι (the recursor on the
constructor) and β (through `wrapCase` and the canonical minor) to the alternative applied to
translations of the fields (`CasesWhred.casesOn_whred_core`). The minor's β-step uses the arity
`nfields + 2 * nrecFields` that `IndBlock` fixes for the recursor's minor premises. Instances:
constructor spines (`CasesWhred.casesOn_whred_spine`) and Nat literals
(`CasesWhred.casesOnLit_whred_spine`); with the saturation of the alternative's spine
(`TrM.apps`), `casesOn_whred` and `casesOnLit_whred`. `CasesWhred.ProgEnv.block` recovers the inductive block of
a Metalean head from the program. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`);
`WHRed.delta`, `WHRed.iota` (`ML Syntax/Reduction.lean`); DV-25.
-/

open Lean Erasure
open Metalean (WHRed WHRedS Head)

namespace EraseProof

namespace CasesWhred

variable {ζ : Metalean.Sigs}

/-! ## The inductive block of a head -/

/-- A weakened binding with an inductive head is the binding with the unweakened head. -/
theorem wk_eq_ind {sig : Metalean.Sig} {ι : Metalean.IndSig} {b : MBinding ζ}
    {η : Head ζ (.inductive ι)} {t : Fin ι.nsorts}
    (h : b.wk (sig := sig) = .ind (Head.there η) t) : b = .ind η t := by
  cases b with
  | ind η' t' => simp only [MBinding.wk] at h; cases h; rfl
  | _ => cases h

/-- A weakened binding with a constructor head is the binding with the unweakened head. -/
theorem wk_eq_ctor {sig : Metalean.Sig} {ι : Metalean.IndSig} {b : MBinding ζ}
    {η : Head ζ (.inductive ι)} {t : Fin ι.nsorts} {c : Fin (ι.nctors t)} {o : List Nat}
    (h : b.wk (sig := sig) = .ctor (Head.there η) t c o) : b = .ctor η t c o := by
  cases b with
  | ctor η' t' c' o' => simp only [MBinding.wk] at h; cases h; rfl
  | _ => cases h

/-- A binding whose head is not a weakened inductive head. -/
abbrev NotThere {sig : Metalean.Sig} (b : MBinding (ζ.snoc sig)) : Prop :=
  (∀ ι (η : Head ζ (.inductive ι)) t, b ≠ .ind (Head.there η) t) ∧
    ∀ ι (η : Head ζ (.inductive ι)) t c o, b ≠ .ctor (Head.there η) t c o

/-- The name of a recursor declaration. -/
theorem name_recInfo (r : RecursorVal) : (ConstantInfo.recInfo r).name = r.name := rfl
/-- The name of a constructor declaration. -/
theorem name_ctorInfo (r : ConstructorVal) : (ConstantInfo.ctorInfo r).name = r.name := rfl
/-- The name of an inductive type declaration. -/
theorem name_inductInfo (r : InductiveVal) : (ConstantInfo.inductInfo r).name = r.name := rfl

/-- In a list with distinct names, a member is the declaration found under its name. -/
theorem findDecl_of_nodup {l : List ConstantInfo} (hnd : (l.map (·.name)).Nodup)
    {ci : ConstantInfo} (hci : ci ∈ l) : findDecl l ci.name = some ci := by
  induction l with
  | nil => cases hci
  | cons x l ih =>
    rw [findDecl_cons]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hci with rfl | hm
    · simp
    · have hne : x.name ≠ ci.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem hm)
      simp [hne, ih hnd.2 hm]

/-- What the program says about the inductive block at a head: its declarations (found in the
program, with distinct names), the block's `IndBlock` clauses, the table entries of its recursors,
and that the table binds the head's sorts and constructors only to the block's names and field
orders. -/
def BlockAt (P : List ConstantInfo) (B : Binds ζ) {ι : Metalean.IndSig}
    (η : Head ζ (.inductive ι)) (lps : List Name) (Is : Fin ι.nsorts → InductiveVal)
    (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal)
    (Rs : Fin ι.nsorts → RecursorVal)
    (orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat) : Prop :=
  (∃ (ζ₀ : Metalean.Sigs) (E₀ : Metalean.Env ζ₀) (B₀ : Binds ζ₀) (η₀ : Head ζ₀ (.inductive ι)),
      IndBlock E₀ B₀ η₀ lps Is Cs Rs orders) ∧
    ((IndBlock.decls Is Cs Rs).map (·.name)).Nodup ∧
    (∀ ci ∈ IndBlock.decls Is Cs Rs, findDecl P ci.name = some ci) ∧
    (∀ t, B (Rs t).name = some (.recr η t (List.ofFn fun t => List.ofFn fun c => orders t c))) ∧
    (∀ x t, B x = some (.ind η t) → x = (Is t).name) ∧
    (∀ x t c o, B x = some (.ctor η t c o) → o = orders t c)

/-- The block at a head survives an extension of the program by fresh names. -/
theorem BlockAt.there {sig : Metalean.Sig} {P P' : List ConstantInfo} {B : Binds ζ}
    {B' : Binds (ζ.snoc sig)} {new : List Name} {ι : Metalean.IndSig}
    {η : Head ζ (.inductive ι)} {lps : List Name} {Is : Fin ι.nsorts → InductiveVal}
    {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal}
    {Rs : Fin ι.nsorts → RecursorVal}
    {orders : (s : Fin ι.nsorts) → Fin (ι.nctors s) → List Nat}
    (hb : BlockAt P B η lps Is Cs Rs orders)
    (hfind : ∀ x ∈ P.map (·.name), findDecl P' x = findDecl P x)
    (hfresh : ∀ x ∈ new, x ∉ P.map (·.name))
    (hold : ∀ x, x ∉ new → B' x = (B x).map MBinding.wk)
    (hnew : ∀ x ∈ new, ∀ b, B' x = some b → NotThere b) :
    BlockAt P' B' (Head.there η) lps Is Cs Rs orders := by
  obtain ⟨hblk, hnd, hfd, hrec, hind, hctor⟩ := hb
  have hmem : ∀ ci ∈ IndBlock.decls Is Cs Rs, ci.name ∈ P.map (·.name) := fun ci hci =>
    List.mem_map.mpr ⟨ci, (findDecl_eq_some (hfd ci hci)).1, rfl⟩
  have hnotnew : ∀ ci ∈ IndBlock.decls Is Cs Rs, ci.name ∉ new := fun ci hci hn =>
    hfresh _ hn (hmem ci hci)
  have hR : ∀ t, .recInfo (Rs t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  refine ⟨hblk, hnd, fun ci hci => (hfind _ (hmem ci hci)).trans (hfd ci hci), fun t => ?_,
    fun x t hx => ?_, fun x t c o hx => ?_⟩
  · exact (hold (Rs t).name (hnotnew _ (hR t))).trans (by rw [hrec t]; rfl)
  · by_cases hn : x ∈ new
    · exact absurd rfl ((hnew x hn _ hx).1 _ η t)
    · rw [hold x hn] at hx
      obtain ⟨b, hb, hbw⟩ := Option.map_eq_some_iff.mp hx
      exact hind x t (hb.trans (congrArg some (wk_eq_ind hbw)))
  · by_cases hn : x ∈ new
    · exact absurd rfl ((hnew x hn _ hx).2 _ η t c o)
    · rw [hold x hn] at hx
      obtain ⟨b, hb, hbw⟩ := Option.map_eq_some_iff.mp hx
      exact hctor x t c o (hb.trans (congrArg some (wk_eq_ctor hbw)))

variable {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- The constructor fields that the block at `η` uses as index variables of a constructor's result
are index fields of the Lean constructor types `Cs` (`IndBlock.indexVars`, at the environment's own
entry of the block). -/
def IndexVarsAt (E : Metalean.Env ζ) {ι : Metalean.IndSig} (η : Head ζ (.inductive ι))
    (Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal) : Prop :=
  ∀ s c, (∃ (i : Fin (ι.nindices s)) (f : Fin (ι.ctors s c).nfields),
      (((E.get η).block.ctors s c).targetIndices i).isVar = some (ι.nparams + f.val)) →
    (indexFields ι.nparams (Cs s c).type).any Option.isSome = true

/-- `IndexVarsAt` survives an extension of the environment. -/
theorem IndexVarsAt.there {sig : Metalean.Sig} {ent : Metalean.Entry ζ sig} {ι : Metalean.IndSig}
    {η : Head ζ (.inductive ι)} {Cs : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ConstructorVal}
    (h : IndexVarsAt E η Cs) : IndexVarsAt (E.snoc ent) (Head.there η) Cs := by
  intro s c ⟨i, f, hx⟩
  refine h s c ⟨i, f, ?_⟩
  have e : (E.snoc ent).get (Head.there η) = (E.get η).map (.step .refl) := rfl
  rw [e, Metalean.Entry.block_map] at hx
  simpa [Metalean.Inductive.map, Metalean.Ctor.map] using hx

/-- Every inductive head of the environment is the head of an inductive block of the program,
whose index-variable fields are Lean index fields (`IndexVarsAt`). Reference: `declared_inductive`
(MC §3.6). -/
theorem ProgEnv.blockIdx (h : ProgEnv P ζ E B) :
    ∀ {ι : Metalean.IndSig} (η : Head ζ (.inductive ι)), ∃ lps Is Cs Rs orders,
      BlockAt P B η lps Is Cs Rs orders ∧ IndexVarsAt E η Cs := by
  induction h with
  | nil => intro ι η; cases η
  | @«axiom» _ _ _ _ v _ hP hfr _ _ _ ih | @defn _ _ _ _ v _ _ hP hfr _ _ _ _ _ ih
  | @thm _ _ _ _ v _ hP hfr _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ hP hfr _ _ _ _ _ _ ih =>
    intro ι η
    cases η with
    | there η =>
      obtain ⟨lps, Is, Cs, Rs, orders, hb, hix⟩ := ih η
      refine ⟨lps, Is, Cs, Rs, orders, hb.there (new := [v.name]) (fun x hx => ?_) ?_ ?_ ?_,
        hix.there⟩
      · have hne : v.name ≠ x := by rintro rfl; exact not_mem_of_findDecl_none hfr hx
        rw [findDecl_cons]; exact ite_eq_right_iff.mpr (fun h => absurd h hne)
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx
        exact not_mem_of_findDecl_none hfr
      · intro x hx; exact set_wk_ne (by simpa using hx)
      · intro x hx b hb
        simp only [List.mem_singleton] at hx; subst hx
        simp only [Binds.set, ite_true, Option.some.injEq] at hb; subst hb
        exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩
  | @induct _ _ _ _ ι' I B' lps' Is' Cs' Rs' orders' hP hnd hfr _ hext hblk _ ih =>
    intro ι η
    have hbnd : ∀ ci ∈ IndBlock.decls Is' Cs' Rs', ∀ b, B' ci.name = some b →
        (∃ s, b = .ind .here s) ∨ (∃ s c, b = .ctor .here s c (orders' s c)) ∨
          ∃ s os, b = .recr .here s os := by
      intro ci hci b hb
      rcases IndBlock.mem_decls hci with ⟨s, rfl⟩ | ⟨s, c, rfl⟩ | ⟨s, rfl⟩ <;>
        first | rw [name_recInfo] at hb | rw [name_ctorInfo] at hb | rw [name_inductInfo] at hb
      · rw [(hblk.recr s).2.1] at hb; cases hb; exact .inr (.inr ⟨s, _, rfl⟩)
      · rw [(hblk.ctor s c).1] at hb; cases hb; exact .inr (.inl ⟨s, c, rfl⟩)
      · rw [(hblk.ind s).1] at hb; cases hb; exact .inl ⟨s, rfl⟩
    have hold := fun x hx => hext x hx
    cases η with
    | here =>
      refine ⟨lps', Is', Cs', Rs', orders', ⟨⟨_, _, _, _, hblk⟩, hnd, fun ci hci => ?_,
        fun t => (hblk.recr t).2.1, fun x t hx => ?_, fun x t c o hx => ?_⟩, hblk.indexVars⟩
      · rw [findDecl_append, findDecl_of_nodup hnd hci]; rfl
      · by_cases hn : x ∈ (IndBlock.decls Is' Cs' Rs').map (·.name)
        · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
          rcases IndBlock.mem_decls hci with ⟨s, rfl⟩ | ⟨s, c, rfl⟩ | ⟨s, rfl⟩ <;>
            first | rw [name_recInfo] at hx | rw [name_ctorInfo] at hx | rw [name_inductInfo] at hx
          · rw [(hblk.recr s).2.1] at hx; cases hx
          · rw [(hblk.ctor s c).1] at hx; cases hx
          · rw [(hblk.ind s).1] at hx; cases hx; rfl
        · rw [hold x hn] at hx
          obtain ⟨b, -, hbw⟩ := Option.map_eq_some_iff.mp hx
          cases b <;> simp only [MBinding.wk] at hbw <;> cases hbw
      · by_cases hn : x ∈ (IndBlock.decls Is' Cs' Rs').map (·.name)
        · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
          rcases IndBlock.mem_decls hci with ⟨s, rfl⟩ | ⟨s, c, rfl⟩ | ⟨s, rfl⟩ <;>
            first | rw [name_recInfo] at hx | rw [name_ctorInfo] at hx | rw [name_inductInfo] at hx
          · rw [(hblk.recr s).2.1] at hx; cases hx
          · rw [(hblk.ctor s c).1] at hx; cases hx; rfl
          · rw [(hblk.ind s).1] at hx; cases hx
        · rw [hold x hn] at hx
          obtain ⟨b, -, hbw⟩ := Option.map_eq_some_iff.mp hx
          cases b <;> simp only [MBinding.wk] at hbw <;> cases hbw
    | there η =>
      obtain ⟨lps, Is, Cs, Rs, orders, hb, hix⟩ := ih η
      refine ⟨lps, Is, Cs, Rs, orders, hb.there (new := (IndBlock.decls Is' Cs' Rs').map (·.name))
        (fun x hx => ?_) (fun x hx hxP => ?_) hold (fun x hx b hbx => ?_), hix.there⟩
      · have hd : findDecl (IndBlock.decls Is' Cs' Rs') x = none := by
          cases hd : findDecl (IndBlock.decls Is' Cs' Rs') x with
          | none => rfl
          | some ci =>
            obtain ⟨hm, rfl⟩ := findDecl_eq_some hd
            exact absurd hx (not_mem_of_findDecl_none (hfr ci hm))
        rw [findDecl_append, hd]; rfl
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hx
        exact not_mem_of_findDecl_none (hfr ci hci) hxP
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hx
        rcases hbnd ci hci b hbx with ⟨s, rfl⟩ | ⟨s, c, rfl⟩ | ⟨s, os, rfl⟩ <;>
          exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩
  | @quot _ _ _ _ _ qs B' hP _ _ hfr _ hext hq ih =>
    intro ι η
    cases η with
    | there η =>
      obtain ⟨lps, Is, Cs, Rs, orders, hb, hix⟩ := ih η
      refine ⟨lps, Is, Cs, Rs, orders, hb.there (new := qs.map (·.name)) (fun x hx => ?_)
        (fun x hx hxP => ?_) (fun x hx => by rw [hext x hx]; rfl) (fun x hx b hbx => ?_), hix.there⟩
      · have hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) x = none := by
          cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) x with
          | none => rfl
          | some ci =>
            obtain ⟨hm, rfl⟩ := findDecl_eq_some hd
            simp only [List.mem_map, List.mem_reverse] at hm
            obtain ⟨q, hq', rfl⟩ := hm
            exact absurd hx (not_mem_of_findDecl_none (hfr q hq'))
        rw [findDecl_append, hd]; rfl
      · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
        exact not_mem_of_findDecl_none (hfr q hq') hxP
      · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
        rw [(hq q hq').1] at hbx; cases hbx
        exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩

/-- Every inductive head of the environment is the head of an inductive block of the program.
Reference: `declared_inductive` (MC §3.6). -/
theorem ProgEnv.block (h : ProgEnv P ζ E B) {ι : Metalean.IndSig} (η : Head ζ (.inductive ι)) :
    ∃ lps Is Cs Rs orders, BlockAt P B η lps Is Cs Rs orders := by
  obtain ⟨lps, Is, Cs, Rs, orders, hb, -⟩ := ProgEnv.blockIdx h η
  exact ⟨lps, Is, Cs, Rs, orders, hb⟩

/-! ## Inversions of the translation -/

/-- `peelLams` peels its last λ after the others. -/
theorem peelLams_succ (k : Nat) (e : Expr) :
    peelLams (k + 1) e = (peelLams k e).bind (peelLams 1) := by
  induction k generalizing e with
  | zero => cases e <;> rfl
  | succ k ih => cases e <;> simp [peelLams, ih]

/-- Enter `k` λ/Π binders. -/
def pushLams {ℓ m : Nat} (Δ : MLCtx ζ ℓ m) : (k : Nat) → MLCtx ζ ℓ (m + k)
  | 0 => Δ
  | k + 1 => (pushLams Δ k).pushLam none

/-- The bound variables entered last denote the last variables. -/
theorem findB_pushLams_lt {ℓ m : Nat} (Δ : MLCtx ζ ℓ m) :
    ∀ (k j : Nat) (hj : j < k),
      (pushLams Δ k).findB j = some (.var ⟨m + (k - 1 - j), by omega⟩)
  | 0, _, hj => absurd hj (by omega)
  | k + 1, 0, _ => by simp [pushLams, MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Fin.last]
  | k + 1, j + 1, hj => by
    simp only [pushLams, MLCtx.pushLam, MLCtx.findB]
    rw [MLCtx.findB_map_wk, findB_pushLams_lt Δ k j (by omega)]
    simp only [Option.map_some, Metalean.Expr.wk, Metalean.Expr.wkFrom]
    congr 2
    simp [Metalean.Expr.rename, Metalean.Ren.wkFrom]
    split <;> (apply Fin.ext; simp only; omega)

/-- The older locals, weakened past the `k` new binders. -/
theorem findB_pushLams_ge {ℓ m : Nat} (Δ : MLCtx ζ ℓ m) :
    ∀ (k j : Nat), (pushLams Δ k).findB (k + j) = (Δ.findB j).map (·.wkN k)
  | 0, j => by simp [pushLams, Metalean.Expr.wkN]
  | k + 1, j => by
    simp only [pushLams, MLCtx.pushLam, show k + 1 + j = (k + j) + 1 by omega, MLCtx.findB]
    rw [MLCtx.findB_map_wk, findB_pushLams_ge Δ k j, Option.map_map]
    rfl

/-- `Forall₂` of two lists extended at the end. -/
theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {a : α} {b : β}
    (h : List.Forall₂ R l l') (hab : R a b) : List.Forall₂ R (l ++ [a]) (l' ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

/-- A term whose head is not a constant is not a spine of a constant. -/
theorem ne_mkAppN_const {e : Expr} (he : ∀ c us, e.getAppFn ≠ .const c us) {c : Name}
    {us : List Level} {as : List Expr} : e ≠ mkAppN (.const c us) as.toArray := by
  intro h
  apply he c us
  rw [h, mkAppN_eq_foldl, foldl_app_getAppFn]; rfl

section
variable {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- The translation of a λ is a λ. -/
theorem trM_lam_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {x : Name} {A b : Expr} {bi : BinderInfo} {V : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.lam x A b bi) V) :
    ∃ A' b', V = .lam A' b' ∧ TrM E B lps (Γ.snoc A') (Δ.pushLam none) b b' := by
  generalize hx : Expr.lam x A b bi = e at h
  cases h with
  | lam _ hb => cases hx; exact ⟨_, _, rfl, hb⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- The translation of a term under `k` λ's is a λ over a telescope of `k` binders around a
translation of the body. -/
theorem trM_peel : ∀ (k : Nat) {m : Nat} {Γ : Metalean.Ctx ζ lps.length 0 m}
    {Δ : MLCtx ζ lps.length m} {e body : Expr} {V : Metalean.Expr ζ lps.length m},
    peelLams k e = some body → TrM E B lps Γ Δ e V →
    ∃ (Θ : Metalean.Ctx ζ lps.length m (m + k)) (b : Metalean.Expr ζ lps.length (m + k))
      (Γ' : Metalean.Ctx ζ lps.length 0 (m + k)),
      V = Θ.lam b ∧ TrM E B lps Γ' (pushLams Δ k) body b
  | 0, _, Γ, _, _, _, _, hp, h => by
    cases hp; exact ⟨.nil, _, Γ, rfl, h⟩
  | k + 1, _, _, _, e, body, _, hp, h => by
    rw [peelLams_succ] at hp
    cases he : peelLams k e with
    | none => rw [he] at hp; cases hp
    | some e' =>
      rw [he] at hp
      obtain ⟨Θ, b, Γ', rfl, hb⟩ := trM_peel k he h
      cases e' with
      | lam x A b₀ bi =>
        cases hp
        obtain ⟨A', b', rfl, hb'⟩ := trM_lam_inv hb
        exact ⟨Θ.snoc A', b', Γ'.snoc A', rfl, hb'⟩
      | _ => cases hp

/-- A spine whose head does not saturate translates argument by argument. -/
theorem trM_spine_inv {h : Expr} (hns : ¬ SpecialHead B h) :
    ∀ {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (as : List Expr)
      {t : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ (mkAppN h as.toArray) t →
      ∃ h' as', TrM E B lps Γ Δ h h' ∧ List.Forall₂ (TrM E B lps Γ Δ) as as' ∧
        t = h'.appList as' := by
  intro n Γ Δ as
  induction as using List.reverseRecOn with
  | nil => intro t ht; exact ⟨t, [], ht, .nil, rfl⟩
  | append_singleton as x ih =>
    intro t ht
    rw [mkAppN_eq_foldl, List.foldl_append] at ht
    simp only [List.foldl_cons, List.foldl_nil] at ht
    generalize hx : Expr.app (List.foldl Expr.app h as) x = e at ht
    cases ht with
    | app _ hf ha =>
      cases hx
      rw [← mkAppN_eq_foldl] at hf
      obtain ⟨h', as', hh, has, rfl⟩ := ih hf
      exact ⟨h', as' ++ [_], hh, forall₂_snoc has ha, by simp [Metalean.Expr.appList]⟩
    | @special c us _ _ _ _ _ b _ hb hsp =>
      refine absurd ⟨c, us, b, ?_, hb, hsp⟩ hns
      have := congrArg Expr.getAppFn hx
      rw [mkAppN_eq_foldl, foldl_app_getAppFn] at this
      exact (foldl_app_getAppFn as h).symm.trans this
    | _ => cases hx

/-- A saturated spine of a recursor translates to the Metalean recursor node, the arguments
translated one by one, the minors wrapped by `wrapCase`, at the translated levels. -/
theorem trM_recr_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {R : Name} {us : List Level} {args : List Expr} {t : Metalean.Expr ζ lps.length n}
    {ι : Metalean.IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {orders : List (List (List Nat))}
    (hB : B R = some (.recr η s orders)) (hlen : args.length = ι.recrEnd s)
    (h : TrM E B lps Γ Δ (mkAppN (.const R us) args.toArray) t) :
    ∃ (ls : Fin ι.nlevels → Metalean.Level lps.length)
      (l : Metalean.Level lps.length) (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat)
      (A : Fin (ι.recrEnd s) → Metalean.Expr ζ lps.length n)
      (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Metalean.Expr ζ lps.length n),
      (∀ i : Fin (ι.recrEnd s), ∃ a, args[i.val]? = some a ∧ TrM E B lps Γ Δ a (A i)) ∧
      (∀ t c, (orders[t.val]?.bind (·[c.val]?)) = some (mo t c)) ∧
      (∀ t c, Metalean.Frontend.wrapCase (E.get η).block η ls
        (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
        (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
        (A (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve) = .ok (mins t c)) ∧
      t = .recr η s ls l
          (fun p => A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) mins
          (fun i => A (Metalean.IndSig.RecrBinder.index i).resolve)
          (A (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve) ∧
      ∃ us', RecrLevels (E.get η).block lps us l us' ∧ TrLevels lps us' ι.nlevels = some ls := by
  obtain ⟨init, last, rfl⟩ : ∃ init last, args = init ++ [last] := by
    rcases List.eq_nil_or_concat args with h0 | ⟨L, b, h1⟩
    · subst h0; simp at hlen
    · exact ⟨L, b, by rw [h1, List.concat_eq_append]⟩
  have hsp : SpecialHead B (mkAppN (.const R us) init.toArray) :=
    ⟨R, us, _, by rw [mkAppN_eq_foldl, foldl_app_getAppFn]; rfl, hB, rfl⟩
  have happ : mkAppN (.const R us) (init ++ [last]).toArray =
      .app (mkAppN (.const R us) init.toArray) last := by
    simp only [mkAppN_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [happ] at h
  generalize hx : Expr.app (mkAppN (.const R us) init.toArray) last = e at h
  cases h with
  | app hns => cases hx; exact absurd hsp hns
  | @special c us₂ _ _ _ as as' b _ hb _ hl hargs hsat =>
    rw [← happ, mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj hx
    rw [hB] at hb
    cases hb
    cases hsat with
    | recrEta _ _ _ hlt => omega
    | recrSat mo A rest mins hrl htl hmo hw =>
      have hrest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_append, List.length_ofFn] at hl hlen
        omega
      subst hrest
      refine ⟨_, _, mo, A, mins, fun i => ?_, hmo, hw, rfl, _, hrl, htl⟩
      have hi : i.val < (init ++ [last]).length := by rw [hlen]; exact i.isLt
      refine ⟨_, List.getElem?_eq_getElem hi,
        hargs i.val _ (A i) (List.getElem?_eq_getElem hi) ?_⟩
      rw [List.append_nil, List.getElem?_ofFn]
      split
      · rfl
      · exact absurd i.isLt ‹_›
  | _ => cases hx
end

/-! ## More inversions -/

section
variable {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- A bound variable translates to its local. -/
theorem trM_bvar_inv {j : Nat} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.bvar j) t) : Δ.findB j = some t := by
  generalize hx : Expr.bvar j = e at h
  cases h with
  | bvar h => cases hx; exact h
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- A constant bound to a Metalean constant translates to it. -/
theorem trM_const_inv {c : Name} {us : List Level} {kind : Metalean.ConstKind} {nl : Nat}
    {η : Head ζ (.const kind nl)} (hB : B c = some (.const η)) {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.const c us) t) : ∃ ls, t = .const η ls := by
  generalize hx : Expr.const c us = e at h
  cases h with
  | const hb =>
    cases hx
    rw [hB] at hb
    cases hb
    exact ⟨_, rfl⟩
  | @special c' us' _ _ _ as _ b _ hb hsp =>
    have := congrArg Expr.getAppFn hx
    rw [mkAppN_eq_foldl, foldl_app_getAppFn] at this
    cases this
    rw [hB] at hb
    cases hb
    cases hsp
  | _ => cases hx

/-- A Nat literal translates to the unary constructor chain. -/
theorem trM_lit_inv {v : Nat} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.lit (.natVal v)) t) :
    ∃ ηNat : Head ζ (.inductive natSig), B ``Nat = some (.ind ηNat 0) ∧ t = natLitM ηNat v := by
  generalize hx : Expr.lit (.natVal v) = e at h
  cases h with
  | lit hB => cases hx; exact ⟨_, hB, rfl⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- A translated Nat literal: ``Nat.zero`` and ``Nat.succ`` are the constructors `0` and `1` of
the inductive bound to ``Nat``. -/
theorem trM_lit_ctors {v : Nat} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.lit (.natVal v)) t) :
    ∃ (ηNat : Head ζ (.inductive natSig)) (o₀ o₁ : List Nat), B ``Nat = some (.ind ηNat 0) ∧
      B ``Nat.zero = some (.ctor ηNat 0 0 o₀) ∧ B ``Nat.succ = some (.ctor ηNat 0 1 o₁) := by
  generalize hx : Expr.lit (.natVal v) = e at h
  cases h with
  | lit hB h₀ h₁ => exact ⟨_, _, _, hB, h₀, h₁⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

end

/-- `Forall₂` at a position. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, l'[i]? = some b ∧ R a b := by
  intro l l' hl
  induction hl with
  | nil => intro i a h; simp at h
  | cons hab _ ih =>
    intro i a h
    cases i with
    | zero => cases h; exact ⟨_, rfl, hab⟩
    | succ i => exact ih (by simpa using h)

/-- Substitution distributes over an application spine. -/
theorem subst_appList {ℓ m n : Nat} (σ : Metalean.Subst ζ ℓ m n) :
    ∀ (xs : List (Metalean.Expr ζ ℓ m)) (f : Metalean.Expr ζ ℓ m),
      (f.appList xs).subst σ = (f.subst σ).appList (xs.map (·.subst σ))
  | [], _ => rfl
  | x :: xs, f => subst_appList σ xs (f.app x)

/-- Appending to an empty substitution. -/
theorem append_elim0 {α : Type} {k : Nat} (g : Fin k → α) (v : Fin (0 + k)) :
    Fin.append (Fin.elim0 : Fin 0 → α) g v = g ⟨v.val, by omega⟩ := by
  simp [Fin.append, Fin.addCases]; rfl

/-- `Fin.append` below the split. -/
theorem append_val_left {α : Type} {m k : Nat} (u : Fin m → α) (w : Fin k → α) {j : Nat}
    (h : j < m) (h' : j < m + k) : Fin.append u w ⟨j, h'⟩ = u ⟨j, h⟩ :=
  Fin.append_left u w ⟨j, h⟩

/-- `Fin.append` above the split. -/
theorem append_val_right {α : Type} {m k : Nat} (u : Fin m → α) (w : Fin k → α) {j : Nat}
    (h : m ≤ j) (h' : j < m + k) : Fin.append u w ⟨j, h'⟩ = w ⟨j - m, by omega⟩ := by
  have := Fin.append_right u w ⟨j - m, by omega⟩
  rw [← this]; congr 1; ext; simp; omega

/-- The recognizer's canonical minor body, as statements. -/
theorem isMinorBody_spec {e : Expr} {h L nf : Nat} (hb : isMinorBody e h L nf = true) :
    ∃ as : List Expr, e = mkAppN (.bvar h) as.toArray ∧ as.length = nf ∧
      ∀ f < nf, as[f]? = some (.bvar (L - 1 - f)) := by
  unfold isMinorBody at hb
  split at hb
  · rename_i h' as hsp
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hb
    obtain ⟨⟨rfl, hl⟩, hall⟩ := hb
    refine ⟨as, ?_, hl, fun f hf => CasesShape.isBVarAt_iff.mp (hall f hf)⟩
    have := CasesShape.spine_mkAppN e
    rw [hsp] at this
    exact this.symm
  · cases hb

/-! ## Counting -/

/-- `Fin.sum` is the sum of the list of values. -/
theorem fin_sum_eq : ∀ {k : Nat} (f : Fin k → Nat), Fin.sum f = (List.ofFn f).sum
  | 0, f => by simp [Fin.sum_zero]
  | k + 1, f => by rw [Fin.sum_succ, List.ofFn_succ, List.sum_cons, fin_sum_eq]

/-- The position of a constructor in the flattened list of a block's constructors. -/
theorem encodeSigma_val : ∀ {k : Nat} (f : Fin k → Nat) (t : Fin k) (c : Fin (f t)),
    (Fin.encodeSigma f ⟨t, c⟩).val = ((List.ofFn f).take t.val).sum + c.val
  | 0, _, t, _ => t.elim0
  | k + 1, f, ⟨0, _⟩, c => by simp [Fin.encodeSigma]
  | k + 1, f, ⟨t + 1, ht⟩, c => by
    have ih := encodeSigma_val (fun i : Fin k => f i.succ) ⟨t, by omega⟩ c
    simp only [Fin.encodeSigma, List.ofFn_succ, List.take_succ_cons, List.sum_cons]
    rw [Nat.add_assoc, ← ih]

/-- `blockCtorCount` sums the constructor counts of the listed inductives. -/
theorem blockCtorCount_sum {decls : List ConstantInfo} {l : List Name} {cs : List Nat}
    (hl : List.Forall₂ (fun x k => ∀ it, findDecl decls x = some (.inductInfo it) →
      it.ctors.length = k) l cs) : ∀ {b : Nat}, blockCtorCount decls l = some b → b = cs.sum := by
  induction hl with
  | nil => intro b h; simp [blockCtorCount] at h; simp [h]
  | @cons x k l cs hx _ ih =>
    intro b h
    unfold blockCtorCount at h
    split at h
    · rename_i it m hfx hbl
      cases h
      rw [List.sum_cons, ← ih hbl, hx it hfx]
    · cases h

/-- `ctorAlts` has one alternative per constructor, with the constructor's field count. -/
theorem ctorAlts_spec {decls : List ConstantInfo} :
    ∀ {l : List Name} {alts : List CasesAltInfo}, ctorAlts decls l = some alts →
      alts.length = l.length ∧ ∀ i (hi : i < l.length), ∃ cv,
        findDecl decls l[i] = some (.ctorInfo cv) ∧ altFields alts i = cv.numFields
  | [], alts, h => by simp [ctorAlts] at h; subst h; simp
  | x :: l, alts, h => by
    unfold ctorAlts at h
    split at h
    · rename_i cv as hx hl
      cases h
      obtain ⟨hlen, hi⟩ := ctorAlts_spec hl
      refine ⟨by simp [hlen], fun i hi' => ?_⟩
      cases i with
      | zero => exact ⟨cv, hx, by simp [altFields]⟩
      | succ i =>
        obtain ⟨cv', h1, h2⟩ := hi i (by simpa using hi')
        exact ⟨cv', by simpa using h1, by simpa [altFields] using h2⟩
    · cases h

/-- Relate two lists elementwise. -/
theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hl, h =>
    .cons (h 0 a b rfl rfl)
      (forall₂_of_getElem? (by simpa using hl) fun i x y h1 h2 => h (i + 1) x y h1 h2)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The Metalean fields that a constructor order picks, truncated to the field count. -/
theorem order_fields {α : Type} {nf nr : Nat} {order : List Nat} {fs : List α}
    {fds : Fin nf → α} {recFds : Fin nr → α} (hmo : MetaOrderOK order nf nr)
    (hperm : ∀ o : Fin (nf + nr), ∃ j a, order[o.val]? = some j ∧ fs[j]? = some a ∧
      Fin.append fds recFds o = a) :
    (fs.take (nf + nr)).length = nf + nr ∧
    (∀ o : Fin (nf + nr), ∃ j a, order[o.val]? = some j ∧ (fs.take (nf + nr))[j]? = some a ∧
      Fin.append fds recFds o = a) ∧
    ∀ j, j < nf + nr → (fs.take (nf + nr))[j]? = fs[j]? := by
  obtain ⟨ords, recs, rfl, -, -, -, -, hp⟩ := hmo
  have hmem : ∀ j, j ∈ ords ++ recs ↔ j < nf + nr := fun j => by
    rw [hp.mem_iff, List.mem_range]
  have hlen : (ords ++ recs).length = nf + nr := by rw [hp.length_eq, List.length_range]
  have hge : nf + nr ≤ fs.length := by
    rcases Nat.eq_zero_or_pos (nf + nr) with h0 | hpos
    · omega
    · obtain ⟨o, ho, hoj⟩ := List.getElem_of_mem ((hmem (nf + nr - 1)).mpr (by omega))
      obtain ⟨j, a, h1, h2, -⟩ := hperm ⟨o, by omega⟩
      rw [List.getElem?_eq_getElem ho, hoj] at h1
      cases h1
      have := (List.getElem?_eq_some_iff.mp h2).1
      omega
  refine ⟨by simp; omega, fun o => ?_, fun j hj => List.getElem?_take_of_lt hj⟩
  obtain ⟨j, a, h1, h2, h3⟩ := hperm o
  have hj : j < nf + nr := (hmem j).mp (List.mem_of_getElem? h1)
  exact ⟨j, a, h1, by rw [List.getElem?_take_of_lt hj, h2], h3⟩

/-! ## Reduction lemmas -/

section
variable {E : Metalean.Env ζ} {ℓ n : Nat}

/-- Weak-head reduction of the head of an application spine. -/
theorem appList_whredS {f f' : Metalean.Expr ζ ℓ n} (h : E ⊢ f ⤳* f') :
    ∀ xs : List (Metalean.Expr ζ ℓ n), E ⊢ f.appList xs ⤳* f'.appList xs := by
  intro xs
  induction xs generalizing f f' with
  | nil => exact h
  | cons x xs ih => exact ih (WHRedS.frame (.app x) h)

/-- A λ over a telescope of `k` binders, its levels instantiated and its free variables
substituted, applied to `k` arguments, reduces by β to its body under the substitution extended by
the arguments. -/
theorem lams_beta {ℓ₀ m k : Nat} (Θ : Metalean.Ctx ζ ℓ₀ m (m + k))
    (b : Metalean.Expr ζ ℓ₀ (m + k)) (ls : Metalean.Param ℓ₀ → Metalean.Level ℓ)
    (σ : Metalean.Subst ζ ℓ m n) (xs : Fin k → Metalean.Expr ζ ℓ n) :
    E ⊢ ((Θ.lam b){ls}.subst σ).apps xs ⤳* b{ls}.subst (Fin.append σ xs) := by
  rw [Metalean.Ctx.lam_instL, Metalean.Ctx.lam_subst]
  have := Ctx.lam_apps_whredS (E := E) (Metalean.Ctx.substN σ k Θ{ls}) (b{ls}.subst (σ.liftN k)) xs
  rwa [Metalean.Expr.subst_subst, Metalean.Subst.liftN_comp_append, Metalean.Subst.comp_id] at this

end

/-! ## The reduction -/

section
variable {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo} {lps : List Name} {n : Nat}
  {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- The ordinary fields `fds`, recursive fields `recFds` and the Lean-order list `fs'` of a
constructor, related by the constructor's field order. -/
def FieldsPerm {α : Type} {nf nr : Nat} (order : List Nat) (fs' : List α) (fds : Fin nf → α)
    (recFds : Fin nr → α) : Prop :=
  ∀ o : Fin (nf + nr), ∃ j a, order[o.val]? = some j ∧ fs'[j]? = some a ∧ Fin.append fds recFds o = a

/-- A saturated recognized `casesOn` of the inductive `iv`, bound to the sort `s` of the Metalean
block at `η`, whose major premise translates to the Metalean constructor `k` with fields `fs'`
(translations of the Lean fields `fs`, related to the Metalean fields by the constructor's field
order), reduces to the translation of the `k`-th alternative applied to `fs'`: by δ (the `casesOn`
definition), β (its λ's), ι (the recursor on the constructor) and β (`wrapCase` and the canonical
minor, whose arity is the recursor's minor arity). -/
theorem casesOn_whred_core {σ : EvalEnv} {c : Name} {iv : InductiveVal} {args : List Expr}
    {m a alt : Expr} {fs : List Expr} {us : List Level} {t : Metalean.Expr ζ lps.length n}
    {ι : Metalean.IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} (k : Fin (ι.nctors s))
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hcs : σ.casesOn? c = some iv) (hlen : args.length + 1 = casesArity iv)
    (hBT : B iv.name = some (.ind η s)) (hm : args[casesMajor iv]? = some m)
    (hM : ∀ m', TrM E B lps Γ Δ m m' → ∀ order,
      MetaOrderOK order (ι.ctors s k).nfields (ι.ctors s k).nrecFields →
      (∀ x o, B x = some (.ctor η s k o) → o = order) →
      ∃ ls₂ ps₂ fds recFds fs', m' = .ctor η s k ls₂ ps₂ fds recFds ∧
        fs'.length = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields ∧
        List.Forall₂ (TrM E B lps Γ Δ) fs fs' ∧ FieldsPerm order fs' fds recFds)
    (halt : (args ++ [a])[casesMajor iv + 1 + k.val]? = some alt)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) (args ++ [a]).toArray) t) :
    ∃ alt' fs', TrM E B lps Γ Δ alt alt' ∧ List.Forall₂ (TrM E B lps Γ Δ) fs fs' ∧
      E ⊢ t ⤳* alt'.appList fs' := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨d, R, j, before, alts, body, rargs, -, hd, hiv, hR, -, -, -, -, hj, hbe, halts, hbody,
    hbdy, hrlen, -, -, hmin, -, hmaj⟩ := casesOn_shape hcs
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨_, _, _, _, hIB⟩, hnd, hfd, hrec, hindB, hctorB⟩ :=
    ProgEnv.block henv η
  have hT : iv.name = (Is s).name := hindB _ _ hBT
  have hmemI : ∀ t, ConstantInfo.inductInfo (Is t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hmemC : ∀ t c, ConstantInfo.ctorInfo (Cs t c) ∈ IndBlock.decls Is Cs Rs := fun t c => by
    simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
    exact .inl (.inr ⟨_, ⟨t, rfl⟩, List.mem_ofFn.mpr ⟨c, rfl⟩⟩)
  have hmemR : ∀ t, ConstantInfo.recInfo (Rs t) ∈ IndBlock.decls Is Cs Rs := fun t => by
    simp [IndBlock.decls, List.mem_ofFn]
  have hfdI : ∀ t, findDecl P (Is t).name = some (.inductInfo (Is t)) := fun t => hfd _ (hmemI t)
  have hfdC : ∀ t c, findDecl P (Cs t c).name = some (.ctorInfo (Cs t c)) := fun t c =>
    hfd _ (hmemC t c)
  have hfdR : ∀ t, findDecl P (Rs t).name = some (.recInfo (Rs t)) := fun t => hfd _ (hmemR t)
  have hivs : iv = Is s := by
    have h1 := hP hiv
    rw [hT, hfdI s] at h1
    cases h1; rfl
  subst hivs
  have hRs : R = Rs s := by
    have h1 := hP hR
    rw [← (hIB.recr s).1, hfdR s] at h1
    cases h1; rfl
  subst hRs
  have hmo := (hIB.ctor s k).2.2.2.2.2.2.2
  obtain ⟨-, -, hall, hInp, hIni, hIctors, -, -⟩ := hIB.ind s
  obtain ⟨hRname, -, -, -, -, hRall, hRnp, hRnm, hRmin, hRni⟩ := hIB.recr s
  have hnodupI : (List.ofFn fun t => (Is t).name).Nodup := by
    have h1 := hnd
    simp only [IndBlock.decls, List.map_append, List.map_ofFn] at h1
    exact (List.nodup_append.mp h1).2.1
  have hidx : (Rs s).all.idxOf (Is s).name = s.val := by
    rw [hRall, hall]
    have := hnodupI.idxOf_getElem s.val (by simp)
    simpa using this
  have hbefore : before = ((List.ofFn fun t => ι.nctors t).take s.val).sum := by
    rw [hidx, hRall, hall] at hbe
    refine blockCtorCount_sum (List.forall₂_take _ (forall₂_of_getElem? (by simp)
      fun j x y h1 h2 => ?_)) hbe
    rw [List.getElem?_ofFn] at h1 h2
    split at h1
    · rename_i hj
      simp only [hj, ↓reduceDIte, Option.some.injEq] at h2
      cases h1; cases h2
      intro it hit
      have := hP hit
      rw [hfdI ⟨j, hj⟩] at this
      cases this
      rw [(hIB.ind ⟨j, hj⟩).2.2.2.2.2.1, List.length_ofFn]
    · cases h1
  have hD : casesArity (Is s) = ι.nparams + 1 + ι.nindices s + 1 + ι.nctors s := by
    simp only [casesArity, casesMajor, hInp, hIni, hIctors, List.length_ofFn]
  have hcM : casesMajor (Is s) = ι.nparams + 1 + ι.nindices s := by
    simp only [casesMajor, hInp, hIni]
  have hrecrEnd : rargs.length = ι.recrEnd s := by
    rw [hrlen, hRnp, hRnm, hRmin, hRni]
    show _ = ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1
    rw [fin_sum_eq]
  obtain ⟨ηc, hBc, htrv⟩ := ProgEnv.lookup_def henv (hP hd)
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us'', b, h1, h2, h3⟩
    cases h1; rw [hBc] at h2; cases h2; cases h3
  obtain ⟨h', xs, hh', hxs, rfl⟩ := trM_spine_inv hns (args ++ [a]) he
  obtain ⟨lsc, rfl⟩ := trM_const_inv hBc hh'
  have hxslen : xs.length = casesArity (Is s) := by
    rw [← hxs.length_eq]; simp; omega
  obtain ⟨Θ, b, Γ', hdef, hb⟩ := trM_peel _ hbody htrv
  rw [hbdy] at hb
  obtain ⟨lsR, lR, mo, A, mins, hA, hmo', hw, hbeq, -⟩ := trM_recr_inv (hrec s) hrecrEnd hb
  let g : Fin (casesArity (Is s)) → Metalean.Expr ζ lps.length n := fun j => xs[j.val]'(by omega)
  let σ₀ : Metalean.Subst ζ lps.length 0 n := Fin.elim0
  have hδβ : E ⊢ (Metalean.Expr.const ηc lsc).appList xs ⤳* b{lsc}.subst (Fin.append σ₀ g) := by
    refine (appList_whredS (E := E) (Relation.ReflTransGen.single
      (WHRed.delta (η := ηc) (ls := lsc))) xs).trans ?_
    rw [hdef, ← Metalean.Expr.subst_closed _ σ₀,
      appList_eq_apps _ g hxslen (fun j => by simp [g])]
    exact lams_beta (E := E) Θ _ lsc σ₀ g
  -- the major premise: a constructor
  have hcMlt : casesMajor (Is s) < args.length := by have := k.isLt; omega
  have hmaj' : (args ++ [a])[casesMajor (Is s)]? = some m := by
    rw [List.getElem?_append_left hcMlt]; exact hm
  obtain ⟨m', hxm, hm'⟩ := forall₂_getElem? hxs hmaj'
  obtain ⟨ls₂, ps₂, fds, recFds, fsT, rfl, hlT, hfsT, hpermT⟩ :=
    hM m' hm' _ hmo fun x o h => hctorB x s k o h
  obtain ⟨a₀, ha₀, htr₀⟩ := hA (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve
  have hpos : ((Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve).val =
      (Is s).numParams + (Rs s).numMotives + (Rs s).numMinors + (Is s).numIndices := by
    simp only [Metalean.IndSig.RecrBinder.resolve, Fin.val_last, hInp, hRnm, hRmin, hIni,
      Metalean.IndSig.casesEnd, Metalean.IndSig.motivesEnd, fin_sum_eq]
  rw [hpos, hmaj] at ha₀
  cases ha₀
  have hfb := trM_bvar_inv htr₀
  rw [findB_pushLams_lt _ _ _ (by omega)] at hfb
  have hAmaj : ((A (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve){lsc}).subst
      (Fin.append σ₀ g) = .ctor η s k ls₂ ps₂ fds recFds := by
    rw [← Option.some.inj hfb]
    show Fin.append σ₀ g _ = _
    rw [append_elim0]
    simp only [g]
    have : casesArity (Is s) - 1 - (casesArity (Is s) - 1 - casesMajor (Is s)) = casesMajor (Is s) := by
      omega
    simp only [Nat.zero_add, this]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hxm)
  -- ι and the field permutation
  have hmok : mo s k = orders s k := by
    have := hmo' s k
    simp only [List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.bind_some] at this
    exact (Option.some.inj this).symm
  have hw' := wrapCase_subst _ _ _ _ _ _ _ _ (Fin.append σ₀ g)
    (wrapCase_instL _ _ _ _ _ _ _ _ lsc (hw s k))
  rw [hmok] at hw'
  obtain ⟨ihs, hiota⟩ : ∃ ihs : Fin (ι.ctors s k).nrecFields → Metalean.Expr ζ lps.length n,
      E ⊢ b{lsc}.subst (Fin.append σ₀ g) ⤳*
        ((((A (Metalean.IndSig.RecrBinder.case (s := s) s k).resolve){lsc}).subst
          (Fin.append σ₀ g)).appList fsT).apps ihs := by
    have hstep : E ⊢ b{lsc}.subst (Fin.append σ₀ g) ⤳
        (E.get η).block.iotaRhs η lsR{lsc} lR{lsc}
          (fun p => ((A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve){lsc}).subst
            (Fin.append σ₀ g))
          (fun t => ((A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve){lsc}).subst
            (Fin.append σ₀ g))
          (fun t c => ((mins t c){lsc}).subst (Fin.append σ₀ g)) s k fds recFds := by
      rw [hbeq]
      show E ⊢ Metalean.Expr.recr η s _ _ _ _ _ _ (((A _){lsc}).subst (Fin.append σ₀ g)) ⤳ _
      rw [hAmaj]
      exact WHRed.iota
    rw [Metalean.Inductive.iotaRhs] at hstep
    exact ⟨_, Relation.ReflTransGen.head hstep (ctorSat_iota hw' hmo _ hlT fds recFds hpermT _)⟩
  -- the canonical minor of constructor `k`
  obtain ⟨haltlen, haltf⟩ := ctorAlts_spec halts
  have hk' : k.val < alts.length := by rw [haltlen, hIctors, List.length_ofFn]; exact k.isLt
  obtain ⟨a₁, mb, ha₁, hpeel, hmb⟩ := hmin k.val hk'
  have hnfalt : altFields alts k.val = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields := by
    obtain ⟨cv', h1, h2⟩ := haltf k.val (by rw [hIctors, List.length_ofFn]; exact k.isLt)
    rw [h2]
    have h3 := hP h1
    simp only [hIctors, List.getElem_ofFn] at h3
    rw [hfdC s k] at h3
    cases h3
    exact (hIB.ctor s k).2.2.2.2.2.1
  have hcanon : (Is s).numParams + (Rs s).numMotives + before + k.val =
      ι.nparams + ι.nsorts + ((List.ofFn fun t => ι.nctors t).take s.val).sum + k.val := by
    rw [hInp, hRnm, hbefore]
  rw [hcanon] at ha₁ hpeel hmb
  rw [hIB.minors s s k] at hpeel hmb
  rw [hnfalt] at hmb
  obtain ⟨a₁', ha₁', htr₁⟩ := hA (Metalean.IndSig.RecrBinder.case (s := s) s k).resolve
  have hpos₁ : ((Metalean.IndSig.RecrBinder.case (s := s) s k).resolve).val =
      ι.nparams + ι.nsorts + ((List.ofFn fun t => ι.nctors t).take s.val).sum + k.val := by
    simp only [Metalean.IndSig.RecrBinder.resolve, Fin.val_castSucc, Fin.val_castAdd,
      Fin.val_natAdd, encodeSigma_val, Metalean.IndSig.motivesEnd]
    exact (Nat.add_assoc _ _ _).symm
  rw [hpos₁, ha₁] at ha₁'
  cases ha₁'
  generalize hL : (ι.ctors s k).nfields + 2 * (ι.ctors s k).nrecFields = L at hpeel hmb
  obtain rfl : L = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields + (ι.ctors s k).nrecFields := by
    omega
  obtain ⟨Θ₂, b₂, Γ₂, hA₂, hb₂⟩ := trM_peel _ hpeel htr₁
  obtain ⟨as, rfl, haslen, hasf⟩ := isMinorBody_spec hmb
  have hns₂ : ¬ SpecialHead B (.bvar ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields +
      (ι.ctors s k).nrecFields + (casesArity (Is s) - 1 - (casesMajor (Is s) + 1 + k.val)))) := by
    rintro ⟨_, _, _, h1, -⟩; cases h1
  obtain ⟨h₂, as₂, hh₂, has₂, rfl⟩ := trM_spine_inv hns₂ as hb₂
  have hfb₂ := trM_bvar_inv hh₂
  rw [findB_pushLams_ge, findB_pushLams_lt _ _ _ (by omega)] at hfb₂
  obtain ⟨alt', hxalt, htralt⟩ := forall₂_getElem? hxs halt
  refine ⟨alt', fsT, htralt, hfsT, hδβ.trans (hiota.trans ?_)⟩
  rw [hA₂]
  let gT : Fin ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields) → Metalean.Expr ζ lps.length n :=
    fun j => fsT[j.val]'(by omega)
  rw [appList_eq_apps _ gT hlT (fun j => by simp [gT]), ← Metalean.Expr.apps_append]
  refine (lams_beta (E := E) Θ₂ _ lsc (Fin.append σ₀ g) (Fin.append gT ihs)).trans ?_
  rw [ML.Expr.instL_appList, subst_appList]
  have hh : (h₂{lsc}).subst (Fin.append (Fin.append σ₀ g) (Fin.append gT ihs)) = alt' := by
    simp only [Option.map_some, Option.some.injEq] at hfb₂
    rw [← hfb₂, Metalean.Expr.wkN_instL, Metalean.Expr.wkN_subst_append]
    show Fin.append σ₀ g _ = _
    rw [append_elim0]
    simp only [g]
    have : casesArity (Is s) - 1 - (casesArity (Is s) - 1 - (casesMajor (Is s) + 1 + k.val)) =
        casesMajor (Is s) + 1 + k.val := by omega
    simp only [Nat.zero_add, this]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hxalt)
  have hl : List.map (fun x => x.subst (Fin.append (Fin.append σ₀ g) (Fin.append gT ihs)))
      (as₂.map (·{lsc})) = fsT := by
    apply List.ext_getElem
    · simp [← has₂.length_eq, haslen, hlT]
    · intro f h1 h2
      have hf : f < (ι.ctors s k).nfields + (ι.ctors s k).nrecFields := by
        simpa [← has₂.length_eq, haslen] using h1
      obtain ⟨y, hy, hty⟩ := forall₂_getElem? has₂ (hasf f hf)
      have hfy := trM_bvar_inv hty
      rw [findB_pushLams_lt _ _ _ (by omega)] at hfy
      simp only [List.getElem_map]
      rw [(List.getElem_of_getElem? hy).2, ← Option.some.inj hfy]
      show Fin.append (Fin.append σ₀ g) (Fin.append gT ihs) _ = _
      rw [append_val_right _ _ (by omega), append_val_left _ _ (by omega)]
      simp only [gT]
      congr 1
      omega
  exact hh ▸ hl ▸ .refl


/-- A saturated recognized `casesOn` on a constructor value reduces to the translation of the
alternative applied to translations of the fields. Reference: `eval_iota`
(`MR P/PCUICWcbvEval.v:253`); DV-25. -/
theorem casesOn_whred_spine {σ : EvalEnv} {c : Name} {iv : InductiveVal} {args : List Expr}
    {m a alt : Expr} {i : Nat} {fs : List Expr} {us : List Level}
    {t : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hcs : σ.casesOn? c = some iv) (hlen : args.length + 1 = casesArity iv)
    (hm : args[casesMajor iv]? = some m) (hcv : CtorValue σ iv.name m i fs)
    (halt : (args ++ [a])[casesMajor iv + 1 + i]? = some alt)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) (args ++ [a]).toArray) t) :
    ∃ alt' fs', TrM E B lps Γ Δ alt alt' ∧ List.Forall₂ (TrM E B lps Γ Δ) fs fs' ∧
      E ⊢ t ⤳* alt'.appList fs' := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨C, us', cv, ps, hC, hind, hcidx, hps, hfs, rfl⟩ := hcv
  obtain ⟨ι, η, s, k, order, hBC, hk, hnp, hnf, hmo, hBT⟩ := ProgEnv.lookup_ctor henv (hP hC)
  rw [hind] at hBT
  obtain rfl : i = k.val := hcidx.symm.trans hk
  refine casesOn_whred_core k henv hsub hcs hlen hBT hm (fun m' hm' order' _ huniq => ?_) halt he
  obtain rfl := huniq _ _ hBC
  obtain ⟨ls₂, ps₂, fds, recFds, fs'', rfl, hrel, hperm⟩ :=
    TrM.ctor_inv hBC (by simp only [List.length_append]; omega) hm'
  obtain ⟨hlT, hpermT, htake⟩ := order_fields hmo hperm
  refine ⟨ls₂, ps₂, fds, recFds, _, rfl, hlT, ?_, hpermT⟩
  refine forall₂_of_getElem? (by rw [hlT, hfs, hnf]) fun j x y h1 h2 => ?_
  have hj : j < (ι.ctors s k).nfields + (ι.ctors s k).nrecFields := by
    have := (List.getElem?_eq_some_iff.mp h2).1; omega
  refine hrel (ps.length + j) x y ?_ ?_
  · rw [List.getElem?_append_right (by omega)]; simpa using h1
  · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn, hps, hnp,
      Nat.add_sub_cancel_left, ← htake j hj]
    exact h2

/-- A saturated recognized `casesOn` of `Nat` on a literal reduces to the translation of the
alternative (`Nat.zero`) or of the alternative applied to the predecessor (`Nat.succ`). -/
theorem casesOnLit_whred_spine {σ : EvalEnv} {c : Name} {iv : InductiveVal} {args : List Expr}
    {a : Expr} {v : Nat} {us : List Level} {t : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hcs : σ.casesOn? c = some iv) (hnat : iv.name = ``Nat)
    (hlen : args.length + 1 = casesArity iv)
    (hm : args[casesMajor iv]? = some (.lit (.natVal v)))
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) (args ++ [a]).toArray) t) :
    ∃ alt alt' fs', (args ++ [a])[casesMajor iv + 1 + min v 1]? = some alt ∧
      TrM E B lps Γ Δ alt alt' ∧
      List.Forall₂ (TrM E B lps Γ Δ) (if v = 0 then [] else [.lit (.natVal (v - 1))]) fs' ∧
      E ⊢ t ⤳* alt'.appList fs' := by
  have hP : ∀ {x ci}, findDecl σ.decls x = some ci → findDecl P x = some ci := fun h => by
    obtain ⟨hm, rfl⟩ := findDecl_eq_some h; exact hsub _ hm
  obtain ⟨d, -, -, -, -, -, -, -, hd, hiv, -⟩ := casesOn_shape hcs
  obtain ⟨ηc, hBc, -⟩ := ProgEnv.lookup_def henv (hP hd)
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us'', b, h1, h2, h3⟩
    cases h1; rw [hBc] at h2; cases h2; cases h3
  obtain ⟨-, xs, -, hxs, -⟩ := trM_spine_inv hns (args ++ [a]) he
  have hcMlt : casesMajor iv < args.length := by
    have := List.getElem?_eq_some_iff.mp hm; exact this.1
  obtain ⟨m', -, hm'⟩ := forall₂_getElem? hxs
    (by rw [List.getElem?_append_left hcMlt]; exact hm)
  obtain ⟨ηNat, hBNat, -⟩ := trM_lit_inv hm'
  obtain ⟨ηN₂, o₀, o₁, hBN₂, hz₀, hs₁⟩ := trM_lit_ctors hm'
  rw [hBNat] at hBN₂
  cases hBN₂
  obtain ⟨ι', η', s', hB', -, -, hctl⟩ := ProgEnv.lookup_ind henv (hP hiv)
  rw [hnat, hBNat] at hB'
  cases hB'
  have hBT : B iv.name = some (.ind ηNat 0) := hnat ▸ hBNat
  obtain ⟨k, hk⟩ : ∃ k : Fin (natSig.nctors 0), k.val = min v 1 :=
    ⟨⟨min v 1, by show min v 1 < 2; omega⟩, rfl⟩
  obtain ⟨alt, halt⟩ : ∃ alt, (args ++ [a])[casesMajor iv + 1 + k.val]? = some alt := by
    have : casesArity iv = casesMajor iv + 1 + 2 := by
      simp only [casesArity, hctl]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    simp only [List.length_append, List.length_singleton, hk]
    omega
  rw [hk] at halt
  refine (fun ⟨alt', fs', htr, hfs, hred⟩ => ⟨alt, alt', fs', halt, htr, hfs, hred⟩)
    (casesOn_whred_core (fs := if v = 0 then [] else [.lit (.natVal (v - 1))]) k henv hsub hcs hlen
      hBT hm (fun m'' hm'' order hmo _ => ?_) (by rw [hk]; exact halt) he)
  obtain ⟨ηNat', hBNat', rfl⟩ := trM_lit_inv hm''
  rw [hBNat] at hBNat'
  cases hBNat'
  cases v with
  | zero =>
    obtain rfl : k = 0 := Fin.ext (by simpa using hk)
    exact ⟨_, _, _, _, [], rfl, rfl, by simp, fun o => o.elim0⟩
  | succ v =>
    obtain rfl : k = 1 := Fin.ext (by simp [hk])
    obtain ⟨ords, recs, rfl, hl1, hl2, -, -, hp⟩ := hmo
    have hords : ords = [] := List.eq_nil_of_length_eq_zero hl1
    subst hords
    have hrecs : recs = [0] := by
      have := hp.length_eq; simp at this hl2
      match recs, hl2 with
      | [r], _ =>
        have := hp.mem_iff.mp (List.mem_singleton_self r)
        simp at this; rw [this]
    subst hrecs
    refine ⟨_, _, _, _, [natLitM ηNat v], rfl, rfl, ?_, fun o => ⟨0, natLitM ηNat v, ?_, rfl, ?_⟩⟩
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact .cons (TrM.lit hBNat hz₀ hs₁) .nil
    · match o with | ⟨0, _⟩ => rfl
    · match o with | ⟨0, _⟩ => rfl

end

end CasesWhred


section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {n : Nat}
  {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- A saturated recognized `casesOn` on a constructor value reduces (δ, β, ι, β through `wrapCase`
and the canonical minors) to the translation of the alternative applied to the fields.
Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`); `WHRed.delta`, `WHRed.iota`
(`ML Syntax/Reduction.lean`); DV-25. -/
theorem casesOn_whred {c : Name} {iv : InductiveVal} {m a alt : Expr} {i : Nat}
    {fs : List Expr} {us : List Level} {t : Metalean.Expr ζ lps.length n} {args : List Expr}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hcs : σ.casesOn? c = some iv) (hlen : args.length + 1 = casesArity iv)
    (hm : args[casesMajor iv]? = some m) (hcv : CtorValue σ iv.name m i fs)
    (halt : (args ++ [a])[casesMajor iv + 1 + i]? = some alt)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) (args ++ [a]).toArray) t) :
    ∃ t', TrM E B lps Γ Δ (mkAppN alt fs.toArray) t' ∧ E ⊢ t ⤳* t' := by
  obtain ⟨alt', fs', ha, hfs, hred⟩ :=
    CasesWhred.casesOn_whred_spine henv hsub hcs hlen hm hcv halt he
  obtain ⟨t', ht', hr⟩ := TrM.apps ha hfs
  exact ⟨t', ht', hred.trans hr⟩

/-- The same chain on a Nat literal major (`natLit`): the alternative of `Nat.zero`, or that of
`Nat.succ` applied to the predecessor. Reference: as `casesOn_whred`. -/
theorem casesOnLit_whred {c : Name} {iv : InductiveVal} {a : Expr} {k : Nat} {us : List Level}
    {t : Metalean.Expr ζ lps.length n} {args : List Expr}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hcs : σ.casesOn? c = some iv) (hnat : iv.name = ``Nat) (hlen : args.length + 1 = casesArity iv)
    (hm : args[casesMajor iv]? = some (.lit (.natVal k)))
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) (args ++ [a]).toArray) t) :
    ∃ alt t', (args ++ [a])[casesMajor iv + 1 + min k 1]? = some alt ∧
      TrM E B lps Γ Δ (if k = 0 then alt else .app alt (.lit (.natVal (k - 1)))) t' ∧
      E ⊢ t ⤳* t' := by
  obtain ⟨alt, alt', fs', halt, ha, hfs, hred⟩ :=
    CasesWhred.casesOnLit_whred_spine henv hsub hcs hnat hlen hm he
  obtain ⟨t', ht', hr⟩ := TrM.apps ha hfs
  refine ⟨alt, t', halt, ?_, hred.trans hr⟩
  cases k <;>
    (simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at ht' ⊢
     rw [mkAppN_eq_foldl] at ht'
     exact ht')

end

end EraseProof
