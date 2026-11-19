import EraseProof.Core.ExistsInv
import EraseProof.Core.StepsQuot
import EraseProof.Core.StepsRec

/-!
# The existence of the marking: steps

`markOf_exists` follows the shipping traversal (`Erasure.visitExpr` and the functions it calls,
`LeanToLambdaBox/Erasure.lean`) at the pure backend `Erasure.PureM` by induction on its fuel, as
`ExprSpec` does, and concludes that the visited term has a marking (`MarkOf`). Its statement at one
fuel is `ExistsSpec`: a successful run of `visitExpr` on a renamed term (`RenOK`, as in
`ExprSpec`) gives a marking of the term under the marking's locals. Each rule of `MarkOf` reads the
oracle on its term, whose answer on the renamed term is the same (`Pure.isErasable_ren`): an answer
`true` is the `erase` mark, an answer `false` the rule of the branch the traversal takes. At each
binder the marking picks a variable fresh for its locals and terms (`exists_fresh`), which the
renaming sends to the traversal's next variable (`RenOK.push`); between two siblings the counter
does not decrease and the registered masks keep every field (`travMonoAt`).

This module proves the steps of the cases of `visitExpr` other than recursors and recognized
`casesOn` spines: the oracle's `□`, a free variable, the terms `visitExpr` rejects, metadata, a λ,
a `let`, a projection, a literal, an application or a constant without a rule of its own
(`MarkOf.app`, `MarkOf.constApp`), and the spines with their own rule whose saturated part is a
constructor or `Quot.mk`/`Quot.lift` (`MarkOf.special`): the η-expansion `withAppEtaToMinArity`
gives `MarkEta` (`withAppEta_exists`) from what the rule does on a saturated spine (`ExSatSpec`).

Reference: none (DV-32: the marking is the traversal's decisions written on the term; MetaRocq's
`erase` is a function, `MR E/ErasureFunction.v:989`).
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

/-! ## Fresh variables -/

/-- The free variable named by the number `k`. Reference: none. -/
abbrev numFVar (k : Nat) : FVarId := ⟨.num .anonymous k⟩

/-- A number above that of `y`, if `y` is named by a number. Reference: none. -/
def fvBound (y : FVarId) : Nat :=
  match y.name with
  | .num _ k => k + 1
  | _ => 0

/-- Every term avoids the variables `numFVar k` from some bound on. -/
theorem exists_bound (e : Expr) : ∃ N, ∀ k, N ≤ k → FVarsIn (· ≠ numFVar k) e := by
  induction e with
  | fvar y =>
    refine ⟨fvBound y, fun k hk h => ?_⟩
    subst h
    simp only [fvBound] at hk
    omega
  | app f a ihf iha =>
    obtain ⟨N₁, h₁⟩ := ihf
    obtain ⟨N₂, h₂⟩ := iha
    exact ⟨max N₁ N₂, fun k hk => ⟨h₁ k (by omega), h₂ k (by omega)⟩⟩
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    obtain ⟨N₁, h₁⟩ := iht
    obtain ⟨N₂, h₂⟩ := ihb
    exact ⟨max N₁ N₂, fun k hk => ⟨h₁ k (by omega), h₂ k (by omega)⟩⟩
  | letE _ t v b _ iht ihv ihb =>
    obtain ⟨N₁, h₁⟩ := iht
    obtain ⟨N₂, h₂⟩ := ihv
    obtain ⟨N₃, h₃⟩ := ihb
    exact ⟨max N₁ (max N₂ N₃), fun k hk => ⟨h₁ k (by omega), h₂ k (by omega), h₃ k (by omega)⟩⟩
  | mdata _ e ih | proj _ _ e ih => exact ih
  | bvar | sort | const | lit | mvar => exact ⟨0, fun _ _ => trivial⟩

/-- Every list of terms avoids the variables `numFVar k` from some bound on. -/
theorem exists_bound_list : ∀ es : List Expr, ∃ N, ∀ k, N ≤ k → ∀ e ∈ es, FVarsIn (· ≠ numFVar k) e
  | [] => ⟨0, fun _ _ _ h => nomatch h⟩
  | e :: es => by
    obtain ⟨N₁, h₁⟩ := exists_bound e
    obtain ⟨N₂, h₂⟩ := exists_bound_list es
    refine ⟨max N₁ N₂, fun k hk a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h₁ k (by omega)
    · exact h₂ k (by omega) a ha

/-- Some variable is fresh for any locals and terms (`Fresh`), as a binder rule of `MarkOf` asks.
Reference: none (DV-13). -/
theorem exists_fresh (ls : List Local) (es : List Expr) : ∃ x, Fresh x ls es := by
  obtain ⟨N, hN⟩ := exists_bound_list
    (es ++ ls.flatMap fun l => .fvar l.fvarId :: l.type :: l.value?.toList)
  have h : ∀ e, e ∈ es ∨ (∃ l ∈ ls, e ∈ Expr.fvar l.fvarId :: l.type :: l.value?.toList) →
      FVarsIn (· ≠ numFVar N) e := fun e he =>
    hN N (Nat.le_refl _) e (by simpa only [List.mem_append, List.mem_flatMap] using he)
  refine ⟨numFVar N, fun l hl => ⟨h (.fvar l.fvarId) (.inr ⟨l, hl, by simp⟩),
    h l.type (.inr ⟨l, hl, by simp⟩), fun v hv => h v (.inr ⟨l, hl, by simp [hv]⟩)⟩,
    fun e he => h e (.inl he)⟩

/-! ## The statement at one fuel -/

/-- `e` has no string literal: `visitLiteral` turns one into `panic!`, a successful run that
leaves no marking. Reference: none. -/
def NoStrLit : Expr → Prop
  | .lit (.strVal _) => False
  | .app f a => NoStrLit f ∧ NoStrLit a
  | .lam _ t b _ | .forallE _ t b _ => NoStrLit t ∧ NoStrLit b
  | .letE _ t v b _ => NoStrLit t ∧ NoStrLit v ∧ NoStrLit b
  | .mdata _ e | .proj _ _ e => NoStrLit e
  | _ => True

/-- `NoStrLit` survives opening a binder with a free variable. -/
theorem NoStrLit.inst_fvar {x : FVarId} :
    ∀ {b : Expr} {d : Nat}, NoStrLit b → NoStrLit (b.instantiate1' (.fvar x) d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split
    · trivial
    · split <;> trivial
  | lit l => intro d h; cases l <;> exact h
  | _ => intro d h; simp_all [Expr.instantiate1', NoStrLit]

/-- The premises of `ExistsSpec` on a visited term: its free variables in `S`, `NatPlain`, no
string literal. Reference: none. -/
abbrev ExArgOK (S : FVarId → Prop) (cfg : ErasureConfig) (a : Expr) : Prop :=
  FVarsIn S a ∧ NatPlain cfg a ∧ NoStrLit a

/-- The premises of `ExistsSpec` on a spine hold of its head and its arguments. -/
theorem exArg_spine {S : FVarId → Prop} {cfg : ErasureConfig} {f : Expr} {as : List Expr}
    (h : ExArgOK S cfg (mkAppN f as.toArray)) : ExArgOK S cfg f ∧ ∀ a ∈ as, ExArgOK S cfg a := by
  rw [mkAppN_toArray] at h
  exact foldl_pred (Q := ExArgOK S cfg)
    (fun _ _ h => ⟨⟨h.1.1, h.2.1.1, h.2.2.1⟩, ⟨h.1.2, h.2.1.2, h.2.2.2⟩⟩) h

/-- The existence of the marking at `visitExpr fuel` on a term `e`: run on `e` renamed by `ρ`,
under traversal locals that `ρ` relates to the marking's locals `ls` on the scope `S` of `e`
(`RenOK`), from a state whose registered masks keep every field (`MasksOK`), on a term that is
`NatPlain` and has no string literal, a successful run has a marking of `e` under `ls`.
Reference: none (DV-32). -/
def ExistsSpec (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat)
    (e : Expr) : Prop :=
  ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃st : ErasureState⦄
    ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
    CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ExArgOK S cfg e →
    MasksOK (evalEnvOf view cfg decls) st →
    (visitExpr (m := PureM) fuel (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
    ∃ ê, MarkOf decls cfg ls e ê

/-- Markings of the terms of a list, pointwise, as the rules of `MarkOf` take them. Reference:
none. -/
abbrev MarkList (decls : List ConstantInfo) (cfg : ErasureConfig) (ls : List Local)
    (as âs : List Expr) : Prop :=
  as.length = âs.length ∧ ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â

/-- Markings of a head and of a tail mark the list. -/
theorem MarkList.cons {decls : List ConstantInfo} {cfg : ErasureConfig} {ls : List Local}
    {a â : Expr} {as âs : List Expr} (h : MarkOf decls cfg ls a â) (hs : MarkList decls cfg ls as âs) :
    MarkList decls cfg ls (a :: as) (â :: âs) := by
  refine ⟨by simp [hs.1], fun i b b' h1 h2 => ?_⟩
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1 h2; exact h
  | succ i => exact hs.2 i b b' (by simpa using h1) (by simpa using h2)

/-! ## The oracle's split and the plain nodes -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The oracle call that starts each unfolding of `visitExpr`: an answer `true` is the `erase`
mark; an answer `false` on the renamed term is `false` on the term (`oracle_agree`), and the
branch `K` ran. -/
theorem exists_split (hcl : ClosedDecls decls = true) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {tc : TravCtx} {st st' : ErasureState} {ps ps' : PureState} {r : LBTerm}
    {e : Expr} {K : EraseT PureM LBTerm} (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e)
    (h : (read >>= fun c₁ => read >>= fun c₂ =>
        (liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals (renFV ρ e)) : EraseT PureM Bool) >>=
          fun b => if b = true then Pure.pure LBTerm.box else K).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps'))
    (hK : oracle decls ls e = .ok false → K.runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
      ∃ ê, MarkOf decls cfg ls e ê) :
    ∃ ê, MarkOf decls cfg ls e ê := by
  rcases oracle_run h with ⟨hor, -⟩ | ⟨hor, hK'⟩
  · exact ⟨_, .erase (oracle_agree hcl hR he hor)⟩
  · exact hK (oracle_agree hcl hR he hor) hK'

/-- The `fvar` step: a free variable is marked by `MarkOf.fvar` or erased. -/
theorem exists_fvar_step (hcl : ClosedDecls decls = true) {fuel : Nat} {x : FVarId} :
    ExistsSpec view cfg decls (fuel + 1) (.fvar x) := by
  intro ρ S ls st tc ps r st' ps' _ hR he _ hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  exact exists_split (e := .fvar x) hcl hR he.1 hrun fun hor _ => ⟨_, .fvar hor⟩

/-- The steps on the terms `visitExpr` rejects after the oracle (a bound variable, a sort, a Π, a
metavariable): only the oracle's `□` returns, which is the `erase` mark. -/
theorem exists_fail_step (hcl : ClosedDecls decls = true) {fuel : Nat} {e : Expr}
    (hk : (e.isBVar || e.isSort || e.isForall || e.isMVar) = true) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  intro ρ S ls st tc ps r st' ps' _ hR he _ hrun
  cases e <;> simp [Expr.isBVar, Expr.isSort, Expr.isForall, Expr.isMVar] at hk <;>
  · simp only [renFV] at hrun
    rw [visitExpr] at hrun
    exact exists_split hcl hR he.1 hrun fun _ h => nomatch h

/-- The `mdata` step, from `ExistsSpec` at `fuel` (`MarkOf.mdata`). -/
theorem exists_mdata_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ e, ExistsSpec view cfg decls fuel e) {m : MData} {e : Expr} :
    ExistsSpec view cfg decls (fuel + 1) (.mdata m e) := by
  intro ρ S ls st tc ps r st' ps' hctx hR he hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  refine exists_split (e := .mdata m e) hcl hR he.1 hrun fun hor hrun => ?_
  obtain ⟨ê, hê⟩ := ih e hctx hR he hm hrun
  exact ⟨_, .mdata hor hê⟩

/-- The `lam` step, from `ExistsSpec` at the fuels up to `fuel`: the marking opens the body with
a fresh variable (`exists_fresh`), renamed to the traversal's next variable (`RenOK.push`)
(`MarkOf.lam`). -/
theorem exists_lam_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {n : Name} {A b : Expr}
    {bi : BinderInfo} :
    ExistsSpec view cfg decls (fuel + 1) (.lam n A b bi) := by
  intro ρ S ls st tc ps r st' ps' hctx hR he hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  refine exists_split (e := .lam n A b bi) hcl hR he.1 hrun fun hor hrun => ?_
  cases fuel with
  | zero => rw [visitLambda] at hrun; cases hrun
  | succ k =>
  rw [visitLambda] at hrun
  simp only [lambdaMonocular, withLocalDecl] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hbody, -⟩ := ok_of_bind hrun
  obtain ⟨x, hx⟩ := exists_fresh ls [b]
  have hR' := hR.push (n := n) (val := none) hx he.1.1 (fun _ h => nomatch h)
  have hxb : FVarsIn (· ≠ x) b := hx.2 b (List.mem_singleton_self b)
  have hren : renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) =
      (renFV ρ b).instantiate1' (.fvar (pureFVar ps.next)) := by
    rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun y hy => renExt_ne hy) hxb]
    simp only [renFV, renExt_self]
  rw [show Backend.instantiate1 (m := PureM) (renFV ρ b) (.fvar (pureFVar ps.next)) =
    renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) from hren.symm] at hbody
  obtain ⟨bM, hbM⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩) hR'
    ⟨fvarsIn_open he.1.2, NatPlain.inst_fvar he.2.1.2, NoStrLit.inst_fvar he.2.2.2⟩ hm hbody
  exact ⟨_, .lam hor hx hbM⟩

/-- The `letE` step, from `ExistsSpec` at the fuels up to `fuel`: the value and the body under the
`let`'s local, opened with a fresh variable renamed to the traversal's next variable; the body's
run starts at a counter no smaller than the value's (`travMonoAt`) (`MarkOf.letE`). -/
theorem exists_letE_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {n : Name} {T v b : Expr} {nd : Bool} :
    ExistsSpec view cfg decls (fuel + 1) (.letE n T v b nd) := by
  intro ρ S ls st tc ps r st' ps' hctx hR he hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  refine exists_split (e := .letE n T v b nd) hcl hR he.1 hrun fun hor hrun => ?_
  cases fuel with
  | zero => rw [visitLet] at hrun; cases hrun
  | succ k =>
  rw [visitLet] at hrun
  simp only [letMonocular, withLocalDef] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨tv, st₁⟩, ps₁⟩, hval, hrun⟩ := ok_of_bind hrun
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨tb, st₂⟩, ps₂⟩, hbody, -⟩ := ok_of_bind hrun
  obtain ⟨x, hx⟩ := exists_fresh ls [v, b]
  have hR' := hR.push (n := n) (val := some v) hx he.1.1 (fun w h => by cases h; exact he.1.2.1)
  have hxS := hR.not_mem hx
  have hagree : ∀ y, S y → renExt ρ x (pureFVar ps.next) y = ρ y := fun y hy =>
    renExt_ne fun e => hxS (e ▸ hy)
  have hxb : FVarsIn (· ≠ x) b := hx.2 b (by simp)
  have hrenb : renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) =
      (renFV ρ b).instantiate1' (.fvar (pureFVar ps.next)) := by
    rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun y hy => renExt_ne hy) hxb]
    simp only [renFV, renExt_self]
  rw [show visitExpr (m := PureM) k (renFV ρ v) =
    visitExpr k (renFV (renExt ρ x (pureFVar ps.next)) v) by
      rw [renFV_congr hagree he.1.2.1]] at hval
  rw [show Backend.instantiate1 (m := PureM) (renFV ρ b) (.fvar (pureFVar ps.next)) =
    renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) from hrenb.symm] at hbody
  obtain ⟨vM, hvM⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩) hR'
    ⟨fvarsIn_mono (fun _ => .inl) he.1.2.1, he.2.1.2.1, he.2.2.2.1⟩ hm hval
  have ⟨hn₁, hm₁⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl k).expr _ _ _ _ _ _ _ hval
  obtain ⟨bM, hbM⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩)
    (hR'.mono hn₁) ⟨fvarsIn_open he.1.2.2, NatPlain.inst_fvar he.2.1.2.2,
      NoStrLit.inst_fvar he.2.2.2.2⟩ (hm₁ hm) hbody
  exact ⟨_, .letE hor hx hvM hbM⟩

/-- The `proj` step, from `ExistsSpec` at the fuels up to `fuel`: the structure is an inductive
of the closure (`getConst`), its registration keeps the counter and the masks, and the major
premise is visited (`MarkOf.proj`). -/
theorem exists_proj_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {s : Name} {i : Nat} {e : Expr} :
    ExistsSpec view cfg decls (fuel + 1) (.proj s i e) := by
  intro ρ S ls st tc ps r st' ps' hctx hR he hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  refine exists_split (e := .proj s i e) hcl hR he.1 hrun fun hor hrun => ?_
  cases fuel with
  | zero => rw [visitProj] at hrun; cases hrun
  | succ k =>
  rw [visitProj, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfc, rfl, rfl⟩ := getConst_run hci
  cases ci with
  | inductInfo iv =>
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rr, st₂⟩, ps₂⟩, hreg, hrun⟩ := ok_of_bind hrun
    have ⟨hn₂, hm₂⟩ := TravMono.register_inductive (σ := evalEnvOf view cfg decls) rfl iv _ _ _ _
      _ _ hreg
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨mask, st₃⟩, ps₃⟩, hmask, hrun⟩ := ok_of_bind hrun
    obtain ⟨-, rfl, rfl⟩ := getOrFail_run hmask
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨te, st₄⟩, ps₄⟩, hte, -⟩ := ok_of_bind hrun
    obtain ⟨ê, hê⟩ := ih k (Nat.le_succ _) e hctx (hR.mono hn₂) he (hm₂ hm) hte
    exact ⟨_, .proj hor hfc hê⟩
  | _ => dsimp only at hrun; cases hrun

/-- The oracle's answer on a Nat literal does not depend on the literal: its type is `Nat`. -/
theorem oracle_lit (ls : List Local) (n m : Nat) :
    oracle decls ls (.lit (.natVal n)) = oracle decls ls (.lit (.natVal m)) := by
  show Pure.isErasable _ (2 ^ 20 - 1 + 1) _ _ = Pure.isErasable _ (2 ^ 20 - 1 + 1) _ _
  simp only [Pure.isErasable, spine, Pure.inferType]

/-- Under `nat := .peano`, a literal up to `peanoMaxLiteral` whose literals the oracle keeps is
marked by itself (`MarkOf.litZero`, `MarkOf.litSucc`). -/
theorem markOf_lit (hnat : cfg.nat = .peano) {ls : List Local}
    (hor : ∀ j, oracle decls ls (.lit (.natVal j)) = .ok false) :
    ∀ n, n ≤ peanoMaxLiteral → MarkOf decls cfg ls (.lit (.natVal n)) (.lit (.natVal n))
  | 0, _ => .litZero (hor 0) hnat
  | k + 1, h => .litSucc (hor (k + 1)) hnat h (markOf_lit hnat hor k (by omega))

/-- The `lit` step: a Nat literal under `nat := .peano` (`NatPlain`) that `visitLiteral` accepts
is at most `peanoMaxLiteral`, and the oracle keeps every literal if it keeps one (`oracle_lit`);
a string literal is excluded (`NoStrLit`). -/
theorem exists_lit_step (hcl : ClosedDecls decls = true) {fuel : Nat} {l : Literal} :
    ExistsSpec view cfg decls (fuel + 1) (.lit l) := by
  intro ρ S ls st tc ps r st' ps' hctx hR he hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  refine exists_split (e := .lit l) hcl hR he.1 hrun fun hor hrun => ?_
  cases l with
  | strVal => exact he.2.2.elim
  | natVal n =>
  have hpeano : cfg.nat = .peano := he.2.1
  cases fuel with
  | zero => rw [visitLiteral] at hrun; cases hrun
  | succ f =>
  rw [visitLiteral, runPure_read_bind, hctx.config, hpeano] at hrun
  dsimp only at hrun
  by_cases hn : n > peanoMaxLiteral
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hn), runPure_read_bind] at hrun
    cases hrun
  · exact ⟨_, markOf_lit hpeano (fun j => (oracle_lit ls j n).trans hor) n (by omega)⟩

/-! ## Application spines -/

/-- Every term is a spine: a head that is no application applied to arguments, of which there is
at least one if the term is an application. -/
theorem exists_spine (e : Expr) : ∃ F as, e = mkAppN F as.toArray ∧ F.isApp = false ∧
    (e.isApp = true → as ≠ []) := by
  induction e with
  | app f a ihf _ =>
    obtain ⟨F, as, rfl, hF, -⟩ := ihf
    exact ⟨F, as ++ [a], (mkAppN_snoc F as a).symm, hF, fun _ => by simp⟩
  | _ => exact ⟨_, [], by rw [mkAppN_toArray]; rfl, rfl, nofun⟩

/-- A term headed by a constant is a spine of the constant. -/
theorem spine_of_getAppFn {e : Expr} {c : Name} {us : List Level} (h : e.getAppFn = .const c us) :
    ∃ as : List Expr, e = mkAppN (.const c us) as.toArray := by
  obtain ⟨F, as, rfl, hF, -⟩ := exists_spine e
  rw [getAppFn_mkAppN_of hF] at h
  exact ⟨as, by rw [h]⟩

/-- The first unfolding of `visitExpr` on a spine that is an application or a constant: the
oracle, then `visitApp`. -/
theorem appLike_run {fuel : Nat} {F : Expr} {as : List Expr}
    (hsh : as ≠ [] ∨ ∃ c us, F = .const c us) {ρ : FVarId → FVarId} {tc : TravCtx}
    {st st' : ErasureState} {ps ps' : PureState} {r : LBTerm} {pc : PureCtx}
    (h : (visitExpr (m := PureM) (fuel + 1) (renFV ρ (mkAppN F as.toArray))).runPure st tc pc ps =
      .ok ((r, st'), ps')) :
    (read >>= fun c₁ => read >>= fun c₂ =>
        (liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals (renFV ρ (mkAppN F as.toArray))) :
          EraseT PureM Bool) >>= fun b => if b = true then Pure.pure LBTerm.box else
            visitApp fuel (renFV ρ (mkAppN F as.toArray))).runPure st tc pc ps = .ok ((r, st'), ps') := by
  rcases eq_nil_or_snoc as with rfl | ⟨as', a, rfl⟩
  · obtain ⟨c, us, rfl⟩ := hsh.resolve_left (fun h => h rfl)
    simp only [mkAppN_toArray, List.foldl_nil, renFV] at h ⊢
    rw [visitExpr] at h
    exact h
  · rw [mkAppN_snoc] at h ⊢
    simp only [renFV] at h ⊢
    rw [visitExpr] at h
    exact h

/-- `ExistsSpec` on a spine that is an application or a constant, from what `visitApp` does after
the oracle keeps the spine. -/
theorem exists_appLike (hcl : ClosedDecls decls = true) {fuel : Nat} {F : Expr} {as : List Expr}
    (hsh : as ≠ [] ∨ ∃ c us, F = .const c us)
    (h : ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃st : ErasureState⦄
      ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ExArgOK S cfg (mkAppN F as.toArray) →
      MasksOK (evalEnvOf view cfg decls) st → oracle decls ls (mkAppN F as.toArray) = .ok false →
      (visitApp (m := PureM) fuel (renFV ρ (mkAppN F as.toArray))).runPure st tc ⟨decls, view⟩ ps =
        .ok ((r, st'), ps') →
      ∃ ê, MarkOf decls cfg ls (mkAppN F as.toArray) ê) :
    ExistsSpec view cfg decls (fuel + 1) (mkAppN F as.toArray) :=
  fun _ _ _ _ _ _ _ _ _ hctx hR he hm hrun =>
    exists_split hcl hR he.1 (appLike_run hsh hrun) (h hctx hR he hm)

/-- `visitAppArgs (j + 1) tf args` on renamed arguments, from `ExistsSpec` at `j`: every argument
is visited, each from a counter no smaller than the one before (`travMonoAt`), so each has a
marking. -/
theorem visitAppArgs_exists {j : Nat} (ih : ∀ e, ExistsSpec view cfg decls j e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {tc : TravCtx}
    (hctx : CtxOK cfg tc) {as : List Expr} {tf r : LBTerm} {st st' : ErasureState}
    {ps ps' : PureState} (hR : RenOK ρ S ls tc.locals ps.next) (hargs : ∀ a ∈ as, ExArgOK S cfg a)
    (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf (as.map (renFV ρ)).toArray).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    ∃ âs, MarkList decls cfg ls as âs := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction as generalizing tf st ps with
  | nil => exact ⟨[], rfl, fun _ _ _ h => nomatch h⟩
  | cons a l ihl =>
    rw [List.map_cons, List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := ok_of_bind hx
    cases hx
    obtain ⟨â, hâ⟩ := ih a hctx hR (hargs a (.head _)) hm ha
    have ⟨hn, hm'⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _ ha
    obtain ⟨âl, hl⟩ := ihl (hR.mono hn) (fun b hb => hargs b (.tail _ hb)) (hm' hm) hrun
    exact ⟨â :: âl, MarkList.cons hâ hl⟩

/-- `visitAppArgs i (visitConst i c) args` on renamed arguments, from `ExistsSpec` below `i`: the
constant's run keeps the invariants (`travMonoAt`), then the arguments (`visitAppArgs_exists`). -/
theorem constArgs_exists {i : Nat} (ih : ∀ m < i, ∀ e, ExistsSpec view cfg decls m e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {tc : TravCtx}
    (hctx : CtxOK cfg tc) {c : Name} {us : List Level} {as : List Expr} {r : LBTerm}
    {st st' : ErasureState} {ps ps' : PureState} (hR : RenOK ρ S ls tc.locals ps.next)
    (hargs : ∀ a ∈ as, ExArgOK S cfg a) (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hrun : (visitConst (m := PureM) i (.const c us) >>= fun tf =>
      visitAppArgs i tf (as.map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps =
        .ok ((r, st'), ps')) :
    ∃ âs, MarkList decls cfg ls as âs := by
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := ok_of_bind hrun
  have ⟨hn, hm₁⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl i).const _ _ _ _ _ _ _ hf
  cases i with
  | zero => rw [visitAppArgs] at hrun; cases hrun
  | succ i => exact visitAppArgs_exists (ih i (by omega)) hctx (hR.mono hn) hargs (hm₁ hm) hrun

/-- `visitApp` on a spine of a constant without a rule of its own (`markArity? = none`), from
`ExistsSpec` at the fuels below: `visitConstApp` takes its last branch, or `visitRec` its
`recStaysConstant` branch, and visits the arguments after the constant (`constArgs_exists`). -/
theorem constApp_exists {fuel : Nat} (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {tc : TravCtx}
    (hctx : CtxOK cfg tc) {c : Name} {us : List Level} {as : List Expr} {r : LBTerm}
    {st st' : ErasureState} {ps ps' : PureState} (hR : RenOK ρ S ls tc.locals ps.next)
    (hargs : ∀ a ∈ as, ExArgOK S cfg a) (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hma : markArity? decls cfg c = none)
    (hrun : (visitApp (m := PureM) fuel (renFV ρ (mkAppN (.const c us) as.toArray))).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    ∃ âs, MarkList decls cfg ls as âs := by
  obtain ⟨hcs, hca, hcq, hcr⟩ := markArity?_none hma
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) = mkAppN (.const c us) (as.map (renFV ρ)).toArray
    from renFV_mkAppN ρ _ as] at hrun
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [visitApp] at hrun
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
        .ok ((findConst decls c, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  split at hrun
  · rename_i q _ _ _ heq
    cases hcq _ heq
  · rename_i q _ _ _ heq
    cases hcq _ heq
  · rename_i rv heq
    cases j with
    | zero => rw [visitRec] at hrun; cases hrun
    | succ i =>
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
    obtain ⟨⟨⟨cvs, st₂⟩, ps₂⟩, hcvs0, hr2⟩ := ok_of_bind hr1
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
    have hblk : recBlockOf? decls rv = some (ivs, cvs) := by
      unfold recBlockOf?
      erw [hivs]
      simp only [Option.bind_eq_bind, Option.bind_some]
      erw [hcvs]
      rfl
    rw [runPure_read_bind, hctx.config, hcr rv heq ivs cvs hblk] at hr2
    simp only [↓reduceIte] at hr2
    rw [withApp_mkAppN rfl] at hr2
    exact constArgs_exists (fun m hm => ih m (by omega)) hctx hR hargs hm hr2
  · exact constArgs_exists (fun m hm => ih m (by omega)) hctx hR hargs hm hrun

/-- The step of an application or a constant whose head is no constant with a rule of its own:
the head is not a constant (`MarkOf.app`: the head, then the arguments) or a constant with
`markArity? = none` (`MarkOf.constApp`, `constApp_exists`). -/
theorem exists_app_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr}
    (hshape : e.isApp = true ∨ ∃ c us, e = .const c us)
    (hplain : ∀ c us, e.getAppFn = .const c us → markArity? decls cfg c = none) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  obtain ⟨F, as, rfl, hF, hne⟩ := exists_spine e
  by_cases hFc : ∃ c us, F = .const c us
  · obtain ⟨c, us, rfl⟩ := hFc
    have hma := hplain c us (getAppFn_mkAppN_const c us as)
    refine exists_appLike hcl (.inr ⟨c, us, rfl⟩) fun ρ S ls st tc ps r st' ps' hctx hR he hm hor
      hrun => ?_
    obtain ⟨âs, hlen, hall⟩ := constApp_exists ih hctx hR (exArg_spine he).2 hm hma hrun
    exact ⟨_, .constApp hor hma hlen hall⟩
  have hFc' : ∀ c us, F ≠ .const c us := fun c us h => hFc ⟨c, us, h⟩
  have has : as ≠ [] := by
    rcases hshape with h | ⟨c, us, h⟩
    · exact hne h
    · rintro rfl
      exact hFc' c us (by rw [mkAppN_toArray] at h; exact h)
  refine exists_appLike hcl (.inl has) fun ρ S ls st tc ps r st' ps' hctx hR he hm hor hrun => ?_
  obtain ⟨hfF, hA⟩ := exArg_spine he
  have hfa' : (renFV ρ F).isApp = false := by cases F <;> first | rfl | cases hF
  have hfc' : ∀ c us, renFV ρ F ≠ .const c us := by
    intro c us h
    cases F <;> simp only [renFV, reduceCtorEq] at h
    cases h
    exact hFc' _ _ rfl
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [renFV_mkAppN, visitApp] at hrun
  split at hrun
  · rename_i c us hc
    rw [getAppFn_mkAppN_of hfa'] at hc
    exact absurd hc (hfc' c us)
  rw [withApp_mkAppN hfa', runPure_bind] at hrun
  obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, htf, hrun⟩ := ok_of_bind hrun
  obtain ⟨fM, hfM⟩ := ih k (by omega) F hctx hR hfF hm htf
  have ⟨hn, hm₁⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl k).expr _ _ _ _ _ _ _ htf
  cases k with
  | zero => rw [visitAppArgs] at hrun; cases hrun
  | succ i =>
  obtain ⟨âs, hlen, hall⟩ := visitAppArgs_exists (ih i (by omega)) hctx (hR.mono hn) hA (hm₁ hm)
    hrun
  exact ⟨_, .app hor has hF hFc' hfM hlen hall⟩

end

/-! ## η-expansion -/

section
variable {pc : PureCtx}

/-- A successful run of `forallMonocular t k` at the pure backend read a leading `Π` of `t`
(`forallView?`). -/
theorem forallMonocular_inv {α : Type} {t : Expr} {k : FVarId → Expr → EraseT PureM α}
    {tc : TravCtx} {st st' : ErasureState} {ps ps' : PureState} {r : α}
    (h : (forallMonocular (m := PureM) t k).runPure st tc pc ps = .ok ((r, st'), ps')) :
    ∃ y D C bi, forallView? pc.decls tc.locals t = some (y, D, C, bi) := by
  unfold forallMonocular at h
  by_cases hf : t.isForall = true
  · cases t with
    | forallE y D C bi => exact ⟨y, D, C, bi, rfl⟩
    | _ => cases hf
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)] at h
    have hnf : ∀ y D C bi, t ≠ .forallE y D C bi := by rintro _ _ _ _ rfl; exact hf rfl
    rw [OracleRen.forallView?_of_not hnf]
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM] at h
    have hrun : ((Backend.whnf (m := PureM) tc.lctx tc.locals t).run pc).run ps =
        (Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals t).map (·, ps) := whnf_run _ _ _ _
    rw [hrun] at h
    cases hw : Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals t with
    | error => rw [hw] at h; cases h
    | ok w =>
      rw [hw] at h
      cases w with
      | forallE y D C bi => exact ⟨y, D, C, bi, rfl⟩
      | _ => cases h

end

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- What the continuation `kont` of `withAppEtaToMinArity` at the arity `ar` does on the head
`c.{us}` and at least `ar` renamed arguments, from the premises of `ExistsSpec` on the arguments:
a successful run has a marking `MarkSat` of the saturated spine. Reference: none (DV-23). -/
def ExSatSpec (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (ar : Nat)
    (c : Name) (us : List Level) (kont : Expr → Array Expr → EraseT PureM LBTerm) : Prop :=
  ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃st : ErasureState⦄
    ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄
    ⦃as : List Expr⦄,
    CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → (∀ a ∈ as, ExArgOK S cfg a) → ar ≤ as.length →
    MasksOK (evalEnvOf view cfg decls) st →
    (kont (.const c us) (as.map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps') →
    ∃ ê, MarkSat decls cfg ls c us as ê

/-- The η-expansion loop `withAppEtaToMinArity.go` at the arity `ar` on the renamed spine
`c.{us} as` and the renamed type `T`: each missing argument is the traversal's next variable at
the leading `Π` it reads, which is the renamed `Π` that `forallView?` reads on `T`
(`forallView?_ren`), and to which the marking's fresh variable is renamed (`MarkEta.intro`); at
the arity the continuation runs (`MarkEta.sat`, `ExSatSpec`). Reference: none (DV-23). -/
theorem etaGo_exists (hcl : ClosedDecls decls = true) {ar : Nat} {c : Name} {us : List Level}
    {kont : Expr → Array Expr → EraseT PureM LBTerm} (hk : ExSatSpec view cfg decls ar c us kont) :
    ∀ (fuel : Nat) {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local}
      {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {T : Expr}
      {as : List Expr},
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → (∀ a ∈ as, ExArgOK S cfg a) →
      FVarsIn S T → MasksOK (evalEnvOf view cfg decls) st →
      (withAppEtaToMinArity.go (m := PureM) ar kont fuel (renFV ρ T) (.const c us)
        (as.map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
      ∃ ê, MarkEta decls cfg ls ar T c us as ê := by
  intro fuel
  induction fuel with
  | zero =>
    intro ρ S ls st st' tc ps ps' r T as _ _ _ _ _ hrun
    rw [withAppEtaToMinArity.go] at hrun; cases hrun
  | succ fuel ihf =>
    intro ρ S ls st st' tc ps ps' r T as hctx hR hargs hT hm hrun
    rw [withAppEtaToMinArity.go] at hrun
    by_cases hge : (as.map (renFV ρ)).toArray.size ≥ ar
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hge)] at hrun
      have hle : ar ≤ as.length := by simpa using hge
      obtain ⟨ê, hê⟩ := hk hctx hR hargs hle hm hrun
      exact ⟨_, .sat hle hê⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hge)] at hrun
    have hlt : as.length < ar := by simp at hge; omega
    obtain ⟨y, D', C', bi, hv'⟩ := forallMonocular_inv hrun
    rw [(forallView?_ren hcl hR.supp hR.ren T hT).1] at hv'
    obtain ⟨⟨y₀, D, C, bi₀⟩, hv, hveq⟩ := Option.map_eq_some_iff.1 hv'
    cases hveq
    have hv'' : forallView? decls tc.locals (renFV ρ T) = some (y₀, renFV ρ D, renFV ρ C, bi₀) := by
      rw [(forallView?_ren hcl hR.supp hR.ren T hT).1, hv]; rfl
    rw [forallMonocular_run _ hv'', runPure_bind] at hrun
    obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hgo, -⟩ := ok_of_bind hrun
    have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
    obtain ⟨x, hfr⟩ := exists_fresh ls (T :: as)
    have hR' := hR.push (n := y₀) (val := none) hfr hD (fun _ h => nomatch h)
    have hxS := hR.not_mem hfr
    have hagree : ∀ z, S z → renExt ρ x (pureFVar ps.next) z = ρ z := fun z hz =>
      renExt_ne fun e => hxS (e ▸ hz)
    have hxC : FVarsIn (· ≠ x) C := fvarsIn_mono (fun z hz (e : z = x) => hxS (e ▸ hz)) hC
    have hrenC : renFV (renExt ρ x (pureFVar ps.next)) (C.instantiate1' (.fvar x)) =
        (renFV ρ C).instantiate1' (.fvar (pureFVar ps.next)) := by
      rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxC]
      simp only [renFV, renExt_self]
    have hmap : (as ++ [Expr.fvar x]).map (renFV (renExt ρ x (pureFVar ps.next))) =
        as.map (renFV ρ) ++ [.fvar (pureFVar ps.next)] := by
      simp only [List.map_append, List.map_cons, List.map_nil, renFV, renExt_self]
      exact congrArg (· ++ _) (List.map_congr_left fun a ha => renFV_congr hagree (hargs a ha).1)
    rw [List.push_toArray, ← hmap, ← hrenC] at hgo
    have hargs' : ∀ a ∈ as ++ [Expr.fvar x], ExArgOK (fun z => S z ∨ z = x) cfg a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨h1, h2, h3⟩ := hargs a ha
        exact ⟨fvarsIn_mono (fun _ => .inl) h1, h2, h3⟩
      · rw [List.mem_singleton] at ha
        subst ha
        exact ⟨Or.inr rfl, trivial, trivial⟩
    obtain ⟨ê, hê⟩ := ihf (by exact ⟨hctx.config, hctx.fixvars⟩) (by exact hR') hargs'
      (fvarsIn_open hC) hm hgo
    exact ⟨_, .intro hlt hv hfr hê⟩

/-- `withAppEtaToMinArity f e ar kont` at the pure backend on the renamed spine of `c.{us} as`:
the oracle types the spine (its type on the renamed spine is the renamed type,
`inferType_ren`), and the loop gives `MarkEta` on that type (`etaGo_exists`), given what `kont`
does on a saturated spine (`ExSatSpec`). Reference: none (DV-23). -/
theorem withAppEta_exists (hcl : ClosedDecls decls = true) {ar f : Nat} {c : Name}
    {us : List Level} {kont : Expr → Array Expr → EraseT PureM LBTerm}
    (hk : ExSatSpec view cfg decls ar c us kont) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {as : List Expr} (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next)
    (hargs : ∀ a ∈ as, ExArgOK S cfg a) (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hrun : (withAppEtaToMinArity (m := PureM) f (mkAppN (.const c us) (as.map (renFV ρ)).toArray)
      ar kont).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    ∃ T ê, Pure.inferType ⟨decls⟩ oracleFuel ls [] (mkAppN (.const c us) as.toArray) = .ok T ∧
      MarkEta decls cfg ls ar T c us as ê := by
  have he : FVarsIn S (mkAppN (.const c us) as.toArray) :=
    fvarsIn_mkAppN.2 ⟨trivial, fun a ha => (hargs a ha).1⟩
  have hT' := (inferType_ren (cx := ⟨decls⟩) hcl hR.supp hR.ren oracleFuel [] _ he (by simp)).1
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) =
    mkAppN (.const c us) (as.map (renFV ρ)).toArray from renFV_mkAppN ρ _ as] at hT'
  rw [withAppEtaToMinArity, runPure_read_bind, runPure_read_bind, runPure_bind,
    inferType_runPure] at hrun
  erw [hT'] at hrun
  cases hT : Pure.inferType ⟨decls⟩ oracleFuel ls [] (mkAppN (.const c us) as.toArray) with
  | error err => rw [hT] at hrun; cases hrun
  | ok T =>
    rw [hT] at hrun
    dsimp only [Except.map] at hrun
    rw [ok_bind'] at hrun
    dsimp only at hrun
    rw [withApp_mkAppN rfl] at hrun
    obtain ⟨ê, hê⟩ :=
      etaGo_exists hcl hk f hctx hR hargs (fvarsIn_oracle_ty hcl hR.supp he hT) hm hrun
    exact ⟨T, ê, rfl, hê⟩

end

/-! ## Constructor and quotient spines -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `visitConstructor (j + 1) c args` on a constructor `c` with at least its arity of renamed
arguments, from `ExistsSpec` at the fuels up to `j`: the constructor sits at its index in its
inductive's constructors (`CtorsListed`), the masks registered for the inductive keep every field
(`register_inductive_masks`, `MasksOK`), so the mask at the index keeps every field and every
argument is visited (`slices_keep`, `visitAppArgs_exists`); so is every argument of a constructor
emitted as an axiom. Machine integers are excluded (`hnat`). -/
theorem visitConstructor_exists (hct : CtorsListed decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExistsSpec view cfg decls m e) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {cv : ConstructorVal} {as : List Expr} (hctx : CtxOK cfg tc)
    (hR : RenOK ρ S ls tc.locals ps.next) (hargs : ∀ a ∈ as, ExArgOK S cfg a)
    (hm : MasksOK (evalEnvOf view cfg decls) st) (hc : findDecl decls c = some (.ctorInfo cv))
    (har : cv.numParams + cv.numFields ≤ as.length)
    (hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ)
    (hrun : (visitConstructor (m := PureM) (j + 1) c (as.map (renFV ρ)).toArray).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    ∃ âs, MarkList decls cfg ls as âs := by
  rw [visitConstructor, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfc, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  rw [show findConst decls c = findDecl decls c from rfl, hc] at hfc
  cases hfc
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfi, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  cases ci with
  | inductInfo iv =>
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rr, st₁⟩, ps₁⟩, hreg, hrun⟩ := ok_of_bind hrun
    obtain ⟨hm₁, hin⟩ := register_inductive_masks (σ := evalEnvOf view cfg decls) rfl iv tc st ps rr
      st₁ ps₁ hm hreg
    have hps := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
    subst ps₁
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨mask, st₂⟩, ps₂⟩, hmask, hrun⟩ := ok_of_bind hrun
    obtain ⟨hmk, h1, h2⟩ := getOrFail_run hmask
    subst st₂ ps₂
    have hiv : findDecl decls cv.induct = some (.inductInfo iv) := hfi
    obtain ⟨iv', hiv', hpos, -⟩ := hct c cv hc
    rw [hiv] at hiv'
    cases hiv'
    obtain ⟨iv₂, hiv₂, hkm⟩ := hm₁ iv.name rr hin
    have hiv₃ : findDecl decls iv.name = some (.inductInfo iv₂) := hiv₂
    have hname : iv.name = cv.induct := (findDecl_eq_some hiv).2
    rw [hname, hiv] at hiv₃
    cases hiv₃
    have hmask' : mask = Array.replicate cv.numFields .keep := by
      have := hkm.2 cv.cidx _ cv hpos hc
      rw [hmk] at this
      cases this; rfl
    dsimp only at hrun
    rw [runPure_bind, isExtern_runPure, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_read_bind] at hrun
    split at hrun
    · cases j with
      | zero => rw [visitAppArgs] at hrun; cases hrun
      | succ i => exact visitAppArgs_exists (ih i (by omega)) hctx hR hargs hm₁ hrun
    rw [runPure_read_bind, hctx.config] at hrun
    split at hrun
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).1
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).2
    all_goals
      rw [hmask', slices_keep (as.map (renFV ρ)) cv.numParams cv.numFields (by simpa using har)]
        at hrun
      cases j with
      | zero => rw [visitAppArgs] at hrun; cases hrun
      | succ i => exact visitAppArgs_exists (ih i (by omega)) hctx hR hargs hm₁ hrun
  | _ => dsimp only at hrun; cases hrun

/-- The constructor step: a spine whose head is a constructor and no recognized `casesOn`, from
`ExistsSpec` at the fuels up to `fuel`: `visitConstApp` takes its constructor branch, the
η-expansion gives `MarkEta` (`withAppEta_exists`) and `visitConstructor` visits every argument
of the saturated spine (`visitConstructor_exists`, `MarkSat.ctor`), so the spine is marked by
`MarkOf.special`. Reference: none (DV-23). -/
theorem exists_ctor_step (hcl : ClosedDecls decls = true) (hct : CtorsListed decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr} {c : Name} {us : List Level}
    {n : Nat} (hfn : e.getAppFn = .const c us) (hcs : casesInfo? decls c = none)
    (hca : ctorArity? decls c = some n) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  obtain ⟨as, rfl⟩ := spine_of_getAppFn hfn
  obtain ⟨cv, hc, rfl⟩ : ∃ cv, findDecl decls c = some (.ctorInfo cv) ∧
      n = cv.numParams + cv.numFields := by
    unfold ctorArity? at hca
    split at hca
    · rename_i cv hcv
      cases hca
      exact ⟨cv, hcv, rfl⟩
    · cases hca
  have hma : markArity? decls cfg c = some (cv.numParams + cv.numFields) := by
    simp [markArity?, hcs, hca]
  refine exists_appLike hcl (.inr ⟨c, us, rfl⟩) fun ρ S ls st tc ps r st' ps' hctx hR he hm hor
    hrun => ?_
  obtain ⟨⟨-, hnc, -⟩, hA⟩ := exArg_spine he
  have hnc' : cfg.nat = .machine → c ∉ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc,
      ``Nat.casesOn, ``Int.casesOn] := hnc
  have hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ := fun h =>
    ⟨fun e => hnc' h (by rw [e]; simp), fun e => hnc' h (by rw [e]; simp)⟩
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) = mkAppN (.const c us) (as.map (renFV ρ)).toArray
    from renFV_mkAppN ρ _ as] at hrun
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [visitApp] at hrun
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
      EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps =
        .ok ((some (cv.numParams + cv.numFields), st), ps) by
    show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
  dsimp only at hrun
  obtain ⟨T, ê, hT, hη⟩ := withAppEta_exists hcl (fun ρ₁ S₁ ls₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁ hctx₁
      hR₁ hargs₁ hle₁ hm₁ hrun₁ => by
    cases j with
    | zero => rw [visitConstructor] at hrun₁; cases hrun₁
    | succ i =>
    obtain ⟨âs, hlen, hall⟩ := visitConstructor_exists hct (fun m hm => ih m (by omega)) hctx₁ hR₁
      hargs₁ hm₁ hc hle₁ hnat hrun₁
    exact ⟨_, .ctor hcs hca hlen hall⟩) hctx hR hA hm hrun
  exact ⟨_, .special hor hma hT hη⟩

/-- The quotient step: a spine whose head is `Quot.mk` or `Quot.lift` (a quotient constant with
an evaluation arity), from `ExistsSpec` at the fuels up to `fuel`: `visitConstApp` takes its
quotient branch, the η-expansion gives `MarkEta` (`withAppEta_exists`), and the saturated spine
visits the element (`Quot.mk α r a`), resp. the function and the quotient
(`Quot.lift α r β f h q`), and the arguments beyond the arity (`MarkSat.quotMk`,
`MarkSat.quotLift`), so the spine is marked by `MarkOf.special`. Reference: none (DV-29). -/
theorem exists_quot_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr} {c : Name} {us : List Level}
    {qv : QuotVal} (hfn : e.getAppFn = .const c us) (hqv : findDecl decls c = some (.quotInfo qv))
    (hqs : (quotEvalArity qv.kind).isSome) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  obtain ⟨as, rfl⟩ := spine_of_getAppFn hfn
  obtain ⟨hcs, hca⟩ := quot_heads hqv
  obtain ⟨ar, har⟩ := Option.isSome_iff_exists.1 hqs
  have hma : markArity? decls cfg c = some ar := by
    unfold markArity?
    rw [hcs, hca]
    dsimp only
    rw [hqv]
    exact har
  refine exists_appLike hcl (.inr ⟨c, us, rfl⟩) fun ρ S ls st tc ps r st' ps' hctx hR he hm hor
    hrun => ?_
  obtain ⟨-, hA⟩ := exArg_spine he
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) = mkAppN (.const c us) (as.map (renFV ρ)).toArray
    from renFV_mkAppN ρ _ as] at hrun
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [visitApp] at hrun
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
        .ok ((some (.quotInfo qv), st), ps) by
    show Except.ok ((findConst decls c, st), ps) = _
    rw [show findConst decls c = findDecl decls c from rfl, hqv], ok_bind'] at hrun
  dsimp only at hrun
  obtain ⟨cval, kind⟩ := qv
  cases kind with
  | type => simp [quotEvalArity] at hqs
  | ind => simp [quotEvalArity] at hqs
  | ctor =>
    obtain rfl : ar = 3 := (Option.some.inj har).symm
    obtain ⟨T, ê, hT, hη⟩ := withAppEta_exists hcl (fun ρ₁ S₁ ls₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁
        hctx₁ hR₁ hargs₁ hle₁ hm₁ hrun₁ => by
      obtain ⟨α, rr, a, extra, rfl⟩ : ∃ α rr a extra, as₁ = α :: rr :: a :: extra := by
        match as₁, hle₁ with
        | α :: rr :: a :: extra, _ => exact ⟨α, rr, a, extra, rfl⟩
      rw [runPure_bind] at hrun₁
      obtain ⟨⟨⟨a₁, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
      obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
      simp only [List.map_cons, List.getElem?_toArray, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      rw [runPure_bind] at hrun₁
      obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun₁⟩ := ok_of_bind hrun₁
      obtain ⟨â, hâ⟩ := ih j (by omega) a hctx₁ hR₁ (hargs₁ a (by simp)) hm₁ hf
      have ⟨hn, hm₂⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _ hf
      rw [show (List.toArray ((α :: rr :: a :: extra).map (renFV ρ₁))).extract 3 =
        (extra.map (renFV ρ₁)).toArray by simp [List.take_of_length_le]] at hrun₁
      cases j with
      | zero => rw [visitAppArgs] at hrun₁; cases hrun₁
      | succ i =>
      obtain ⟨êxtra, hlen, hall⟩ := visitAppArgs_exists (ih i (by omega)) hctx₁ (hR₁.mono hn)
        (fun b hb => hargs₁ b (by simp [hb])) (hm₂ hm₁) hrun₁
      exact ⟨_, .quotMk (α := α) (r := rr) hcs hca hqv rfl hâ hlen hall⟩) hctx hR hA hm hrun
    exact ⟨_, .special hor hma hT hη⟩
  | lift =>
    obtain rfl : ar = 6 := (Option.some.inj har).symm
    obtain ⟨T, ê, hT, hη⟩ := withAppEta_exists hcl (fun ρ₁ S₁ ls₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁
        hctx₁ hR₁ hargs₁ hle₁ hm₁ hrun₁ => by
      obtain ⟨α, rr, β, f, h, q, extra, rfl⟩ :
          ∃ α rr β f h q extra, as₁ = α :: rr :: β :: f :: h :: q :: extra := by
        match as₁, hle₁ with
        | α :: rr :: β :: f :: h :: q :: extra, _ => exact ⟨α, rr, β, f, h, q, extra, rfl⟩
      rw [runPure_bind] at hrun₁
      obtain ⟨⟨⟨f₁, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
      obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
      simp only [List.map_cons, List.getElem?_toArray, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      rw [runPure_bind] at hrun₁
      obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun₁⟩ := ok_of_bind hrun₁
      obtain ⟨fM, hfM⟩ := ih j (by omega) f hctx₁ hR₁ (hargs₁ f (by simp)) hm₁ hf
      have ⟨hn, hm₂⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _ hf
      rw [show (List.toArray ((α :: rr :: β :: f :: h :: q :: extra).map (renFV ρ₁))).extract 5 =
        ((q :: extra).map (renFV ρ₁)).toArray by simp [List.take_of_length_le]] at hrun₁
      cases j with
      | zero => rw [visitAppArgs] at hrun₁; cases hrun₁
      | succ i =>
      obtain ⟨âs, hlen, hall⟩ := visitAppArgs_exists (ih i (by omega)) hctx₁ (hR₁.mono hn)
        (fun b hb => hargs₁ b (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ hb)))))) (hm₂ hm₁) hrun₁
      obtain ⟨qM, êxtra, rfl⟩ : ∃ qM êxtra, âs = qM :: êxtra := by
        rcases âs with _ | ⟨qM, êxtra⟩
        · simp at hlen
        · exact ⟨_, _, rfl⟩
      exact ⟨_, .quotLift (α := α) (r := rr) (β := β) (h := h) hcs hca hqv rfl hfM
        (hall 0 q qM rfl rfl) (by simpa using hlen)
        (fun i x xM h1 h2 => hall (i + 1) x xM h1 h2)⟩) hctx hR hA hm hrun
    exact ⟨_, .special hor hma hT hη⟩

end

end Steps

end EraseProof
