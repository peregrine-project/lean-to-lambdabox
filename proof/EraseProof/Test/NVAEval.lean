import EraseProof.Test.NVARun
import EraseProof.Test.NVLFinal
import EraseProof.Test.NVSFinal

/-!
# NV-A: the source evaluation

`hev`: the term `e = Nat.add 2 3` of NV-A (`Test/NVAData.lean`) evaluates to
`Nat.succ (Nat.succ (Nat.succ 2))`, the literal `2` under three constructors. The numerals
evaluate to their literals: `OfNat.ofNat` (δ, β) projects the field of `instOfNatNat k`, the
constructor value `OfNat.mk Nat k k` (`ev_numK`). `Nat.add 2 3` unfolds (δ, β) to
`Nat.brecOn (fun y => Nat → Nat) 3 Nat.add._f 2`; `Nat.brecOn` and `Nat.brecOn.go` unfold to the
recursor `Nat.rec` into the pairs `PProd (motive t) (Nat.below motive t)` on the literal `3`, whose
ι reads the literal as `Nat.succ` applied to `2` (`natLitCtor`), with the induction hypothesis its
ι on `2`, down to `0`, read as `Nat.zero` (`ev_rec`). The table `T k` it computes holds, first, the
function `G k` (`Nat.add._f` on `k`, a λ over the first argument), then the table on the
predecessor; `Nat.below` on a literal evaluates to the types of the tables (`ev_below`). Applied to
`2`, `G k` matches with `Nat.add.match_1` (δ, β, then `SrcEval.casesIota` on the constructor value
`Nat.zero` or `Nat.succ k'`): on `Nat.zero` the first alternative returns `2`; on `Nat.succ k'` the
second applies `Nat.succ` to the recursive call, the first projection of the table on `k'` applied
to `2` (`ev_call`). The value is `V 3`, `V k` the literal `2` under `k` constructors `Nat.succ`.
-/

open Lean Erasure

namespace EraseProof.Test.NVA

open EraseProof.Test.NVL (tN cZ cS Nat_ind Zero_ctor Succ_ctor Nat_rec motTy recShape_N
  minorsN minors_shape)
open EraseProof.Test.NVS (uu u1 l1 m1u tPU cPU tPP cPP PUnit_ind PUnit_unit PUnit_rec PProd_ind
  PProd_mk PProd_rec ml PPl PPmkl)

/-- The evaluation environment. -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

/-! ## Closed terms -/

/-- Every loose bound variable of a term is below `s`. -/
def Below : Nat → Expr → Prop
  | s, .bvar i => i < s
  | s, .app f a => Below s f ∧ Below s a
  | s, .lam _ t b _ => Below s t ∧ Below (s + 1) b
  | s, .forallE _ t b _ => Below s t ∧ Below (s + 1) b
  | s, .letE _ t v b _ => Below s t ∧ Below s v ∧ Below (s + 1) b
  | s, .mdata _ e => Below s e
  | s, .proj _ _ e => Below s e
  | _, _ => True

/-- Instantiation above the loose bound variables of a term leaves it unchanged. -/
theorem inst_below (a : Expr) : ∀ {e : Expr} {s d : Nat}, Below s e → s ≤ d →
    e.instantiate1' a d = e
  | .bvar i, s, d, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', show i < d by omega, ↓reduceIte]
  | .app f x, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h.1 hd, inst_below a h.2 hd]
  | .lam _ t b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h.1 hd, inst_below a h.2 (Nat.succ_le_succ hd)]
  | .forallE _ t b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h.1 hd, inst_below a h.2 (Nat.succ_le_succ hd)]
  | .letE _ t v b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h.1 hd, inst_below a h.2.1 hd,
      inst_below a h.2.2 (Nat.succ_le_succ hd)]
  | .mdata _ e, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h hd]
  | .proj _ _ e, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.instantiate1', inst_below a h hd]
  | .const .., _, _, _, _ | .sort _, _, _, _, _ | .fvar _, _, _, _, _ | .mvar _, _, _, _, _
  | .lit _, _, _, _, _ => rfl

/-- Lifting above the loose bound variables of a term leaves it unchanged. -/
theorem lift_below (d : Nat) : ∀ {e : Expr} {s s' : Nat}, Below s e → s ≤ s' →
    e.liftLooseBVars' s' d = e
  | .bvar i, s, s', h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', show i < s' by omega, ↓reduceIte]
  | .app f x, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h.1 hd, lift_below d h.2 hd]
  | .lam _ t b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h.1 hd, lift_below d h.2 (Nat.succ_le_succ hd)]
  | .forallE _ t b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h.1 hd, lift_below d h.2 (Nat.succ_le_succ hd)]
  | .letE _ t v b _, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h.1 hd, lift_below d h.2.1 hd,
      lift_below d h.2.2 (Nat.succ_le_succ hd)]
  | .mdata _ e, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h hd]
  | .proj _ _ e, _, _, h, hd => by
    simp only [Below] at h
    simp only [Expr.liftLooseBVars', lift_below d h hd]
  | .const .., _, _, _, _ | .sort _, _, _, _, _ | .fvar _, _, _, _, _ | .mvar _, _, _, _, _
  | .lit _, _, _, _, _ => rfl

/-! ## The values -/

/-- `Nat.below.{1} (fun y => Nat → Nat) k`'s value: `PUnit` on `0`, `PProd (Nat → Nat) (BL k)` on
`k + 1`. -/
def BL : Nat → Expr
  | 0 => tPU ml
  | k + 1 => PPl nn (BL k)

/-- `Nat.add.match_1.{1} a b c d e f` -/
def m6 (a b c d e f : Expr) : Expr :=
  .app (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) a) b) c) d) e) f

/-- `G y tbl`, the value of `Nat.add._f y tbl`: a λ over the first argument. -/
def Gb (y tbl : Expr) : Expr := .lam x13 tN (m6 motF (.bvar 0) y h1F h2F tbl) .default

/-- The table of `Nat.brecOn.go (fun y => Nat → Nat) k Nat.add._f`: the pair of `Nat.add._f k` and
the table on the predecessor. -/
def T : Nat → Expr
  | 0 => PPmkl nn (tPU ml) (Gb cZ (cPU ml)) (cPU ml)
  | k + 1 => PPmkl nn (PPl nn (BL k)) (Gb (.app cS (lit k)) (T k)) (T k)

/-- The first field of the table `T k`. -/
def G : Nat → Expr
  | 0 => Gb cZ (cPU ml)
  | k + 1 => Gb (.app cS (lit k)) (T k)

/-- The value of `G k` applied to `2`: `2` under `k` constructors `Nat.succ`. -/
def V : Nat → Expr
  | 0 => lit 2
  | k + 1 => .app cS (V k)

/-- `Below` is monotone. -/
theorem below_mono : ∀ {e : Expr} {s s' : Nat}, Below s e → s ≤ s' → Below s' e
  | .bvar _, _, _, h, hs => by simp only [Below] at h ⊢; omega
  | .app _ _, _, _, h, hs => ⟨below_mono h.1 hs, below_mono h.2 hs⟩
  | .lam _ _ _ _, _, _, h, hs => ⟨below_mono h.1 hs, below_mono h.2 (Nat.succ_le_succ hs)⟩
  | .forallE _ _ _ _, _, _, h, hs => ⟨below_mono h.1 hs, below_mono h.2 (Nat.succ_le_succ hs)⟩
  | .letE _ _ _ _ _, _, _, h, hs =>
    ⟨below_mono h.1 hs, below_mono h.2.1 hs, below_mono h.2.2 (Nat.succ_le_succ hs)⟩
  | .mdata _ e, _, _, h, hs => below_mono (e := e) h hs
  | .proj _ _ e, _, _, h, hs => below_mono (e := e) h hs
  | .const .., _, _, _, _ | .sort _, _, _, _, _ | .fvar _, _, _, _, _ | .mvar _, _, _, _, _
  | .lit _, _, _, _, _ => trivial

/-- Unfold `Below` on the concrete parts of the values. -/
macro "belowsimp" : tactic => `(tactic| simp [Below, motF, belowA, below, motA, nn, tN, cZ, cS,
  h1F, h2F, lit, tPU, cPU, tPP, cPP, PPl, PPmkl, mkAppN, Array.foldl, List.foldl])

theorem below_BL : ∀ k, Below 0 (BL k)
  | 0 => by simp [BL, Below, tPU]
  | k + 1 => by simp only [BL]; exact ⟨by belowsimp, below_BL k⟩

theorem below_Gb {y tbl : Expr} (hy : Below 0 y) (ht : Below 0 tbl) : Below 0 (Gb y tbl) := by
  have hy1 := below_mono hy (Nat.zero_le 1)
  have ht1 := below_mono ht (Nat.zero_le 1)
  simp only [Gb, m6]
  exact ⟨trivial, ⟨⟨⟨⟨⟨⟨trivial, by belowsimp⟩, by simp [Below]⟩, hy1⟩, by belowsimp⟩, by belowsimp⟩,
    ht1⟩⟩

theorem below_T : ∀ k, Below 0 (T k)
  | 0 => by
    simp only [T]
    exact ⟨⟨⟨⟨trivial, by belowsimp⟩, by belowsimp⟩, below_Gb (by belowsimp) (by belowsimp)⟩,
      by belowsimp⟩
  | k + 1 => by
    simp only [T]
    exact ⟨⟨⟨⟨trivial, by belowsimp⟩, ⟨by belowsimp, below_BL k⟩⟩,
      below_Gb (by belowsimp) (below_T k)⟩, below_T k⟩

/-- `T k` is closed: instantiation and lifting leave it unchanged. -/
theorem inst_T (k : Nat) (a : Expr) (d : Nat) : (T k).instantiate1' a d = T k :=
  inst_below a (below_T k) (Nat.zero_le d)

theorem lift_T (k : Nat) (s d : Nat) : (T k).liftLooseBVars' s d = T k :=
  lift_below d (below_T k) (Nat.zero_le s)

/-! ## Steps -/

theorem ns_lam {f a : Expr} {n : Name} {A b : Expr} {bi : BinderInfo}
    (h : f.getAppFn = .lam n A b bi) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem ns_proj {f a : Expr} {S : Name} {i : Nat} {x : Expr} (h : f.getAppFn = .proj S i x) :
    ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem ns_const {f a : Expr} {c : Name} {us : List Level} (h : f.getAppFn = .const c us)
    (hc : specialArity σ c = none) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2

/-- A spine with more arguments than its arity is not short. -/
theorem ns_over {f a : Expr} {c : Name} {us : List Level} {ar : Nat}
    (h : f.getAppFn = .const c us) (hc : specialArity σ c = some ar) (hn : ar ≤ f.getAppNumArgs) :
    ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c', us', ar', h1, h2, h3⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2
  rw [SrcDefeq.getAppNumArgs_app] at h3
  omega

theorem ev_atom {e : Expr} (h : SrcAtom e) : SrcEval σ e e := .atom h

theorem ev_delta {c : Name} {us : List Level} {v : DefinitionVal} {r : Expr}
    (h : σ.unfold? c = some (.defnInfo v, v.value))
    (hr : SrcEval σ (Pure.instLevels v.levelParams us v.value) r) : SrcEval σ (.const c us) r :=
  .delta h hr

theorem ev_tN : SrcEval σ tN tN := .constAtom (by krfl)
theorem ev_lit (k : Nat) : SrcEval σ (lit k) (lit k) := .lit
theorem ev_tPU : SrcEval σ (tPU ml) (tPU ml) := .constAtom (by krfl)

theorem ev_cZ : SrcEval σ cZ cZ :=
  SrcEval.ctor (c := `Nat.zero) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)

theorem ev_cPU : SrcEval σ (cPU ml) (cPU ml) :=
  SrcEval.ctor (c := `PUnit.unit) (us := [ml]) (as := []) (vs := []) rfl rfl rfl
    (fun _ _ _ h => nomatch h)

/-- `Nat.succ a ⇓ Nat.succ v` when `a ⇓ v`. -/
theorem ev_succ {a v : Expr} (h : SrcEval σ a v) : SrcEval σ (.app cS a) (.app cS v) := by
  refine SrcEval.ctor (c := `Nat.succ) (us := []) (as := [a]) (vs := [v]) rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | i <;> simp at h1 h2
  subst h1 h2
  exact h

/-- `PProd.mk.{1, max 1 1} A B a b ⇓ PProd.mk.{1, max 1 1} A' B' a' b'`. -/
theorem ev_mk {A B a b A' B' a' b' : Expr} (hA : SrcEval σ A A') (hB : SrcEval σ B B')
    (ha : SrcEval σ a a') (hb : SrcEval σ b b') : SrcEval σ (PPmkl A B a b) (PPmkl A' B' a' b') := by
  refine SrcEval.ctor (c := `PProd.mk) (us := [l1, ml]) (as := [A, B, a, b]) (vs := [A', B', a', b'])
    rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact hA
  · exact hB
  · exact ha
  · exact hb

theorem findDecl_PProd : findDecl σ.decls `PProd = some (.inductInfo PProd_ind) := by krfl
theorem casesOn_PProd : σ.casesOn? `PProd = none := by krfl
theorem arity_PProd : specialArity σ `PProd = none := by krfl

theorem nb_PP : ¬ BlocksCong σ (tPP l1 ml) := by
  rintro (⟨c, us, cv, h1, h2⟩ | ⟨c, us, iv, h1, h2⟩ | ⟨c, us, qv, h1, h2⟩) <;> cases h1 <;>
    simp [findDecl_PProd, casesOn_PProd] at h2

theorem nb_PP1 {A : Expr} : ¬ BlocksCong σ (.app (tPP l1 ml) A) := by
  rintro (⟨c, us, cv, h1, h2⟩ | ⟨c, us, iv, h1, h2⟩ | ⟨c, us, qv, h1, h2⟩) <;> cases h1 <;>
    simp [findDecl_PProd, casesOn_PProd] at h2

/-- `PProd.{1, max 1 1} A B ⇓ PProd A' B'` (`appCong` on a type former). -/
theorem ev_PP {A B A' B' : Expr} (hA : SrcEval σ A A') (hB : SrcEval σ B B') :
    SrcEval σ (PPl A B) (PPl A' B') :=
  .appCong (ns_const (c := `PProd) (us := [l1, ml]) rfl arity_PProd)
    (.appCong (ns_const (c := `PProd) (us := [l1, ml]) rfl arity_PProd) (.constAtom (by krfl)) nb_PP
      hA) nb_PP1 hB

/-- `(fun y => Nat → Nat) a ⇓ Nat → Nat`. -/
theorem ev_motA {a a' : Expr} (ha : SrcEval σ a a') : SrcEval σ (.app motA a) nn :=
  .beta (ns_lam rfl) (ev_atom trivial) ha (ev_atom trivial)

/-! ## The numerals -/

/-- `OfNat.mk.{0} Nat k k`, the value of `instOfNatNat k`. -/
def mkOf (k : Nat) : Expr := .app (.app (.app (cOf .zero) tN) (lit k)) (lit k)

theorem ev_mkOf (k : Nat) : SrcEval σ (mkOf k) (mkOf k) := by
  refine SrcEval.ctor (c := `OfNat.mk) (us := [.zero]) (as := [tN, lit k, lit k])
    (vs := [tN, lit k, lit k]) rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_tN
  · exact ev_lit k
  · exact ev_lit k

theorem ev_instK (k : Nat) : SrcEval σ (instK k) (mkOf k) :=
  .beta (ns_const rfl (by krfl)) (ev_delta (v := inst_def) (by krfl) (ev_atom trivial)) (ev_lit k)
    (ev_mkOf k)

/-- The numeral `k` evaluates to the literal `k`: `OfNat.ofNat` projects the field of the instance. -/
theorem ev_numK (k : Nat) : SrcEval σ (numK k) (lit k) := by
  have h0 := ev_delta (c := `OfNat.ofNat) (us := [.zero]) (v := ofNat_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl (by krfl)) h0 (SrcEval.mdata (d := borrowed) ev_tN) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl (by krfl)) h1 (ev_lit k) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl (by krfl)) h2 (ev_instK k)
    (SrcEval.proj (ev_mkOf k) ⟨`OfNat.mk, [.zero], OfNat_mk, [tN, lit k], rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fs := [lit k]) rfl)


/-! ## Instantiation of the closed parts -/

theorem inst_motA (a : Expr) (d : Nat) : motA.instantiate1' a d = motA :=
  inst_below a (by belowsimp) (Nat.zero_le d)
theorem inst_motF (a : Expr) (d : Nat) : motF.instantiate1' a d = motF :=
  inst_below a (by belowsimp) (Nat.zero_le d)
theorem inst_h1F (a : Expr) (d : Nat) : h1F.instantiate1' a d = h1F :=
  inst_below a (by belowsimp) (Nat.zero_le d)
theorem inst_h2F (a : Expr) (d : Nat) : h2F.instantiate1' a d = h2F :=
  inst_below a (by belowsimp) (Nat.zero_le d)
theorem inst_fVal (a : Expr) (d : Nat) : fVal.instantiate1' a d = fVal :=
  inst_below a (by simp [Below, fVal, motF, belowA, below, motA, nn, tN, cZ, cS, h1F, h2F, x13, x14])
    (Nat.zero_le d)

/-- Push an instantiation through the values' constructors. -/
macro "instsimp" : tactic => `(tactic| simp +decide only [Expr.instantiate1', inst_motA,
      inst_motF, inst_h1F, inst_h2F, inst_fVal, inst_T, liftLooseBVars'_zero, lift_T, tN, cZ, cS,
      lit, tPU, cPU, tPP, cPP, PPl, PPmkl, belowA, below, m6, Nat.zero_add, Nat.reduceAdd,
      Nat.lt_irrefl, Nat.zero_lt_one, ↓reduceIte, Nat.not_lt_zero, Nat.lt_succ_self])

/-! ## `Nat.below` on a literal -/

/-- The minor premise of `Nat.succ` in `Nat.below.{1} (fun y => Nat → Nat)`'s recursor. -/
def blMin : Expr :=
  .lam `n tN (.lam `n_ih (.sort ml) (PPl (.app motA (.bvar 1)) (.bvar 0)) .default) .default

/-- `Nat.below.{1} (fun y => Nat → Nat) a` after δ and β: the recursor into `Sort (max 1 1)`. -/
def blRec (a : Expr) : Expr :=
  mkAppN (.const `Nat.rec [.succ ml]) #[.lam `t tN (.sort ml) .default, tPU ml, blMin, a]

theorem ev_BL : ∀ k, SrcEval σ (BL k) (BL k)
  | 0 => ev_tPU
  | k + 1 => ev_PP (ev_atom trivial) (ev_BL k)

theorem ev_recBlock : σ.recBlock? Nat_rec = some ([Nat_ind], [Zero_ctor, Succ_ctor]) := by krfl

theorem ev_blMins : ∀ (i : Nat) m mv, [tPU ml, blMin][i]? = some m →
    [tPU ml, blMin][i]? = some mv → SrcEval σ m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_tPU
  · exact ev_atom trivial

theorem ev_blRec : ∀ k, SrcEval σ (blRec (lit k)) (BL k)
  | 0 =>
    SrcEval.recIota (c := `Nat.rec) (us := [.succ ml]) (ps := []) (ms := [.lam `t tN (.sort ml) .default])
      (mins := [tPU ml, blMin]) (mvs := [tPU ml, blMin]) (fs := []) (rfs := []) (ihvs := [])
      (T := `Nat) (iv := Nat_ind) (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl ev_recBlock rfl
      recShape_N minors_shape rfl rfl rfl rfl ev_blMins (ev_lit 0)
      ⟨`Nat.zero, [], Zero_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      (fun _ _ _ h => nomatch h) ev_tPU
  | k + 1 => by
    refine SrcEval.recIota (c := `Nat.rec) (us := [.succ ml]) (ps := [])
      (ms := [.lam `t tN (.sort ml) .default]) (mins := [tPU ml, blMin]) (mvs := [tPU ml, blMin])
      (fs := [lit k]) (rfs := [lit k]) (ihvs := [BL k]) (T := `Nat) (iv := Nat_ind)
      (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl ev_recBlock rfl recShape_N minors_shape rfl rfl rfl
      rfl ev_blMins (ev_lit (k + 1)) ⟨`Nat.succ, [], Succ_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      rfl rfl rfl
      (fun i f w h1 h2 => by
        rcases i with _ | i <;> simp at h1 h2
        subst h1 h2
        exact ev_blRec k) ?_
    have h1 : SrcEval σ (.app blMin (lit k))
        (.lam `n_ih (.sort ml) (PPl (.app motA (lit k)) (.bvar 0)) .default) :=
      .beta (ns_lam rfl) (ev_atom trivial) (ev_lit k) (ev_atom trivial)
    refine SrcEval.beta (ns_lam rfl) h1 (ev_BL k) ?_
    have : (PPl (.app motA (lit k)) (.bvar 0)).instantiate1' (BL k) = PPl (.app motA (lit k)) (BL k) := by
      instsimp
    rw [this]
    exact ev_PP (ev_motA (ev_lit k)) (ev_BL k)

/-- `Nat.below.{1} (fun y => Nat → Nat) k ⇓ BL k`. -/
theorem ev_below (k : Nat) : SrcEval σ (belowA (lit k)) (BL k) := by
  have h0 := ev_delta (c := `Nat.below) (us := [l1]) (v := Nat_below) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl (by krfl)) h0 (ev_atom (e := motA) trivial) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl (by krfl)) h1 (ev_lit k) (ev_blRec k)


/-! ## The tables -/

theorem ev_Gb {y tbl : Expr} : SrcEval σ (Gb y tbl) (Gb y tbl) := ev_atom trivial

theorem ev_T : ∀ k, SrcEval σ (T k) (T k)
  | 0 => ev_mk (ev_atom trivial) ev_tPU ev_Gb ev_cPU
  | k + 1 => ev_mk (ev_atom trivial) (ev_PP (ev_atom trivial) (ev_BL k)) ev_Gb (ev_T k)

/-- `Nat.add._f`'s value applied to `y` and the table `tbl` evaluates to `Gb y tbl`. -/
theorem ev_fApp {y tbl : Expr} (hy : SrcEval σ y y) (ht : SrcEval σ tbl tbl) (hyb : Below 0 y)
    (htb : Below 0 tbl) : SrcEval σ (.app (.app fVal y) tbl) (Gb y tbl) := by
  have e1 : (Expr.lam `f (belowA (.bvar 0)) (.lam x13 tN
      (m6 motF (.bvar 0) (.bvar 2) h1F h2F (.bvar 1)) .default)
      .default).instantiate1' y = .lam `f (belowA y) (.lam x13 tN
      (m6 motF (.bvar 0) y h1F h2F (.bvar 1)) .default)
      .default := by
    instsimp
    rw [lift_below 2 hyb (Nat.le_refl 0)]
  have h1 : SrcEval σ (.app fVal y) (.lam `f (belowA y) (.lam x13 tN
      (m6 motF (.bvar 0) y h1F h2F (.bvar 1)) .default)
      .default) :=
    .beta (ns_lam rfl) (ev_atom trivial) hy ((congrArg (fun x => SrcEval σ x _) e1).mpr
      (ev_atom trivial))
  have e2 : (Expr.lam x13 tN (m6 motF (.bvar 0) y h1F h2F (.bvar 1)) .default).instantiate1' tbl = Gb y tbl := by
    simp only [Gb]
    instsimp
    rw [inst_below tbl (below_mono hyb (Nat.zero_le 1)) (Nat.le_refl 1),
      lift_below 1 htb (Nat.le_refl 0)]
  exact .beta (ns_lam rfl) h1 ht ((congrArg (fun x => SrcEval σ x _) e2).mpr ev_Gb)


/-! ## `Nat.brecOn.go` on a literal -/

/-- The motive and the minor premises of `Nat.brecOn.go`'s recursor at the motive
`fun y => Nat → Nat` and `F_1 := Nat.add._f`'s value. -/
def Mg : Expr := .lam `t tN (PPl (.app motA (.bvar 0)) (belowA (.bvar 0))) .default
def zMin : Expr := PPmkl (.app motA cZ) (tPU ml) (.app (.app fVal cZ) (cPU ml)) (cPU ml)
def sMinB (n ih : Expr) : Expr :=
  PPmkl (.app motA (.app cS n)) (PPl (.app motA n) (belowA n)) (.app (.app fVal (.app cS n)) ih) ih
def sMin : Expr :=
  .lam `n tN (.lam `n_ih (PPl (.app motA (.bvar 0)) (belowA (.bvar 0))) (sMinB (.bvar 1) (.bvar 0))
    .default) .default

/-- `Nat.rec.{max 1 1} Mg z sMin maj` -/
def recG (z maj : Expr) : Expr := .app (.app (.app (.app (.const `Nat.rec [ml]) Mg) z) sMin) maj

theorem ev_zMin : SrcEval σ zMin (T 0) :=
  ev_mk (ev_motA ev_cZ) ev_tPU (ev_fApp ev_cZ ev_cPU trivial trivial) ev_cPU

/-- The minor premise of `Nat.succ` on the field `k` and the table on `k`. -/
theorem ev_sMin (k : Nat) : SrcEval σ (.app (.app sMin (lit k)) (T k)) (T (k + 1)) := by
  have h1 : SrcEval σ (.app sMin (lit k))
      (.lam `n_ih (PPl (.app motA (lit k)) (belowA (lit k))) (sMinB (lit k) (.bvar 0)) .default) :=
    .beta (ns_lam rfl) (ev_atom trivial) (ev_lit k) (ev_atom trivial)
  have e2 : (sMinB (lit k) (.bvar 0)).instantiate1' (T k) = sMinB (lit k) (T k) := by
    simp only [sMinB]
    instsimp
  refine .beta (ns_lam rfl) h1 (ev_T k) ((congrArg (fun x => SrcEval σ x _) e2).mpr ?_)
  exact ev_mk (ev_motA (ev_succ (ev_lit k))) (ev_PP (ev_motA (ev_lit k)) (ev_below k))
    (ev_fApp (ev_succ (ev_lit k)) (ev_T k) ⟨trivial, trivial⟩ (below_T k)) (ev_T k)

theorem ev_minsG {z : Expr} (hz : SrcEval σ z (T 0)) : ∀ (i : Nat) m mv, [z, sMin][i]? = some m →
    [T 0, sMin][i]? = some mv → SrcEval σ m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact hz
  · exact ev_atom trivial

/-- The recursor's ι on `0` and on `k + 1`, the zero minor premise evaluating to `T 0`. -/
theorem ev_recG0 {z : Expr} (hz : SrcEval σ z (T 0)) : SrcEval σ (recG z (lit 0)) (T 0) :=
  SrcEval.recIota (c := `Nat.rec) (us := [ml]) (ps := []) (ms := [Mg]) (mins := [z, sMin])
    (mvs := [T 0, sMin]) (fs := []) (rfs := []) (ihvs := []) (T := `Nat) (iv := Nat_ind)
    (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl ev_recBlock rfl recShape_N minors_shape rfl rfl rfl rfl
    (ev_minsG hz) (ev_lit 0) ⟨`Nat.zero, [], Zero_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
    rfl (fun _ _ _ h => nomatch h) (ev_T 0)

theorem ev_recGS {z : Expr} (hz : SrcEval σ z (T 0)) {k : Nat}
    (ih : SrcEval σ (recG (T 0) (lit k)) (T k)) : SrcEval σ (recG z (lit (k + 1))) (T (k + 1)) :=
  SrcEval.recIota (c := `Nat.rec) (us := [ml]) (ps := []) (ms := [Mg]) (mins := [z, sMin])
    (mvs := [T 0, sMin]) (fs := [lit k]) (rfs := [lit k]) (ihvs := [T k]) (T := `Nat)
    (iv := Nat_ind) (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl ev_recBlock rfl recShape_N
    minors_shape rfl rfl rfl rfl (ev_minsG hz) (ev_lit (k + 1))
    ⟨`Nat.succ, [], Succ_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun i f w h1 h2 => by
      rcases i with _ | i <;> simp at h1 h2
      subst h1 h2
      exact ih)
    (ev_sMin k)

theorem ev_recG : ∀ k, SrcEval σ (recG (T 0) (lit k)) (T k)
  | 0 => ev_recG0 (ev_T 0)
  | k + 1 => ev_recGS (ev_T 0) (ev_recG k)

/-- `Nat.brecOn.go (fun y => Nat → Nat) 3 (Nat.add._f's value) ⇓ T 3`. -/
theorem ev_go : SrcEval σ (.app (.app (.app (.const `Nat.brecOn.go [l1]) motA) (lit 3)) fVal)
    (T 3) := by
  have hns : specialArity σ `Nat.brecOn.go = none := by krfl
  have h0 := ev_delta (c := `Nat.brecOn.go) (us := [l1]) (v := Nat_brecOn_go) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motA) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 (ev_lit 3) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 (ev_atom (e := fVal) trivial)
    (ev_recGS (k := 2) ev_zMin (ev_recG 2))

/-- `Nat.brecOn (fun y => Nat → Nat) 3 Nat.add._f ⇓ G 3`, the first field of the table. -/
theorem ev_brecOn : SrcEval σ (.app (.app (.app (.const `Nat.brecOn [l1]) motA) (lit 3))
    (.const `Nat.add._f [])) (G 3) := by
  have hns : specialArity σ `Nat.brecOn = none := by krfl
  have h0 := ev_delta (c := `Nat.brecOn) (us := [l1]) (v := Nat_brecOn) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motA) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 (ev_lit 3) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2
    (ev_delta (c := `Nat.add._f) (us := []) (v := add_f) (by krfl) (ev_atom trivial))
    (SrcEval.proj ev_go ⟨`PProd.mk, [l1, ml], PProd_mk, [nn, PPl nn (BL 2)], rfl, rfl, rfl, rfl, rfl,
      rfl⟩ (fs := [G 3, T 2]) rfl)


/-! ## The calls -/

/-- The second argument of the match in `G k`, and the table it receives. -/
def yv : Nat → Expr
  | 0 => cZ
  | k + 1 => .app cS (lit k)
def tv : Nat → Expr
  | 0 => cPU ml
  | k + 1 => T k

theorem G_eq (k : Nat) : G k = Gb (yv k) (tv k) := by cases k <;> rfl

theorem below_yv : ∀ k, Below 0 (yv k)
  | 0 => trivial
  | _ + 1 => ⟨trivial, trivial⟩
theorem below_tv : ∀ k, Below 0 (tv k)
  | 0 => trivial
  | k + 1 => below_T k

/-- `Nat.add.match_1.{1} motF 2 y h1F h2F` -/
def m5 (y : Expr) : Expr :=
  .app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motF) (lit 2)) y) h1F) h2F

/-- The arguments of `Nat.casesOn` in `m5 y` after δ and β. -/
def casesArgs (y : Expr) : List Expr :=
  [.lam `x tN (.app (.app motF (lit 2)) (.bvar 0)) .default, y, .app h1F (lit 2),
    .lam n58 tN (.app (.app h2F (lit 2)) (.bvar 0)) .default]

/-- δ and the five β of `Nat.add.match_1` on the arguments `motF 2 y h1F h2F`. -/
syntax (name := _matchBetaA) "add_match_beta" term : tactic
macro_rules
  | `(tactic| add_match_beta $hy:term) => `(tactic| (
  have hns : specialArity σ `Nat.add.match_1 = none := by krfl
  have h0 := ev_delta (c := `Nat.add.match_1) (us := [l1]) (v := match_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motF) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 (ev_lit 2) (ev_atom trivial)
  have h3 := SrcEval.beta (ns_const rfl hns) h2 $hy (ev_atom trivial)
  have h4 := SrcEval.beta (ns_const rfl hns) h3 (ev_atom (e := h1F) trivial) (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hns) h4 (ev_atom (e := h2F) trivial) ?_))

theorem casesOn_N : σ.casesOn? `Nat.casesOn = some Nat_ind := by krfl

/-- The match on `Nat.zero`: the first alternative, `fun x => 2`. -/
theorem ev_m5Z : SrcEval σ (m5 cZ) (.lam x61 (belowA cZ) (lit 2) .default) := by
  add_match_beta ev_cZ
  exact SrcEval.casesIota (c := `Nat.casesOn) (us := [l1]) (as := casesArgs cZ) (i := 0) (fs := [])
    casesOn_N rfl rfl ev_cZ ⟨`Nat.zero, [], Zero_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (.beta (ns_lam rfl) (ev_atom trivial) (ev_lit 2) (ev_atom trivial))

/-- The match on `Nat.succ k`: the second alternative, `fun x => Nat.succ (x.1 2)`. -/
theorem ev_m5S (k : Nat) : SrcEval σ (m5 (.app cS (lit k)))
    (.lam x61 (belowA (.app cS (lit k))) (.app cS (.app (.proj `PProd 0 (.bvar 0)) (lit 2)))
      .default) := by
  add_match_beta (ev_succ (ev_lit k))
  refine SrcEval.casesIota (c := `Nat.casesOn) (us := [l1]) (as := casesArgs (.app cS (lit k)))
    (i := 1) (fs := [lit k]) casesOn_N rfl rfl (ev_succ (ev_lit k))
    ⟨`Nat.succ, [], Succ_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_
  have h1 := SrcEval.beta (ns_lam rfl) (ev_atom (e := h2F) trivial) (ev_lit 2) (ev_atom trivial)
  exact .beta (ns_lam rfl) (ev_atom trivial) (ev_lit k)
    (.beta (ns_lam rfl) h1 (ev_lit k) (ev_atom trivial))

theorem ctorT (k : Nat) : CtorValue σ `PProd (T k) 0 [G k, tv k] := by
  cases k
  · exact ⟨`PProd.mk, [l1, ml], PProd_mk, [nn, tPU ml], rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨`PProd.mk, [l1, ml], PProd_mk, [nn, PPl nn (BL _)], rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The body of `G k` applied to `2` evaluates to `V k`. -/
theorem ev_callB : ∀ k, SrcEval σ ((m6 motF (.bvar 0) (yv k) h1F h2F (tv k)).instantiate1' (lit 2))
    (V k)
  | 0 => .beta (ns_const rfl (by krfl)) ev_m5Z ev_cPU (ev_lit 2)
  | k + 1 => by
    have e1 : (m6 motF (.bvar 0) (yv (k + 1)) h1F h2F (tv (k + 1))).instantiate1' (lit 2) =
        .app (m5 (.app cS (lit k))) (T k) := by
      simp only [m6, m5, yv, tv]
      instsimp
    have e2 : (Expr.app cS (.app (.proj `PProd 0 (.bvar 0)) (lit 2))).instantiate1' (T k) =
        .app cS (.app (.proj `PProd 0 (T k)) (lit 2)) := by
      instsimp
    rw [e1]
    refine .beta (ns_const rfl (by krfl)) (ev_m5S k) (ev_T k)
      ((congrArg (fun x => SrcEval σ x _) e2).mpr (ev_succ ?_))
    have hp : SrcEval σ (.proj `PProd 0 (T k)) (Gb (yv k) (tv k)) := by
      rw [← G_eq]
      exact SrcEval.proj (ev_T k) (ctorT k) (fs := [G k, tv k]) rfl
    exact .beta (ns_proj rfl) hp (ev_lit 2) (ev_callB k)

/-! ## `Nat.add 2 3` -/

/-- The value of `Nat.add 2 3`: the literal `2` under three constructors `Nat.succ`. -/
abbrev v5 : Expr := V 3

/-- `hev`: `e = Nat.add 2 3` evaluates to `Nat.succ (Nat.succ (Nat.succ 2))`. -/
theorem hev : SrcEval σ e v5 := by
  have hns : specialArity σ `Nat.add = none := by krfl
  have h0 := ev_delta (c := `Nat.add) (us := []) (v := add_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_numK 2) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h1 (ev_numK 3)
    (SrcEval.beta (ns_const rfl (by krfl)) ev_brecOn (ev_lit 2) (ev_callB 3))


end EraseProof.Test.NVA
