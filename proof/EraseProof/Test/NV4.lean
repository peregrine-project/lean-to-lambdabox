import EraseProof.Simulation
import EraseProof.Test.LBEval

/-!
# Non-vacuity instance NV-4 of `erases_correct`: a two-member unsafe block

The program of `tests/corpus/UnsafeRec.lean` behind `uaFalseOne` (every name in the namespace
`URec`; the λ-binders written `_` there are named here)

    universe u
    def CN : Type (u+1) := (α : Type u) → (α → α) → α → α
    def one : CN.{u} := fun α s z => s z
    def csucc (n : CN.{u}) : CN.{u} := fun α s z => s (n α s z)
    def CB : Type 2 := (α : Type 1) → α → α → α
    def btrue : CB := fun α t f => t
    def bfalse : CB := fun α t f => f
    mutual
    unsafe def ua (b : CB) (n : CN.{0}) : CN.{0} :=
      b (CN.{0} → CN.{0}) (fun m => m) (fun m => ub btrue (csucc m)) n
    unsafe def ub (b : CB) (n : CN.{0}) : CN.{0} :=
      b (CN.{0} → CN.{0}) (fun m => m) (fun m => ua btrue (csucc m)) n
    end
    #erase ua bfalse one.{0}

as the newest-first declaration list `decls4`, where the block `[ua, ub]` enters by
`ProgEnv.block` and so appears as `ub, ua` (the kernel's addition order), with its lean4lean model
`venv4`, and the erased term `e4` with its translation `e4'`. Every hypothesis of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`) is discharged by a checked term: `henv`, `hsub`,
`hinj`, `hlc`, `he`, `her`, `hdeps`, `hblocks`, `hev`, with the evaluation environment `σ4` of a
list view and the λ□ environment `lenv4` that `#erase` emits, in which `ua` and `ub` are the two
members of one λ□ fixpoint `fix defs4` and satisfy the two-member `ErasesBlock`. The source
evaluation takes `fixAtom` and `fixApp` on both members, δ on `bfalse` and `btrue`, δ at the level
`0` on `one.{0}` and `csucc.{0}`, and β; the λ□ evaluation takes `LBEval.fix` on both members.
`inst` applies the theorem; `concl` exhibits its conclusion with the witness
`v4' = λα. λs. λz. s (one' □ s z)`, where `one'` is `one`'s erased body, and `witness` shows, by
determinism of λ□ evaluation, that every witness of the theorem is this λ, not `□`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV4

/-! ## The source program -/

/-- The level parameter `u` of `CN`, `one` and `csucc`. -/
def lu : Level := .param `u

/-- `Type l`. -/
def tyE (l : Level) : Expr := .sort (.succ l)

/-- `α → α`, with `α` the loose index `0`. -/
def endoE : Expr := .forallE `a (.bvar 0) (.bvar 1) .default

/-- `α → α`, with `α` the loose index `1`. -/
def endo1E : Expr := .forallE `a (.bvar 1) (.bvar 2) .default

/-- `(α : Type l) → (α → α) → α → α`: the value of `CN.{l}`. -/
def cnE (l : Level) : Expr := .forallE `α (tyE l) (.forallE `a endoE endo1E .default) .default

/-- `CN.{l}`. -/
def cnC (l : Level) : Expr := .const `URec.CN [l]

/-- `fun α s z => s z` at the level `l`: the value of `one.{l}`. -/
def oneE (l : Level) : Expr :=
  .lam `α (tyE l) (.lam `s endoE (.lam `z (.bvar 1) (.app (.bvar 1) (.bvar 0)) .default) .default)
    .default

/-- `f α s a`, with `α`, `s` the loose indices `2`, `1`. -/
def spE (f a : Expr) : Expr := .app (.app (.app f (.bvar 2)) (.bvar 1)) a

/-- `fun α s z => s (f α s z)` at the level `l`, with `f` under the three binders. -/
def succBodyE (l : Level) (f : Expr) : Expr :=
  .lam `α (tyE l)
    (.lam `s endoE (.lam `z (.bvar 1) (.app (.bvar 1) (spE f (.bvar 0))) .default) .default)
    .default

/-- `fun n α s z => s (n α s z)` at the level `l`: the value of `csucc.{l}`. -/
def csuccE (l : Level) : Expr := .lam `n (cnC l) (succBodyE l (.bvar 3)) .default

/-- `Type 1`. -/
def ty1E : Expr := .sort (.succ (.succ .zero))

/-- `(α : Type 1) → α → α → α`: the value of `CB`. -/
def cbE : Expr :=
  .forallE `α ty1E (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.bvar 2) .default) .default)
    .default

/-- `CB`. -/
def cbC : Expr := .const `URec.CB []

/-- `fun α t f => t`: the value of `btrue`. -/
def btrueE : Expr :=
  .lam `α ty1E (.lam `t (.bvar 0) (.lam `f (.bvar 1) (.bvar 1) .default) .default) .default

/-- `fun α t f => f`: the value of `bfalse`. -/
def bfalseE : Expr :=
  .lam `α ty1E (.lam `t (.bvar 0) (.lam `f (.bvar 1) (.bvar 0) .default) .default) .default

/-- `CN.{0} → CN.{0}`. -/
def cnArrE : Expr := .forallE `a (cnC .zero) (cnC .zero) .default

/-- `fun m => m` on `CN.{0}`. -/
def idE : Expr := .lam `m (cnC .zero) (.bvar 0) .default

/-- `fun m => c btrue (csucc.{0} m)`: the branch of a member that calls the member `c`. -/
def callE (c : Name) : Expr :=
  .lam `m (cnC .zero)
    (.app (.app (.const c []) (.const `URec.btrue []))
      (.app (.const `URec.csucc [.zero]) (.bvar 0)))
    .default

/-- `b (CN.{0} → CN.{0}) (fun m => m) (fun m => c btrue (csucc m)) x`. -/
def appSelE (b x : Expr) (c : Name) : Expr := .app (.app (.app (.app b cnArrE) idE) (callE c)) x

/-- `b (CN.{0} → CN.{0}) (fun m => m) (fun m => c btrue (csucc m)) n`, with `b`, `n` the loose
indices `1`, `0`. -/
def selE (c : Name) : Expr := appSelE (.bvar 1) (.bvar 0) c

/-- `fun b n => b (CN.{0} → CN.{0}) (fun m => m) (fun m => c btrue (csucc m)) n`: the value of
the block member that calls the member `c`. -/
def memberE (c : Name) : Expr := .lam `b cbC (.lam `n (cnC .zero) (selE c) .default) .default

/-- `CB → CN.{0} → CN.{0}`: the type of `ua` and `ub`. -/
def memberTyE : Expr := .forallE `b cbC (.forallE `n (cnC .zero) (cnC .zero) .default) .default

/-- `def CN.{u} : Type (u+1) := (α : Type u) → (α → α) → α → α`. -/
def CN_val : DefinitionVal :=
  { name := `URec.CN, levelParams := [`u], type := .sort (.succ (.succ lu)), value := cnE lu,
    hints := .regular 1, safety := .safe, all := [`URec.CN] }

/-- `def one.{u} : CN.{u} := fun α s z => s z`. -/
def one_val : DefinitionVal :=
  { name := `URec.one, levelParams := [`u], type := cnC lu, value := oneE lu, hints := .regular 1,
    safety := .safe, all := [`URec.one] }

/-- `def csucc.{u} : CN.{u} → CN.{u} := fun n α s z => s (n α s z)`. -/
def csucc_val : DefinitionVal :=
  { name := `URec.csucc, levelParams := [`u], type := .forallE `n (cnC lu) (cnC lu) .default,
    value := csuccE lu, hints := .regular 2, safety := .safe, all := [`URec.csucc] }

/-- `def CB : Type 2 := (α : Type 1) → α → α → α`. -/
def CB_val : DefinitionVal :=
  { name := `URec.CB, levelParams := [], type := .sort (.succ (.succ (.succ .zero))),
    value := cbE, hints := .regular 1, safety := .safe, all := [`URec.CB] }

/-- `def btrue : CB := fun α t f => t`. -/
def btrue_val : DefinitionVal :=
  { name := `URec.btrue, levelParams := [], type := cbC, value := btrueE, hints := .regular 1,
    safety := .safe, all := [`URec.btrue] }

/-- `def bfalse : CB := fun α t f => f`. -/
def bfalse_val : DefinitionVal :=
  { name := `URec.bfalse, levelParams := [], type := cbC, value := bfalseE, hints := .regular 1,
    safety := .safe, all := [`URec.bfalse] }

/-- The first member of the block: `ua b n := b … (fun m => ub btrue (csucc m)) n`. -/
def ua_val : DefinitionVal :=
  { name := `URec.ua, levelParams := [], type := memberTyE, value := memberE `URec.ub,
    hints := .«opaque», safety := .«unsafe», all := [`URec.ua, `URec.ub] }

/-- The second member of the block: `ub b n := b … (fun m => ua btrue (csucc m)) n`. -/
def ub_val : DefinitionVal :=
  { name := `URec.ub, levelParams := [], type := memberTyE, value := memberE `URec.ua,
    hints := .«opaque», safety := .«unsafe», all := [`URec.ua, `URec.ub] }

/-- The program's declarations, newest first; the block's members in reversed `all` order. -/
def decls4 : List ConstantInfo :=
  [.defnInfo ub_val, .defnInfo ua_val, .defnInfo bfalse_val, .defnInfo btrue_val, .defnInfo CB_val,
    .defnInfo csucc_val, .defnInfo one_val, .defnInfo CN_val]

/-- The erased term `ua bfalse one.{0}`. -/
def e4 : Expr :=
  .app (.app (.const `URec.ua []) (.const `URec.bfalse [])) (.const `URec.one [.zero])

/-! ## Its model in lean4lean -/

/-- The image of the level parameter `u`. -/
def vu : VLevel := .param 0

/-- The level `2` (of `Type 1`). -/
def lv2 : VLevel := .succ (.succ .zero)

/-- The level `3` (of `Type 2`). -/
def lv3 : VLevel := .succ lv2

/-- The image of `Type l`. -/
def vty (l : VLevel) : VExpr := .sort (.succ l)

/-- The image of `α → α`, with `α` the loose index `0`. -/
def endoV : VExpr := .forallE (.bvar 0) (.bvar 1)

/-- The image of `α → α`, with `α` the loose index `1`. -/
def zV : VExpr := .forallE (.bvar 1) (.bvar 2)

/-- The image of `CN.{l}`'s value. -/
def cnV (l : VLevel) : VExpr := .forallE (vty l) (.forallE endoV zV)

/-- The image of `CN.{l}`. -/
def vcn (l : VLevel) : VExpr := .const `URec.CN [l]

/-- The image of `one.{l}`'s value. -/
def oneV (l : VLevel) : VExpr :=
  .lam (vty l) (.lam endoV (.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))))

/-- The image of `f α s a`. -/
def spV (f a : VExpr) : VExpr := .app (.app (.app f (.bvar 2)) (.bvar 1)) a

/-- The image of `csucc.{l}`'s value. -/
def csuccV (l : VLevel) : VExpr :=
  .lam (vcn l)
    (.lam (vty l) (.lam endoV (.lam (.bvar 1) (.app (.bvar 1) (spV (.bvar 3) (.bvar 0))))))

/-- The image of `Type 1`. -/
def ty2V : VExpr := .sort lv2

/-- The image of `CB`'s value. -/
def cbV : VExpr := .forallE ty2V (.forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2)))

/-- The image of `CB`. -/
def vcb : VExpr := .const `URec.CB []

/-- The image of `btrue`'s value. -/
def btrueV : VExpr := .lam ty2V (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 1)))

/-- The image of `bfalse`'s value. -/
def bfalseV : VExpr := .lam ty2V (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 0)))

/-- The image of `CN.{0}`. -/
def cn0 : VExpr := vcn .zero

/-- The image of `CN.{0} → CN.{0}`. -/
def cnArrV : VExpr := .forallE cn0 cn0

/-- The image of `fun m => m`. -/
def idV : VExpr := .lam cn0 (.bvar 0)

/-- The image of `fun m => c btrue (csucc.{0} m)`. -/
def callV (c : Name) : VExpr :=
  .lam cn0 (.app (.app (.const c []) (.const `URec.btrue []))
    (.app (.const `URec.csucc [.zero]) (.bvar 0)))

/-- The image of `b (CN.{0} → CN.{0}) (fun m => m) (fun m => c btrue (csucc m)) n`. -/
def selV (c : Name) : VExpr := .app (.app (.app (.app (.bvar 1) cnArrV) idV) (callV c)) (.bvar 0)

/-- The image of the value of the member that calls `c`. -/
def memberV (c : Name) : VExpr := .lam vcb (.lam cn0 (selV c))

/-- The image of `CB → CN.{0} → CN.{0}`. -/
def memberTyV : VExpr := .forallE vcb (.forallE cn0 cn0)

/-- The model of `CN`. -/
def CNdef : VDefVal :=
  { name := `URec.CN, uvars := 1, type := .sort (.succ (.succ vu)), value := cnV vu }

/-- The model of `one`. -/
def onedef : VDefVal := { name := `URec.one, uvars := 1, type := vcn vu, value := oneV vu }

/-- The model of `csucc`. -/
def csuccdef : VDefVal :=
  { name := `URec.csucc, uvars := 1, type := .forallE (vcn vu) (vcn vu), value := csuccV vu }

/-- The model of `CB`. -/
def CBdef : VDefVal := { name := `URec.CB, uvars := 0, type := .sort lv3, value := cbV }

/-- The model of `btrue`. -/
def btruedef : VDefVal := { name := `URec.btrue, uvars := 0, type := vcb, value := btrueV }

/-- The model of `bfalse`. -/
def bfalsedef : VDefVal := { name := `URec.bfalse, uvars := 0, type := vcb, value := bfalseV }

/-- The model of `ua`. -/
def uadef : VDefVal :=
  { name := `URec.ua, uvars := 0, type := memberTyV, value := memberV `URec.ub }

/-- The model of `ub`. -/
def ubdef : VDefVal :=
  { name := `URec.ub, uvars := 0, type := memberTyV, value := memberV `URec.ua }

/-- `env` with the constant `n` added (the result of `VEnv.addConst` when `n` is fresh). -/
def withConst (env : VEnv) (n : Name) (ci : VConstant) : VEnv :=
  { env with constants := fun m => if n = m then some ci else env.constants m }

/-- The model after adding `CN` with its defining equation. -/
def envCN : VEnv := (withConst .empty `URec.CN CNdef.toVConstant).addDefEq CNdef.toDefEq

/-- The model after adding `one` with its defining equation. -/
def envOne : VEnv := (withConst envCN `URec.one onedef.toVConstant).addDefEq onedef.toDefEq

/-- The model after adding `csucc` with its defining equation. -/
def envCsucc : VEnv :=
  (withConst envOne `URec.csucc csuccdef.toVConstant).addDefEq csuccdef.toDefEq

/-- The model after adding `CB` with its defining equation. -/
def envCB : VEnv := (withConst envCsucc `URec.CB CBdef.toVConstant).addDefEq CBdef.toDefEq

/-- The model after adding `btrue` with its defining equation. -/
def envBtrue : VEnv :=
  (withConst envCB `URec.btrue btruedef.toVConstant).addDefEq btruedef.toDefEq

/-- The model after adding `bfalse` with its defining equation. -/
def envBfalse : VEnv :=
  (withConst envBtrue `URec.bfalse bfalsedef.toVConstant).addDefEq bfalsedef.toDefEq

/-- The model after adding the block's constants `ua`, `ub`, without their defining equations. -/
def envBlk : VEnv :=
  withConst (withConst envBfalse `URec.ua uadef.toVConstant) `URec.ub ubdef.toVConstant

/-- The model of the program: `envBlk` with the block's defining equations. -/
def venv4 : VEnv := envBlk.addDefEqs [uadef, ubdef]

/-- The image of `e4`. -/
def e4' : VExpr :=
  .app (.app (.const `URec.ua []) (.const `URec.bfalse [])) (.const `URec.one [.zero])

/-! ## Typing in the model -/

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {l : VLevel}

/-- The image of `u` is a well-formed level of one parameter. -/
theorem vu_wf : vu.WF 1 := Nat.zero_lt_one

/-- `α → α : Sort (imax (l+1) (l+1))` under `α : Type l`. -/
theorem endoV_ty : env.HasType U (vty l :: Γ) endoV (.sort (.imax (.succ l) (.succ l))) :=
  .forallE (.bvar .zero) (.bvar (.succ .zero))

/-- `α → α : Sort (imax (l+1) (l+1))` under `s : α → α`, `α : Type l`. -/
theorem zV_ty : env.HasType U (endoV :: vty l :: Γ) zV (.sort (.imax (.succ l) (.succ l))) :=
  .forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))

/-- The sort of `CN.{l}`'s value is equivalent to `Type (l+1)`. -/
theorem cnV_level :
    VLevel.imax (.succ (.succ l)) (.imax (.imax (.succ l) (.succ l)) (.imax (.succ l) (.succ l))) ≈
      .succ (.succ l) := by
  refine VLevel.equiv_def.2 fun ls => ?_
  simp only [VLevel.eval, Lean.Nat.imax]
  simp

/-- `CN.{l}`'s value has type `Type (l+1)` in any model. -/
theorem cnV_ty (hl : l.WF U) : env.HasType U Γ (cnV l) (.sort (.succ (.succ l))) :=
  (VEnv.IsDefEq.sortDF
      (l := .imax (.succ (.succ l)) (.imax (.imax (.succ l) (.succ l)) (.imax (.succ l) (.succ l))))
      (l' := .succ (.succ l)) ⟨hl, ⟨hl, hl⟩, ⟨hl, hl⟩⟩ hl cnV_level).defeq
    (.forallE (.sort hl) (.forallE endoV_ty zV_ty))

/-- `CN.{l}` unfolds to its value in any model holding `CN`'s defining equation. -/
theorem cn_unfold (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.IsDefEq U Γ (vcn l) (cnV l) (.sort (.succ (.succ l))) :=
  .extra (ls := [l]) hd (by simpa using hl) rfl

/-- `CN.{l} : Type (l+1)` in any model that declares `CN`. -/
theorem vcn_ty (hc : env.constants `URec.CN = some CNdef.toVConstant) (hl : l.WF U) :
    env.HasType U Γ (vcn l) (.sort (.succ (.succ l))) :=
  .const hc (by simpa using hl) rfl

/-- `s z : α` under `z : α`, `s : α → α`, `α : Type l`. -/
theorem sz_ty :
    env.HasType U (.bvar 1 :: endoV :: vty l :: Γ) (.app (.bvar 1) (.bvar 0)) (.bvar 2) :=
  .app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (.bvar .zero)

/-- `one.{l}`'s value has type `CN.{l}`'s value in any model. -/
theorem oneV_ty (hl : l.WF U) : env.HasType U Γ (oneV l) (cnV l) :=
  .lam (.sort hl) (.lam endoV_ty (.lam (.bvar (.succ .zero)) sz_ty))

/-- `n : CN.{l}`, seen as `CN.{l}`'s value, under `z`, `s`, `α`. -/
theorem n_ty (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.HasType U (.bvar 1 :: endoV :: vty l :: vcn l :: Γ) (.bvar 3) (cnV l) :=
  (cn_unfold hd hl).defeq (.bvar (.succ (.succ (.succ .zero))))

/-- `n α : (α → α) → α → α` under `z`, `s`, `α`, `n : CN.{l}`. -/
theorem nα_ty (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.HasType U (.bvar 1 :: endoV :: vty l :: vcn l :: Γ) (.app (.bvar 3) (.bvar 2))
      (.forallE (.forallE (.bvar 2) (.bvar 3)) (.forallE (.bvar 3) (.bvar 4))) :=
  .app (A := vty l) (B := .forallE endoV zV) (n_ty hd hl) (.bvar (.succ (.succ .zero)))

/-- `n α s : α → α` under `z`, `s`, `α`, `n : CN.{l}`. -/
theorem nαs_ty (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.HasType U (.bvar 1 :: endoV :: vty l :: vcn l :: Γ)
      (.app (.app (.bvar 3) (.bvar 2)) (.bvar 1)) (.forallE (.bvar 2) (.bvar 3)) :=
  .app (A := .forallE (.bvar 2) (.bvar 3)) (B := .forallE (.bvar 3) (.bvar 4)) (nα_ty hd hl)
    (.bvar (.succ .zero))

/-- `n α s z : α` under `z`, `s`, `α`, `n : CN.{l}`. -/
theorem nαsz_ty (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.HasType U (.bvar 1 :: endoV :: vty l :: vcn l :: Γ) (spV (.bvar 3) (.bvar 0)) (.bvar 2) :=
  .app (A := .bvar 2) (B := .bvar 3) (nαs_ty hd hl) (.bvar .zero)

/-- `csucc.{l}`'s value has type `CN.{l} → CN.{l}` in any model that declares `CN` with its
defining equation: one δ-conversion for `n α`, one for the result. -/
theorem csuccV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hd : env.defeqs CNdef.toDefEq) (hl : l.WF U) :
    env.HasType U Γ (csuccV l) (.forallE (vcn l) (vcn l)) :=
  .lam (vcn_ty hc hl) ((cn_unfold hd hl).symm.defeq
    (.lam (.sort hl) (.lam endoV_ty (.lam (.bvar (.succ .zero))
      (.app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (nαsz_ty hd hl))))))

/-- `CB`'s value has type `Type 2` in any model. -/
theorem cbV_ty : env.HasType U Γ cbV (.sort lv3) :=
  (VEnv.IsDefEq.sortDF (l := .imax lv3 (.imax lv2 (.imax lv2 lv2))) (l' := lv3)
      ⟨trivial, trivial, trivial, trivial⟩ trivial (funext fun _ => rfl)).defeq
    (.forallE (.sort trivial) (.forallE (.bvar .zero)
      (.forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero))))))

/-- `CB` unfolds to its value in any model holding `CB`'s defining equation. -/
theorem cb_unfold (hd : env.defeqs CBdef.toDefEq) : env.IsDefEq U Γ vcb cbV (.sort lv3) :=
  .extra (ls := []) hd (fun _ h => nomatch h) rfl

/-- `CB : Type 2` in any model that declares `CB`. -/
theorem vcb_ty (hc : env.constants `URec.CB = some CBdef.toVConstant) :
    env.HasType U Γ vcb (.sort lv3) :=
  .const hc (fun _ h => nomatch h) rfl

/-- `btrue`'s value has type `CB`'s value in any model. -/
theorem btrueV_ty : env.HasType U Γ btrueV cbV :=
  .lam (.sort trivial) (.lam (.bvar .zero) (.lam (.bvar (.succ .zero)) (.bvar (.succ .zero))))

/-- `bfalse`'s value has type `CB`'s value in any model. -/
theorem bfalseV_ty : env.HasType U Γ bfalseV cbV :=
  .lam (.sort trivial) (.lam (.bvar .zero) (.lam (.bvar (.succ .zero)) (.bvar .zero)))

end

/-! ### The block's members -/

section
variable {env : VEnv} {Γ : List VExpr} {c : Name}

/-- `CN.{0} : Type 1` in any model that declares `CN`. -/
theorem cn0_ty (hc : env.constants `URec.CN = some CNdef.toVConstant) :
    env.HasType 0 Γ cn0 (.sort lv2) :=
  vcn_ty hc trivial

/-- `CN.{0} → CN.{0} : Type 1` in any model that declares `CN`. -/
theorem cnArrV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant) :
    env.HasType 0 Γ cnArrV ty2V :=
  (VEnv.IsDefEq.sortDF (l := .imax lv2 lv2) (l' := lv2) ⟨trivial, trivial⟩ trivial
      (funext fun _ => rfl)).defeq (.forallE (cn0_ty hc) (cn0_ty hc))

/-- `fun m => m : CN.{0} → CN.{0}` in any model that declares `CN`. -/
theorem idV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant) :
    env.HasType 0 Γ idV cnArrV :=
  .lam (cn0_ty hc) (.bvar .zero)

/-- `c btrue : CN.{0} → CN.{0}`, for a constant `c` of the members' type. -/
theorem cbt_ty (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) :
    env.HasType 0 Γ (.app (.const c []) (.const `URec.btrue [])) (.forallE cn0 cn0) :=
  .app (A := vcb) (B := .forallE cn0 cn0) (.const hcc (fun _ h => nomatch h) rfl)
    (.const hbt (fun _ h => nomatch h) rfl)

/-- `csucc.{0} : CN.{0} → CN.{0}` in any model that declares `csucc`. -/
theorem csucc0_ty (hcs : env.constants `URec.csucc = some csuccdef.toVConstant) :
    env.HasType 0 Γ (.const `URec.csucc [.zero]) (.forallE cn0 cn0) :=
  .const hcs (by simp [VLevel.WF]) rfl

/-- `csucc.{0} m : CN.{0}` under `m : CN.{0}`. -/
theorem csm_ty (hcs : env.constants `URec.csucc = some csuccdef.toVConstant) :
    env.HasType 0 (cn0 :: Γ) (.app (.const `URec.csucc [.zero]) (.bvar 0)) cn0 :=
  .app (A := cn0) (B := cn0) (csucc0_ty hcs) (.bvar .zero)

/-- `c btrue (csucc.{0} m) : CN.{0}` under `m : CN.{0}`, for a constant `c` of the members' type. -/
theorem callBody_ty (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) :
    env.HasType 0 (cn0 :: Γ)
      (.app (.app (.const c []) (.const `URec.btrue []))
        (.app (.const `URec.csucc [.zero]) (.bvar 0)))
      cn0 :=
  .app (A := cn0) (B := cn0) (cbt_ty hbt hcc) (csm_ty hcs)

/-- `fun m => c btrue (csucc.{0} m) : CN.{0} → CN.{0}`, for a constant `c` of the members'
type. -/
theorem callV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) : env.HasType 0 Γ (callV c) cnArrV :=
  .lam (cn0_ty hc) (callBody_ty hbt hcs hcc)

/-- `b : CB`, seen as `CB`'s value, under `n : CN.{0}`, `b : CB`. -/
theorem b_ty (hdb : env.defeqs CBdef.toDefEq) : env.HasType 0 (cn0 :: vcb :: Γ) (.bvar 1) cbV :=
  (cb_unfold hdb).defeq (.bvar (.succ .zero))

/-- `b (CN.{0} → CN.{0})` under `n`, `b`. -/
theorem bα_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hdb : env.defeqs CBdef.toDefEq) :
    env.HasType 0 (cn0 :: vcb :: Γ) (.app (.bvar 1) cnArrV)
      (.forallE cnArrV (.forallE cnArrV cnArrV)) :=
  .app (A := ty2V) (B := .forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))) (b_ty hdb)
    (cnArrV_ty hc)

/-- `b (CN.{0} → CN.{0}) (fun m => m)` under `n`, `b`. -/
theorem bαi_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hdb : env.defeqs CBdef.toDefEq) :
    env.HasType 0 (cn0 :: vcb :: Γ) (.app (.app (.bvar 1) cnArrV) idV) (.forallE cnArrV cnArrV) :=
  .app (A := cnArrV) (B := .forallE cnArrV cnArrV) (bα_ty hc hdb) (idV_ty hc)

/-- `b (CN.{0} → CN.{0}) (fun m => m) (fun m => c btrue (csucc m))` under `n`, `b`. -/
theorem bαig_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hdb : env.defeqs CBdef.toDefEq) (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) :
    env.HasType 0 (cn0 :: vcb :: Γ) (.app (.app (.app (.bvar 1) cnArrV) idV) (callV c)) cnArrV :=
  .app (A := cnArrV) (B := cnArrV) (bαi_ty hc hdb) (callV_ty hc hbt hcs hcc)

/-- The body of the member that calls `c` has type `CN.{0}` under `n`, `b`. -/
theorem selV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hdb : env.defeqs CBdef.toDefEq) (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) :
    env.HasType 0 (cn0 :: vcb :: Γ) (selV c) cn0 :=
  .app (A := cn0) (B := cn0) (bαig_ty hc hdb hbt hcs hcc) (.bvar .zero)

/-- The member that calls `c` has type `CB → CN.{0} → CN.{0}` in any model that declares `CN`,
`CB` (with its defining equation), `btrue`, `csucc` and `c`: one δ-conversion of `CB` and one
conversion of the sort of `CN.{0} → CN.{0}`. -/
theorem memberV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hcb : env.constants `URec.CB = some CBdef.toVConstant) (hdb : env.defeqs CBdef.toDefEq)
    (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) : env.HasType 0 [] (memberV c) memberTyV :=
  .lam (vcb_ty hcb) (.lam (cn0_ty hc) (selV_ty hc hdb hbt hcs hcc))

/-- `CB → CN.{0} → CN.{0}` is a type in any model that declares `CN` and `CB`. -/
theorem memberTyV_ty (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hcb : env.constants `URec.CB = some CBdef.toVConstant) : env.IsType 0 Γ memberTyV :=
  ⟨_, .forallE (vcb_ty hcb) (.forallE (cn0_ty hc) (cn0_ty hc))⟩

end

/-! ## The translation -/

section
variable {env : VEnv} {Us : List Name} {Δ : VLCtx} {l : Level} {l' : VLevel}

/-- `α → α` translates to `endoV` under `α : Type l`. -/
theorem trEndo {l : VLevel} : TrS env Us ((none, .vlam (vty l)) :: Δ) endoE endoV :=
  .forallE ⟨_, .bvar .zero⟩ ⟨_, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl)

/-- `α` translates under `s`, `α`. -/
theorem trAlpha {l : VLevel} :
    TrS env Us ((none, .vlam endoV) :: (none, .vlam (vty l)) :: Δ) (.bvar 1) (.bvar 1) :=
  .bvar rfl

/-- `CN.{l}`'s value translates to `cnV l'` when `l + 1` translates to `l' + 1`. -/
theorem trCn (h : VLevel.ofLevel Us (.succ l) = some (.succ l')) (hl : l'.WF Us.length) :
    TrS env Us Δ (cnE l) (cnV l') :=
  .forallE ⟨_, .sort hl⟩ ⟨_, .forallE endoV_ty zV_ty⟩ (.sort h)
    (.forallE ⟨_, endoV_ty⟩ ⟨_, zV_ty⟩ trEndo
      (.forallE ⟨_, .bvar (.succ .zero)⟩ ⟨_, .bvar (.succ (.succ .zero))⟩ trAlpha (.bvar rfl)))

/-- `one.{l}`'s value translates to `oneV l'` when `l + 1` translates to `l' + 1`. -/
theorem trOne (h : VLevel.ofLevel Us (.succ l) = some (.succ l')) (hl : l'.WF Us.length) :
    TrS env Us Δ (oneE l) (oneV l') :=
  .lam ⟨_, .sort hl⟩ (.sort h) (.lam ⟨_, endoV_ty⟩ trEndo (.lam ⟨_, .bvar (.succ .zero)⟩ trAlpha
    (.app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (.bvar .zero) (.bvar rfl)
      (.bvar rfl))))

/-- `csucc.{u}`'s value translates to `csuccV vu` in any model that declares `CN` with its defining
equation. -/
theorem trCsucc (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hd : env.defeqs CNdef.toDefEq) : TrS env [`u] [] (csuccE lu) (csuccV vu) :=
  .lam ⟨_, vcn_ty hc vu_wf⟩ (.const hc rfl rfl)
    (.lam ⟨_, .sort vu_wf⟩ (.sort rfl) (.lam ⟨_, endoV_ty⟩ trEndo
      (.lam ⟨_, .bvar (.succ .zero)⟩ trAlpha
        (.app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (nαsz_ty hd vu_wf) (.bvar rfl)
          (.app (A := .bvar 2) (B := .bvar 3) (nαs_ty hd vu_wf) (.bvar .zero)
            (.app (A := .forallE (.bvar 2) (.bvar 3)) (B := .forallE (.bvar 3) (.bvar 4))
              (nα_ty hd vu_wf) (.bvar (.succ .zero))
              (.app (A := vty vu) (B := .forallE endoV zV) (n_ty hd vu_wf)
                (.bvar (.succ (.succ .zero))) (.bvar rfl) (.bvar rfl))
              (.bvar rfl))
            (.bvar rfl))))))

/-- `CB`'s value translates to `cbV`. -/
theorem trCb : TrS env [] Δ cbE cbV :=
  .forallE ⟨_, .sort trivial⟩
    ⟨_, .forallE (.bvar .zero) (.forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero))))⟩
    (.sort rfl)
    (.forallE ⟨_, .bvar .zero⟩ ⟨_, .forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))⟩
      (.bvar rfl)
      (.forallE ⟨_, .bvar (.succ .zero)⟩ ⟨_, .bvar (.succ (.succ .zero))⟩ (.bvar rfl) (.bvar rfl)))

/-- `btrue`'s value translates to `btrueV`. -/
theorem trBtrue : TrS env [] Δ btrueE btrueV :=
  .lam ⟨_, .sort trivial⟩ (.sort rfl)
    (.lam ⟨_, .bvar .zero⟩ (.bvar rfl) (.lam ⟨_, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl)))

/-- `bfalse`'s value translates to `bfalseV`. -/
theorem trBfalse : TrS env [] Δ bfalseE bfalseV :=
  .lam ⟨_, .sort trivial⟩ (.sort rfl)
    (.lam ⟨_, .bvar .zero⟩ (.bvar rfl) (.lam ⟨_, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl)))

/-- `CN.{0}` translates to `cn0` in any model that declares `CN`. -/
theorem trCn0 (hc : env.constants `URec.CN = some CNdef.toVConstant) :
    TrS env [] Δ (cnC .zero) cn0 :=
  .const hc rfl rfl

/-- `CN.{0} → CN.{0}` translates to `cnArrV` in any model that declares `CN`. -/
theorem trCnArr (hc : env.constants `URec.CN = some CNdef.toVConstant) :
    TrS env [] Δ cnArrE cnArrV :=
  .forallE ⟨_, cn0_ty hc⟩ ⟨_, cn0_ty hc⟩ (trCn0 hc) (trCn0 hc)

/-- The members' type translates to `memberTyV` in any model that declares `CN` and `CB`. -/
theorem trMemberTy (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hcb : env.constants `URec.CB = some CBdef.toVConstant) :
    TrS env [] [] memberTyE memberTyV :=
  .forallE ⟨_, vcb_ty hcb⟩ ⟨_, .forallE (cn0_ty hc) (cn0_ty hc)⟩ (.const hcb rfl rfl)
    (.forallE ⟨_, cn0_ty hc⟩ ⟨_, cn0_ty hc⟩ (trCn0 hc) (trCn0 hc))

/-- The value of the member that calls `c` translates to `memberV c` in any model that declares
`CN`, `CB` (with its defining equation), `btrue`, `csucc` and `c`. -/
theorem trMember {c : Name} (hc : env.constants `URec.CN = some CNdef.toVConstant)
    (hcb : env.constants `URec.CB = some CBdef.toVConstant) (hdb : env.defeqs CBdef.toDefEq)
    (hbt : env.constants `URec.btrue = some btruedef.toVConstant)
    (hcs : env.constants `URec.csucc = some csuccdef.toVConstant)
    (hcc : env.constants c = some ⟨0, memberTyV⟩) : TrS env [] [] (memberE c) (memberV c) :=
  .lam ⟨_, vcb_ty hcb⟩ (.const hcb rfl rfl) (.lam ⟨_, cn0_ty hc⟩ (trCn0 hc)
    (.app (A := cn0) (B := cn0) (bαig_ty hc hdb hbt hcs hcc) (.bvar .zero)
      (.app (A := cnArrV) (B := cnArrV) (bαi_ty hc hdb) (callV_ty hc hbt hcs hcc)
        (.app (A := cnArrV) (B := .forallE cnArrV cnArrV) (bα_ty hc hdb) (idV_ty hc)
          (.app (A := ty2V) (B := .forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))) (b_ty hdb)
            (cnArrV_ty hc) (.bvar rfl) (trCnArr hc))
          (.lam ⟨_, cn0_ty hc⟩ (trCn0 hc) (.bvar rfl)))
        (.lam ⟨_, cn0_ty hc⟩ (trCn0 hc)
          (.app (A := cn0) (B := cn0) (cbt_ty hbt hcc) (csm_ty hcs)
            (.app (A := vcb) (B := .forallE cn0 cn0) (.const hcc (fun _ h => nomatch h) rfl)
              (.const hbt (fun _ h => nomatch h) rfl) (.const hcc rfl rfl) (.const hbt rfl rfl))
            (.app (A := cn0) (B := cn0) (csucc0_ty hcs) (.bvar .zero) (.const hcs rfl rfl)
              (.bvar rfl)))))
      (.bvar rfl)))

end

/-! ## `henv`: the program's environment -/

/-- The model of `[CN]` is `envCN`. -/
theorem pCN : ProgEnv [.defnInfo CN_val] envCN :=
  .defn (ci' := CNdef) .nil rfl ⟨⟨rfl, .sort rfl⟩, rfl, trCn rfl vu_wf⟩ (cnV_ty vu_wf) rfl

/-- The model of `[one, CN]` is `envOne`: `one`'s value has type `CN.{u}` by one δ-conversion. -/
theorem pOne : ProgEnv [.defnInfo one_val, .defnInfo CN_val] envOne :=
  .defn (ci' := onedef) pCN rfl ⟨⟨rfl, .const rfl rfl rfl⟩, rfl, trOne rfl vu_wf⟩
    ((cn_unfold (Or.inl rfl) vu_wf).symm.defeq (oneV_ty vu_wf)) rfl

/-- The model of `[csucc, one, CN]` is `envCsucc`. -/
theorem pCsucc : ProgEnv [.defnInfo csucc_val, .defnInfo one_val, .defnInfo CN_val] envCsucc :=
  .defn (ci' := csuccdef) pOne rfl
    ⟨⟨rfl, .forallE ⟨_, vcn_ty rfl vu_wf⟩ ⟨_, vcn_ty rfl vu_wf⟩ (.const rfl rfl rfl)
      (.const rfl rfl rfl)⟩, rfl, trCsucc rfl (Or.inr (Or.inl rfl))⟩
    (csuccV_ty rfl (Or.inr (Or.inl rfl)) vu_wf) rfl

/-- The model of `[CB, csucc, one, CN]` is `envCB`. -/
theorem pCB :
    ProgEnv [.defnInfo CB_val, .defnInfo csucc_val, .defnInfo one_val, .defnInfo CN_val] envCB :=
  .defn (ci' := CBdef) pCsucc rfl ⟨⟨rfl, .sort rfl⟩, rfl, trCb⟩ cbV_ty rfl

/-- The model of `[btrue, CB, csucc, one, CN]` is `envBtrue`. -/
theorem pBtrue :
    ProgEnv [.defnInfo btrue_val, .defnInfo CB_val, .defnInfo csucc_val, .defnInfo one_val,
      .defnInfo CN_val] envBtrue :=
  .defn (ci' := btruedef) pCB rfl ⟨⟨rfl, .const rfl rfl rfl⟩, rfl, trBtrue⟩
    ((cb_unfold (Or.inl rfl)).symm.defeq btrueV_ty) rfl

/-- The model of the declarations before the block is `envBfalse`. -/
theorem pBfalse :
    ProgEnv [.defnInfo bfalse_val, .defnInfo btrue_val, .defnInfo CB_val, .defnInfo csucc_val,
      .defnInfo one_val, .defnInfo CN_val] envBfalse :=
  .defn (ci' := bfalsedef) pBtrue rfl ⟨⟨rfl, .const rfl rfl rfl⟩, rfl, trBfalse⟩
    ((cb_unfold (Or.inr (Or.inl rfl))).symm.defeq bfalseV_ty) rfl

/-- `envBlk` holds `CB`'s defining equation. -/
theorem envBlk_dCB : envBlk.defeqs CBdef.toDefEq := Or.inr (Or.inr (Or.inl rfl))

/-- The block's constants are added to `envBfalse` in `all` order. -/
theorem addBlk : envBfalse.addConsts [uadef, ubdef] = some envBlk := rfl

/-- The program's model is `venv4`: `ProgEnv.block` adds the two members' constants, translates
and types their values in `envBlk` (where each member's value mentions the other member), and adds
their defining equations; the members appear in `decls4` in reversed `all` order. The environment
hypothesis of `erases_correct` on NV-4. Reference: the hypothesis `wf_ext Σ` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem henv : ProgEnv decls4 venv4 :=
  .block (vs := [ua_val, ub_val]) (cis' := [uadef, ubdef]) pBfalse (by decide)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> rfl)
    (.cons ⟨⟨rfl, trMemberTy rfl rfl⟩, rfl, trMember rfl rfl envBlk_dCB rfl rfl rfl⟩
      (.cons ⟨⟨rfl, trMemberTy rfl rfl⟩, rfl, trMember rfl rfl envBlk_dCB rfl rfl rfl⟩ .nil))
    (by intro ci h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact memberTyV_ty rfl rfl)
    addBlk
    (by intro ci h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact memberV_ty rfl rfl envBlk_dCB rfl rfl rfl)

/-- `ua bfalse : CN.{0} → CN.{0}` in the program's model. -/
theorem ua_bfalse_ty :
    venv4.HasType 0 [] (.app (.const `URec.ua []) (.const `URec.bfalse [])) (.forallE cn0 cn0) :=
  .app (A := vcb) (B := .forallE cn0 cn0)
    (.const (ci := uadef.toVConstant) rfl (fun _ h => nomatch h) rfl)
    (.const (ci := bfalsedef.toVConstant) rfl (fun _ h => nomatch h) rfl)

/-- `e4` translates to `e4'` in the program's model, with both sides of each application typed:
the typing hypothesis of `erases_correct` on NV-4. Reference: the hypothesis `welltyped Σ [] t`
of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS venv4 [] [] e4 e4' :=
  .app (A := cn0) (B := cn0) ua_bfalse_ty
    (.const (ci := onedef.toVConstant) rfl (by simp [VLevel.WF]) rfl)
    (.app (A := vcb) (B := .forallE cn0 cn0)
      (.const (ci := uadef.toVConstant) rfl (fun _ h => nomatch h) rfl)
      (.const (ci := bfalsedef.toVConstant) rfl (fun _ h => nomatch h) rfl)
      (.const rfl rfl rfl) (.const rfl rfl rfl))
    (.const rfl rfl rfl)

/-! ## The evaluation environment and the source evaluation -/

/-- The program's view: list lookup, nothing `@[extern]`, no inline attribute. -/
def view4 : EnvView := ⟨fun n => decls4.find? (·.name == n), fun _ => false, fun _ => none⟩

/-- The program's evaluation environment under the default configuration. -/
def σ4 : EvalEnv := evalEnvOf view4 {} decls4

/-- `fun α s z => s (one.{0}' α s z)`, with `one.{0}'` the value of `one.{0}`: the value of
`e4`. -/
def v4 : Expr := succBodyE .zero (oneE .zero)

/-- `ua` unfolds to its value. -/
theorem unfold_ua : σ4.unfold? `URec.ua = some (.defnInfo ua_val, memberE `URec.ub) := rfl

/-- `ub` unfolds to its value. -/
theorem unfold_ub : σ4.unfold? `URec.ub = some (.defnInfo ub_val, memberE `URec.ua) := rfl

/-- `ua` is recursive: it belongs to a block of two members. -/
theorem rec_ua : RecursiveDecl (.defnInfo ua_val) = true := by decide

/-- `ub` is recursive: it belongs to a block of two members. -/
theorem rec_ub : RecursiveDecl (.defnInfo ub_val) = true := by decide

/-- `bfalse` evaluates, by δ, to its value. -/
theorem ev_bfalse : SrcEval σ4 (.const `URec.bfalse []) bfalseE :=
  .delta rfl rfl rfl (.atom trivial)

/-- `btrue` evaluates, by δ, to its value. -/
theorem ev_btrue : SrcEval σ4 (.const `URec.btrue []) btrueE :=
  .delta rfl rfl rfl (.atom trivial)

/-- `one.{0}` evaluates, by δ at the level `0`, to `one`'s value at the level `0`. -/
theorem ev_one0 : SrcEval σ4 (.const `URec.one [.zero]) (oneE .zero) :=
  .delta rfl rfl rfl (.atom trivial)

/-- `ua bfalse` evaluates, by `fixAtom` and `fixApp` (`ua` unfolds when applied), to the λ that
selects on `bfalse`. -/
theorem ev_ua_bfalse :
    SrcEval σ4 (.app (.const `URec.ua []) (.const `URec.bfalse []))
      (.lam `n (cnC .zero) (appSelE bfalseE (.bvar 0) `URec.ub) .default) :=
  .fixApp (.fixAtom unfold_ua rec_ua rfl) unfold_ua rec_ua ev_bfalse
    (.beta (.atom trivial) (.atom trivial) (.atom trivial))

/-- `ub btrue` evaluates, by `fixAtom` and `fixApp`, to the λ that selects on `btrue`. -/
theorem ev_ub_btrue :
    SrcEval σ4 (.app (.const `URec.ub []) (.const `URec.btrue []))
      (.lam `n (cnC .zero) (appSelE btrueE (.bvar 0) `URec.ua) .default) :=
  .fixApp (.fixAtom unfold_ub rec_ub rfl) unfold_ub rec_ub ev_btrue
    (.beta (.atom trivial) (.atom trivial) (.atom trivial))

/-- `bfalse` selects its second branch: `bfalse (CN.{0} → CN.{0}) (fun m => m) (fun m => ub …)`
evaluates, by β, to the second branch. -/
theorem ev_sel_false :
    SrcEval σ4 (.app (.app (.app bfalseE cnArrE) idE) (callE `URec.ub)) (callE `URec.ub) :=
  .beta (.beta (.beta (.atom trivial) (.atom trivial) (.atom trivial)) (.atom trivial)
    (.atom trivial)) (.atom trivial) (.atom trivial)

/-- `btrue` selects its first branch. -/
theorem ev_sel_true :
    SrcEval σ4 (.app (.app (.app btrueE cnArrE) idE) (callE `URec.ua)) idE :=
  .beta (.beta (.beta (.atom trivial) (.atom trivial) (.atom trivial)) (.atom trivial)
    (.atom trivial)) (.atom trivial) (.atom trivial)

/-- `csucc.{0} one.{0}'` evaluates, by δ at the level `0` and β, to `v4`. -/
theorem ev_csucc : SrcEval σ4 (.app (.const `URec.csucc [.zero]) (oneE .zero)) v4 :=
  .beta (.delta rfl rfl rfl (.atom trivial)) (.atom trivial) (.atom trivial)

/-- `ub btrue (csucc.{0} one.{0}')` evaluates to `v4`: `btrue` selects `fun m => m`. -/
theorem ev_ub_call :
    SrcEval σ4 (.app (.app (.const `URec.ub []) (.const `URec.btrue []))
      (.app (.const `URec.csucc [.zero]) (oneE .zero))) v4 :=
  .beta ev_ub_btrue ev_csucc (.beta ev_sel_true (.atom trivial) (.atom trivial))

/-- `e4` evaluates to `v4`: `ua` unfolds when applied to `bfalse`, which selects the branch that
calls `ub` on `csucc one`; `ub` unfolds when applied to `btrue`, which selects the identity. The
source-evaluation hypothesis of `erases_correct` on NV-4. Reference: the hypothesis
`Σ |-p t ⇓ v` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval σ4 e4 v4 :=
  .beta ev_ua_bfalse ev_one0 (.beta ev_sel_false (.atom trivial) ev_ub_call)

/-- Every declaration is the first of its name, so the evaluation environment is a
sub-environment of the program: the hypothesis `hsub` of `erases_correct` on NV-4. -/
theorem hsub : SubEnv σ4.decls decls4 := by
  intro ci h
  simp only [σ4, evalEnvOf, decls4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The program's constants are `ub`, `ua`, `bfalse`, `btrue`, `CB`, `csucc`, `one` and `CN`. -/
theorem mem_names {c : Name} (h : (findDecl decls4 c).isSome = true) :
    c = `URec.ub ∨ c = `URec.ua ∨ c = `URec.bfalse ∨ c = `URec.btrue ∨ c = `URec.CB ∨
      c = `URec.csucc ∨ c = `URec.one ∨ c = `URec.CN := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, ub_val, ua_val, bfalse_val, btrue_val,
      CB_val, csucc_val, one_val, CN_val] at hc <;>
    subst hc <;> simp

/-- The program's kernames are distinct: the hypothesis `hinj` of `erases_correct` on NV-4. -/
theorem hinj : KernameInj σ4.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem_names h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-! ## The erased program -/

/-- `λα. λs. λz. s z`: the λ□ body of `one`. -/
def oneL : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `s) (.lambda (binderNameOf `z)
    (.app (.bvar 1) (.bvar 0))))

/-- `f □ s a`: the erased type argument is `□`. -/
def spL (f a : LBTerm) : LBTerm := .app (.app (.app f .box) (.bvar 1)) a

/-- `λα. λs. λz. s (f □ s z)`, with `f` under the three binders. -/
def succBodyL (f : LBTerm) : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `s) (.lambda (binderNameOf `z)
    (.app (.bvar 1) (spL f (.bvar 0)))))

/-- `λn. λα. λs. λz. s (n □ s z)`: the λ□ body of `csucc`. -/
def csuccL : LBTerm := .lambda (binderNameOf `n) (succBodyL (.bvar 3))

/-- `λα. λt. λf. t`: the λ□ body of `btrue`. -/
def btrueL : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `t) (.lambda (binderNameOf `f) (.bvar 1)))

/-- `λα. λt. λf. f`: the λ□ body of `bfalse`. -/
def bfalseL : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `t) (.lambda (binderNameOf `f) (.bvar 0)))

/-- `λm. m`. -/
def idL : LBTerm := .lambda (binderNameOf `m) (.bvar 0)

/-- `λm. r btrue (csucc m)`: the erased branch that calls the member `r`. -/
def callL (r : LBTerm) : LBTerm :=
  .lambda (binderNameOf `m)
    (.app (.app r (.const (toKername `URec.btrue)))
      (.app (.const (toKername `URec.csucc)) (.bvar 0)))

/-- `b □ (λm. m) (λm. r btrue (csucc m)) x`. -/
def appSelL (b x r : LBTerm) : LBTerm := .app (.app (.app (.app b .box) idL) (callL r)) x

/-- `λb. λn. b □ (λm. m) (λm. r btrue (csucc m)) n`: the erased member that calls `r`. -/
def memberL (r : LBTerm) : LBTerm :=
  .lambda (binderNameOf `b) (.lambda (binderNameOf `n) (appSelL (.bvar 1) (.bvar 0) r))

/-- The λ□ block of `ua` and `ub`: each body calls the other member through the fixpoint's
binders (`ub` is the index `0` below `ua`'s three λs, `ua` the index `1` below `ub`'s). -/
def defs4 : List (@FixDef LBTerm) :=
  [{ name := fixDefName `URec.ua, body := memberL (.bvar 3), principalArgIdx := 0 },
   { name := fixDefName `URec.ub, body := memberL (.bvar 4), principalArgIdx := 0 }]

/-- The λ□ environment, as `#erase` emits it: `ua` and `ub` are the members `0` and `1` of the
fixpoint `fix defs4`. -/
def lenv4 : GlobalDeclarations :=
  [(toKername `URec.one, .constantDecl ⟨some oneL⟩),
   (toKername `URec.bfalse, .constantDecl ⟨some bfalseL⟩),
   (toKername `URec.ub, .constantDecl ⟨some (.fix defs4 1)⟩),
   (toKername `URec.ua, .constantDecl ⟨some (.fix defs4 0)⟩),
   (toKername `URec.csucc, .constantDecl ⟨some csuccL⟩),
   (toKername `URec.btrue, .constantDecl ⟨some btrueL⟩)]

/-- `ua bfalse one`: the erasure of `e4`. -/
def t4 : LBTerm :=
  .app (.app (.const (toKername `URec.ua)) (.const (toKername `URec.bfalse)))
    (.const (toKername `URec.one))

/-- `λα. λs. λz. s (one' □ s z)`, with `one'` the λ□ body of `one`: the erasure of `v4`. -/
def v4' : LBTerm := succBodyL oneL

/-- `ua`'s body with the block's members substituted (`cunfold_fix defs4 0`): `ub` is
`fix defs4 1`. -/
theorem cunfold_ua : cunfoldFix defs4 0 = some (0, memberL (.fix defs4 1)) := rfl

/-- `ub`'s body with the block's members substituted (`cunfold_fix defs4 1`): `ua` is
`fix defs4 0`. -/
theorem cunfold_ub : cunfoldFix defs4 1 = some (0, memberL (.fix defs4 0)) := rfl

/-- `one` is stored with its erased body. -/
theorem look_one : lookupConst lenv4 (toKername `URec.one) = some ⟨some oneL⟩ := rfl
/-- `bfalse` is stored with its erased body. -/
theorem look_bfalse : lookupConst lenv4 (toKername `URec.bfalse) = some ⟨some bfalseL⟩ := rfl
/-- `ub` is stored as the member `1` of the block. -/
theorem look_ub : lookupConst lenv4 (toKername `URec.ub) = some ⟨some (.fix defs4 1)⟩ := rfl
/-- `ua` is stored as the member `0` of the block. -/
theorem look_ua : lookupConst lenv4 (toKername `URec.ua) = some ⟨some (.fix defs4 0)⟩ := rfl
/-- `csucc` is stored with its erased body. -/
theorem look_csucc : lookupConst lenv4 (toKername `URec.csucc) = some ⟨some csuccL⟩ := rfl
/-- `btrue` is stored with its erased body. -/
theorem look_btrue : lookupConst lenv4 (toKername `URec.btrue) = some ⟨some btrueL⟩ := rfl
/-- `CB`, a type, is not stored. -/
theorem look_CB : lookupConst lenv4 (toKername `URec.CB) = none := by decide
/-- `CN`, a type, is not stored. -/
theorem look_CN : lookupConst lenv4 (toKername `URec.CN) = none := by decide

/-- A declaration found in a λ□ environment is its first entry or is found in the rest. -/
theorem lookupConst_cons {kn kn' : Kername} {cb cb' : ConstantBody} {rest : GlobalDeclarations}
    (h : lookupConst ((kn', .constantDecl cb') :: rest) kn = some cb) :
    cb = cb' ∨ lookupConst rest kn = some cb := by
  unfold lookupConst at h ⊢
  rw [List.find?_cons] at h
  cases hk : (kn' == kn) <;> simp only [hk] at h
  · exact .inr h
  · exact .inl (Option.some.inj h).symm

/-- The declarations of `lenv4` are the six stored bodies. -/
theorem look_cases {kn : Kername} {cb : ConstantBody} (h : lookupConst lenv4 kn = some cb) :
    cb = ⟨some oneL⟩ ∨ cb = ⟨some bfalseL⟩ ∨ cb = ⟨some (.fix defs4 1)⟩ ∨
      cb = ⟨some (.fix defs4 0)⟩ ∨ cb = ⟨some csuccL⟩ ∨ cb = ⟨some btrueL⟩ := by
  rcases lookupConst_cons h with h | h; · exact .inl h
  rcases lookupConst_cons h with h | h; · exact .inr (.inl h)
  rcases lookupConst_cons h with h | h; · exact .inr (.inr (.inl h))
  rcases lookupConst_cons h with h | h; · exact .inr (.inr (.inr (.inl h)))
  rcases lookupConst_cons h with h | h; · exact .inr (.inr (.inr (.inr (.inl h))))
  rcases lookupConst_cons h with h | h; · exact .inr (.inr (.inr (.inr (.inr h))))
  cases h

/-- `lenv4`'s bodies are closed, the fixpoint's bodies below its two binders: the hypothesis
`hlc` of `erases_correct` on NV-4. -/
theorem hlc : LenvClosed lenv4 := by
  intro kn cb b h hb
  rcases look_cases h with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hb <;>
    exact ⟨rfl, fun _ => rfl⟩

/-! ## The erasure relation -/

/-- `ua` is not an atom: it unfolds. -/
theorem atom_ua : σ4.isAtom `URec.ua = false := by decide
/-- `ub` is not an atom: it unfolds. -/
theorem atom_ub : σ4.isAtom `URec.ub = false := by decide
/-- `bfalse` is not an atom: it unfolds. -/
theorem atom_bfalse : σ4.isAtom `URec.bfalse = false := by decide
/-- `btrue` is not an atom: it unfolds. -/
theorem atom_btrue : σ4.isAtom `URec.btrue = false := by decide
/-- `one` is not an atom: it unfolds. -/
theorem atom_one : σ4.isAtom `URec.one = false := by decide
/-- `csucc` is not an atom: it unfolds. -/
theorem atom_csucc : σ4.isAtom `URec.csucc = false := by decide

/-- `ua`'s admissible target is its stored fixpoint. -/
theorem recIn_ua : RecIn lenv4 `URec.ua (.fix defs4 0) := ⟨defs4, 0, rfl, look_ua⟩

/-- `ub`'s admissible target is its stored fixpoint. -/
theorem recIn_ub : RecIn lenv4 `URec.ub (.fix defs4 1) := ⟨defs4, 1, rfl, look_ub⟩

section
variable {Us : List Name} {Δ : VLCtx}

/-- `one.{l}`'s value erases to `oneL` in any context. -/
theorem erOne {l : Level} {l' : VLevel} (h : VLevel.ofLevel Us (.succ l) = some (.succ l')) :
    Erases venv4 Us σ4.isAtom (RecIn lenv4) Δ (oneE l) oneL :=
  .lam (.sort h) (.lam trEndo (.lam trAlpha (.app .bvar .bvar)))

/-- The type variable `α` is erasable under `z`, `s`, `α : Type l`: its type is a sort. -/
theorem erAlpha {l' : VLevel} :
    ErasableS venv4 Us
      ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam (vty l')) :: Δ) (.bvar 2) :=
  ⟨.bvar 2, .bvar rfl, vty l', .bvar (.succ (.succ .zero)), .inl trivial⟩

/-- `fun α s z => s (f α s z)` at the level `l` erases to `λα. λs. λz. s (f' □ s z)` when `f`
erases to `f'` under the three binders. -/
theorem erSuccBody {l : Level} {l' : VLevel} {f : Expr} {f' : LBTerm}
    (h : VLevel.ofLevel Us (.succ l) = some (.succ l'))
    (hf : Erases venv4 Us σ4.isAtom (RecIn lenv4)
      ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam (vty l')) :: Δ) f f') :
    Erases venv4 Us σ4.isAtom (RecIn lenv4) Δ (succBodyE l f) (succBodyL f') :=
  .lam (.sort h) (.lam trEndo (.lam trAlpha (.app .bvar (.app (.app (.app hf (.box erAlpha)) .bvar)
    .bvar))))

end

/-- `csucc.{u}`'s value erases to `csuccL`: the type argument of `n` is boxed. -/
theorem erCsucc : Erases venv4 [`u] σ4.isAtom (RecIn lenv4) [] (csuccE lu) csuccL :=
  .lam (.const rfl rfl rfl) (erSuccBody rfl .bvar)

/-- `btrue`'s value erases to `btrueL`. -/
theorem erBtrue : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] btrueE btrueL :=
  .lam (.sort rfl) (.lam (.bvar rfl) (.lam (.bvar rfl) .bvar))

/-- `bfalse`'s value erases to `bfalseL`. -/
theorem erBfalse : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] bfalseE bfalseL :=
  .lam (.sort rfl) (.lam (.bvar rfl) (.lam (.bvar rfl) .bvar))

/-- `CN.{0} → CN.{0}` is erasable under `n`, `b`: its type is a sort. -/
theorem erCnArr :
    ErasableS venv4 [] [(none, .vlam cn0), (none, .vlam vcb)] cnArrE :=
  ⟨cnArrV, trCnArr rfl, ty2V, cnArrV_ty rfl, .inl trivial⟩

/-- The value of the member that calls `c` erases to `memberL r` when `c` is not an atom and its
admissible target is `r`: the type argument is boxed and the call goes through `Erases.constRec`. -/
theorem erMember {c : Name} {r : LBTerm} (hc : σ4.isAtom c = false) (hr : RecIn lenv4 c r) :
    Erases venv4 [] σ4.isAtom (RecIn lenv4) [] (memberE c) (memberL r) :=
  .lam (.const rfl rfl rfl) (.lam (trCn0 rfl)
    (.app (.app (.app (.app .bvar (.box erCnArr)) (.lam (trCn0 rfl) .bvar))
      (.lam (trCn0 rfl)
        (.app (.app (.constRec hc hr) (.const atom_btrue)) (.app (.const atom_csucc) .bvar))))
      .bvar))

/-- The two-member block: each member's value erases to its fixpoint body with the block's
members substituted (`cunfold_fix`), each member is stored as its member of `fix defs4`, and the
fixpoint's names and principal arguments are the eraser's. -/
theorem block4 : ErasesBlock venv4 σ4 lenv4 [`URec.ua, `URec.ub] defs4 := by
  refine ⟨rfl, fun j n hn => ?_⟩
  match j, hn with
  | 0, hn =>
    cases hn
    exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, erMember atom_ub recIn_ub, look_ua⟩
  | 1, hn =>
    cases hn
    exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, erMember atom_ua recIn_ua, look_ub⟩

/-- `ua`'s stored body is its member of the erased block. -/
theorem decl_ua : ErasesDecl venv4 σ4 lenv4 (.defnInfo ua_val) ⟨some (.fix defs4 0)⟩ :=
  .inr (.inl ⟨by decide, rec_ua, defs4, 0, rfl, rfl, block4⟩)

/-- `ub`'s stored body is its member of the erased block. -/
theorem decl_ub : ErasesDecl venv4 σ4 lenv4 (.defnInfo ub_val) ⟨some (.fix defs4 1)⟩ :=
  .inr (.inl ⟨by decide, rec_ub, defs4, 1, rfl, rfl, block4⟩)

/-- `btrue`'s dependency entry. -/
theorem deps_btrue : ErasesDeps venv4 σ4 lenv4 (.const (toKername `URec.btrue)) :=
  .const (ci := .defnInfo btrue_val) rfl look_btrue
    (Or.inr (Or.inr ⟨by decide, by decide, btrueL, rfl, erBtrue⟩))
    (fun _ hb => by cases hb; exact .lambda (.lambda (.lambda .bvar)))

/-- `csucc`'s dependency entry. -/
theorem deps_csucc : ErasesDeps venv4 σ4 lenv4 (.const (toKername `URec.csucc)) :=
  .const (ci := .defnInfo csucc_val) rfl look_csucc
    (Or.inr (Or.inr ⟨by decide, by decide, csuccL, rfl, erCsucc⟩))
    (fun _ hb => by
      cases hb
      exact .lambda (.lambda (.lambda (.lambda (.app .bvar (.app (.app (.app .bvar .box) .bvar)
        .bvar))))))

/-- An erased member's dependencies are erased when its call target's are. -/
theorem deps_memberL {r : LBTerm} (hr : ErasesDeps venv4 σ4 lenv4 r) :
    ErasesDeps venv4 σ4 lenv4 (memberL r) :=
  .lambda (.lambda (.app (.app (.app (.app .bvar .box) (.lambda .bvar))
    (.lambda (.app (.app hr deps_btrue) (.app deps_csucc .bvar)))) .bvar))

/-- The block's bodies have erased dependencies. -/
theorem deps_defs : ∀ d ∈ defs4, ErasesDeps venv4 σ4 lenv4 d.body := by
  intro d hd
  simp only [defs4, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> exact deps_memberL .bvar

/-- `ua`'s dependency entry: its fixpoint. -/
theorem deps_ua : ErasesDeps venv4 σ4 lenv4 (.const (toKername `URec.ua)) :=
  .const (ci := .defnInfo ua_val) rfl look_ua decl_ua
    (fun _ hb => by cases hb; exact .fix deps_defs)

/-- `e4` erases to `t4`: `ua` to its kername (`Erases.const`), not to its fixpoint. The
hypothesis `her` of `erases_correct` on NV-4. Reference: the hypothesis `Σ;;; [] |- t ⇝ℇ t'` of
`erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] e4 t4 :=
  .app (.app (.const atom_ua) (.const atom_bfalse)) (.const atom_one)

/-- `t4`'s dependencies `ua` (with the block), `bfalse` and `one` are erased in `lenv4`: the
hypothesis `hdeps` of `erases_correct` on NV-4. Reference: the hypothesis `erases_deps Σ Σ' t'`
of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps venv4 σ4 lenv4 t4 :=
  .app
    (.app deps_ua
      (.const (ci := .defnInfo bfalse_val) rfl look_bfalse
        (Or.inr (Or.inr ⟨by decide, by decide, bfalseL, rfl, erBfalse⟩))
        (fun _ hb => by cases hb; exact .lambda (.lambda (.lambda .bvar)))))
    (.const (ci := .defnInfo one_val) rfl look_one
      (Or.inr (Or.inr ⟨by decide, by decide, oneL, rfl, erOne rfl⟩))
      (fun _ hb => by cases hb; exact .lambda (.lambda (.lambda (.app .bvar .bvar)))))

/-- The fixpoints stored for `ua` and `ub` are the erased block: the hypothesis `hblocks` of
`erases_correct` on NV-4. -/
theorem hblocks : BlocksErased venv4 σ4 lenv4 := by
  intro c ci ds i hfd hl
  have hs : (findDecl decls4 c).isSome = true := by
    have h := hfd; simp only [σ4, evalEnvOf] at h; rw [h]; rfl
  rcases mem_names hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show findDecl σ4.decls `URec.ub = some (.defnInfo ub_val) from rfl] at hfd
    cases hfd
    rw [look_ub] at hl; cases hl
    exact ⟨decl_ub, deps_defs⟩
  · rw [show findDecl σ4.decls `URec.ua = some (.defnInfo ua_val) from rfl] at hfd
    cases hfd
    rw [look_ua] at hl; cases hl
    exact ⟨decl_ua, deps_defs⟩
  · rw [look_bfalse] at hl; cases hl
  · rw [look_btrue] at hl; cases hl
  · rw [look_CB] at hl; cases hl
  · rw [look_csucc] at hl; cases hl
  · rw [look_one] at hl; cases hl
  · rw [look_CN] at hl; cases hl

/-! ## The instance and its conclusion -/

/-- `ua bfalse` evaluates, by `LBEval.fix` (`ua` is `fix defs4 0`), to the λ that selects on
`bfalse`. -/
theorem lb_ua_bfalse :
    LBEval defaultFlags lenv4 (.app (.const (toKername `URec.ua)) (.const (toKername `URec.bfalse)))
      (.lambda (binderNameOf `n) (appSelL bfalseL (.bvar 0) (.fix defs4 1))) :=
  .fix (argsv := []) rfl (.delta look_ua rfl (.atom rfl)) (.delta look_bfalse rfl (.atom rfl))
    cunfold_ua (.beta (.atom rfl) (.atom rfl) (.atom rfl))

/-- `fix defs4 1 btrue` evaluates, by `LBEval.fix`, to the λ that selects on `btrue`. -/
theorem lb_ub_btrue :
    LBEval defaultFlags lenv4 (.app (.fix defs4 1) (.const (toKername `URec.btrue)))
      (.lambda (binderNameOf `n) (appSelL btrueL (.bvar 0) (.fix defs4 0))) :=
  .fix (argsv := []) rfl (.atom rfl) (.delta look_btrue rfl (.atom rfl)) cunfold_ub
    (.beta (.atom rfl) (.atom rfl) (.atom rfl))

/-- The erased `bfalse` selects its second branch. -/
theorem lb_sel_false :
    LBEval defaultFlags lenv4 (.app (.app (.app bfalseL .box) idL) (callL (.fix defs4 1)))
      (callL (.fix defs4 1)) :=
  .beta (.beta (.beta (.atom rfl) (.atom rfl) (.atom rfl)) (.atom rfl) (.atom rfl)) (.atom rfl)
    (.atom rfl)

/-- The erased `btrue` selects its first branch. -/
theorem lb_sel_true :
    LBEval defaultFlags lenv4 (.app (.app (.app btrueL .box) idL) (callL (.fix defs4 0))) idL :=
  .beta (.beta (.beta (.atom rfl) (.atom rfl) (.atom rfl)) (.atom rfl) (.atom rfl)) (.atom rfl)
    (.atom rfl)

/-- `csucc one'` evaluates, by δ and β, to `v4'`. -/
theorem lb_csucc : LBEval defaultFlags lenv4 (.app (.const (toKername `URec.csucc)) oneL) v4' :=
  .beta (.delta look_csucc rfl (.atom rfl)) (.atom rfl) (.atom rfl)

/-- `t4` evaluates to `v4'` in `lenv4`: `LBEval.fix` on `ua`, then on `ub`, δ and β. -/
theorem lbev : LBEval defaultFlags lenv4 t4 v4' :=
  .beta lb_ua_bfalse (.delta look_one rfl (.atom rfl))
    (.beta lb_sel_false (.atom rfl)
      (.beta lb_ub_btrue lb_csucc (.beta lb_sel_true (.atom rfl) (.atom rfl))))

/-- `v4` erases to `v4'`. -/
theorem herv : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] v4 v4' :=
  erSuccBody rfl (erOne rfl)

/-- `erases_correct` on NV-4: every hypothesis is a checked term. Reference: `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem inst : ∃ v', Erases venv4 [] σ4.isAtom (RecIn lenv4) [] v4 v' ∧
    LBEval defaultFlags lenv4 t4 v' :=
  erases_correct henv hsub hinj hlc he her hdeps hblocks hev

/-- The conclusion of `erases_correct` on NV-4 holds with the non-`□` witness `v4'`. -/
theorem concl : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] v4 v4' ∧
    LBEval defaultFlags lenv4 t4 v4' :=
  ⟨herv, lbev⟩

/-- Every witness of `erases_correct` on NV-4 is `v4'`, a λ: λ□ evaluation is deterministic and
`t4` evaluates to `v4'` (`lbev`). Reference: `eval_deterministic`
(`MR erasure/theories/EWcbvEval.v:1375`). -/
theorem witness {v' : LBTerm} (h : Erases venv4 [] σ4.isAtom (RecIn lenv4) [] v4 v' ∧
    LBEval defaultFlags lenv4 t4 v') : v' = v4' :=
  LBEval.deterministic h.2 lbev

end EraseProof.Test.NV4
