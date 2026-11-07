import EraseProof.Test.NVRData

/-!
# NV-S: the program

    inductive N | z | s (n : N)
    def add (n m : N) : N :=
      match m with
      | .z => n
      | .s k => .s (add n k)
    #erase add (N.s N.z) (N.s N.z) config {structural := .kernel}   -- evaluates to N.s (N.s N.z)

`N` is NV-R's `inductive N | z | s (n : N)`. `add` is defined by structural recursion on its
second argument: Lean's elaborator (`Lean.Elab.Structural`) writes its kernel definition through
`N.brecOn`, whose value is the first projection of `N.brecOn.go`, a `N.rec` into the pairs
(`PProd`) of a value and its table of recursive calls `N.below` (a `N.rec` into `Sort`, of
`PUnit` and `PProd`); the body is `add._f`, which matches with `add.match_1` (a `N.casesOn`) and
reads the recursive call as the first projection of the table. The declarations as Lean
v4.35.0-rc2 generates them (`tools/NVEmit.lean` elaborates the source above and checks them
against the environment's), newest first:
`P = [add, add._f, add.match_1, N.brecOn, N.brecOn.go, N.below, N.casesOn, N.rec, N.z, N.s, N,
PProd.rec, PProd.mk, PProd, Unit.unit, Unit, PUnit.rec, PUnit.unit, PUnit]` (the dependency closure
of the term, `Init`'s `PUnit`, `Unit` and `PProd` included); the term `e`; the view `#erase` reads
(`P` as a list; `@[inline]` on `add.match_1`, as on every matcher, and on the abbreviations
`Unit` and `Unit.unit`; the compiled companion `add._unsafe_rec` is not in it); the configuration
`structural := .kernel`. Toward a non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) through the kernel definitions of
structural recursion: `Test/NVSRun.lean` discharges its hypotheses `hfrag` and `hrun`.
-/

open Lean Erasure

namespace EraseProof.Test.NVS

open EraseProof.Test.NVR (tN cZ cS N_ind Nz_ctor Ns_ctor N_rec motTy mj)

/-- A hygienic binder name of the elaborated definitions, `x._@.2314059840._hygCtx._hyg.k`
(macro scopes of the elaboration that `tools/NVEmit.lean` runs). -/
def hyg (x : String) (k : Nat) : Name :=
  .mkNum (.mkStr (.mkStr (.mkNum (.mkStr (.mkStr .anonymous x) "_@") 2314059840) "_hygCtx") "_hyg") k

def uu : Level := .param `u
def uv : Level := .param `v
def u1 : Level := .param `u_1
def l1 : Level := .succ .zero
/-- `max 1 u` -/
def m1u : Level := .max l1 uu

/-! ## `PUnit.{u} : Sort u` (`Init.Prelude`) -/

def tPU (l : Level) : Expr := .const `PUnit [l]
def cPU (l : Level) : Expr := .const `PUnit.unit [l]

def PUnit_ind : InductiveVal :=
  { name := `PUnit, levelParams := [`u], type := .sort uu, numParams := 0, numIndices := 0,
    all := [`PUnit], ctors := [`PUnit.unit], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }

def PUnit_unit : ConstructorVal :=
  { name := `PUnit.unit, levelParams := [`u], type := tPU uu, induct := `PUnit, cidx := 0,
    numParams := 0, numFields := 0, isUnsafe := false }

/-- `(t : PUnit.{u}) → Sort u_1` -/
def puMotTy : Expr := .forallE `t (tPU uu) (.sort u1) .default

/-- The rule's right-hand side `fun motive unit => unit`. -/
def puRhs : Expr :=
  .lam `motive puMotTy (.lam `unit (.app (.bvar 0) (cPU uu)) (.bvar 0) .default) .default

def PUnit_rec : RecursorVal :=
  { name := `PUnit.rec, levelParams := [`u_1, `u],
    type := .forallE `motive puMotTy
      (.forallE `unit (.app (.bvar 0) (cPU uu))
        (.forallE `t (tPU uu) (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit,
    all := [`PUnit], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `PUnit.unit, nfields := 0, rhs := puRhs }],
    k := false, isUnsafe := false }

/-! ## `Unit := PUnit.{1}`, `Unit.unit := PUnit.unit.{1}` (`Init.Prelude`) -/

def tUnit : Expr := .const `Unit []

def Unit_def : DefinitionVal :=
  { name := `Unit, levelParams := [], type := .sort l1, value := tPU l1, hints := .abbrev,
    safety := .safe, all := [`Unit] }

def Unit_unit : DefinitionVal :=
  { name := `Unit.unit, levelParams := [], type := tUnit, value := cPU l1, hints := .abbrev,
    safety := .safe, all := [`Unit.unit] }

/-! ## `PProd.{u, v} (α : Sort u) (β : Sort v) : Sort (max (max 1 u) v)` (`Init.Prelude`) -/

def tPP (a b : Level) : Expr := .const `PProd [a, b]
def cPP (a b : Level) : Expr := .const `PProd.mk [a, b]

def PProd_ind : InductiveVal :=
  { name := `PProd, levelParams := [`u, `v],
    type := .forallE `α (.sort uu) (.forallE `β (.sort uv) (.sort (.max (.max l1 uu) uv)) .default)
      .default,
    numParams := 2, numIndices := 0, all := [`PProd], ctors := [`PProd.mk], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }

def PProd_mk : ConstructorVal :=
  { name := `PProd.mk, levelParams := [`u, `v],
    type := .forallE `α (.sort uu) (.forallE `β (.sort uv) (.forallE `fst (.bvar 1)
      (.forallE `snd (.bvar 1) (.app (.app (tPP uu uv) (.bvar 3)) (.bvar 2)) .default) .default)
      .implicit) .implicit,
    induct := `PProd, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false }

/-- `(t : PProd α β) → Sort u_1`, under `α β`. -/
def ppMotTy : Expr := .forallE `t (.app (.app (tPP uu uv) (.bvar 1)) (.bvar 0)) (.sort u1) .default

/-- `(fst : α) → (snd : β) → motive ⟨fst, snd⟩`, under `α β motive`. -/
def ppMinTy : Expr :=
  .forallE `fst (.bvar 2) (.forallE `snd (.bvar 2)
    (.app (.bvar 2) (.app (.app (.app (.app (cPP uu uv) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0)))
    .default) .default

/-- The rule's right-hand side `fun α β motive mk fst snd => mk fst snd`. -/
def ppRhs : Expr :=
  .lam `α (.sort uu) (.lam `β (.sort uv) (.lam `motive ppMotTy (.lam `mk ppMinTy
    (.lam `fst (.bvar 3) (.lam `snd (.bvar 3) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      .default) .default) .default) .default) .default) .default

def PProd_rec : RecursorVal :=
  { name := `PProd.rec, levelParams := [`u_1, `u, `v],
    type := .forallE `α (.sort uu) (.forallE `β (.sort uv) (.forallE `motive ppMotTy
      (.forallE `mk ppMinTy (.forallE `t (.app (.app (tPP uu uv) (.bvar 3)) (.bvar 2))
        (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit) .implicit,
    all := [`PProd], numParams := 2, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `PProd.mk, nfields := 2, rhs := ppRhs }],
    k := false, isUnsafe := false }

/-! ## `N.casesOn`, `N.below`, `N.brecOn.go`, `N.brecOn` -/

/-- `{motive : N → Sort u} → (t : N) → motive N.z → ((n : N) → motive (N.s n)) → motive t` -/
def casesOnTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `z (.app (.bvar 1) cZ)
    (.forallE `s (.forallE `n tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
      (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .implicit

/-- `fun {motive} t z s => @N.rec motive z (fun n n_ih => s n) t` -/
def casesOnVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `z (.app (.bvar 1) cZ)
    (.lam `s (.forallE `n tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
      (.app (.app (.app (.app (.const `N.rec [uu]) (.bvar 3)) (.bvar 1))
        (.lam `n tN (.lam `n_ih (.app (.bvar 4) (.bvar 0)) (.app (.bvar 2) (.bvar 1)) .default)
          .default)) (.bvar 2)) .default) .default) .default) .implicit

def N_casesOn : DefinitionVal :=
  { name := `N.casesOn, levelParams := [`u], type := casesOnTy, value := casesOnVal,
    hints := .abbrev, safety := .safe, all := [`N.casesOn] }

/-- `N.below.{l}` -/
def below (l : Level) : Expr := .const `N.below [l]

/-- `{motive : N → Sort u} → N → Sort (max 1 u)` -/
def belowTy : Expr := .forallE `motive motTy (.forallE `t tN (.sort m1u) .default) .implicit

/-- `fun {motive} t => @N.rec.{max 1 u + 1} (fun t => Sort (max 1 u)) PUnit
(fun n n_ih => PProd (motive n) n_ih) t` -/
def belowVal : Expr :=
  .lam `motive motTy (.lam `t tN
    (.app (.app (.app (.app (.const `N.rec [.succ m1u]) (.lam `t tN (.sort m1u) .default))
      (tPU m1u))
      (.lam `n tN (.lam `n_ih (.sort m1u) (.app (.app (tPP uu m1u) (.app (.bvar 3) (.bvar 1)))
        (.bvar 0)) .default) .default)) (.bvar 0)) .default) .implicit

def N_below : DefinitionVal :=
  { name := `N.below, levelParams := [`u], type := belowTy, value := belowVal, hints := .abbrev,
    safety := .safe, all := [`N.below] }

/-- `(t : N) → N.below motive t → motive t`, under `motive t`. -/
def F1Ty : Expr :=
  .forallE `t tN (.forallE `f (.app (.app (below uu) (.bvar 2)) (.bvar 0)) (.app (.bvar 3) (.bvar 1))
    .default) .default

/-- `PProd (motive t) (N.below motive t)`, `motive` and `t` the variables `mo` and `t`. -/
def pairTy (mo t : Nat) : Expr :=
  .app (.app (tPP uu m1u) (.app (.bvar mo) (.bvar t))) (.app (.app (below uu) (.bvar mo)) (.bvar t))

/-- `{motive : N → Sort u} → (t : N) → (F_1 : (t : N) → N.below motive t → motive t) →
PProd (motive t) (N.below motive t)` -/
def goTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `F_1 F1Ty (pairTy 2 1) .default) .default)
    .implicit

/-- `fun {motive} t F_1 => @N.rec.{max 1 u} (fun t => PProd (motive t) (N.below motive t))
⟨F_1 N.z PUnit.unit, PUnit.unit⟩ (fun n n_ih => ⟨F_1 (N.s n) n_ih, n_ih⟩) t` -/
def goVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `F_1 F1Ty
    (.app (.app (.app (.app (.const `N.rec [m1u]) (.lam `t tN (pairTy 3 0) .default))
      (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 2) cZ)) (tPU m1u))
        (.app (.app (.bvar 0) cZ) (cPU m1u))) (cPU m1u)))
      (.lam `n tN (.lam `n_ih (pairTy 3 0)
        (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 4) (.app cS (.bvar 1)))) (pairTy 4 1))
          (.app (.app (.bvar 2) (.app cS (.bvar 1))) (.bvar 0))) (.bvar 0)) .default) .default))
      (.bvar 1)) .default) .default) .implicit

def N_brecOn_go : DefinitionVal :=
  { name := `N.brecOn.go, levelParams := [`u], type := goTy, value := goVal, hints := .abbrev,
    safety := .safe, all := [`N.brecOn.go] }

/-- `{motive : N → Sort u} → (t : N) → (F_1 : (t : N) → N.below motive t → motive t) → motive t` -/
def brecOnTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `F_1 F1Ty (.app (.bvar 2) (.bvar 1)) .default)
    .default) .implicit

/-- `fun {motive} t F_1 => (N.brecOn.go motive t F_1).1` -/
def brecOnVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `F_1 F1Ty
    (.proj `PProd 0 (.app (.app (.app (.const `N.brecOn.go [uu]) (.bvar 2)) (.bvar 1)) (.bvar 0)))
    .default) .default) .implicit

def N_brecOn : DefinitionVal :=
  { name := `N.brecOn, levelParams := [`u], type := brecOnTy, value := brecOnVal,
    hints := .abbrev, safety := .safe, all := [`N.brecOn] }

/-! ## `add.match_1`, `add._f`, `add` -/

/-- `(m : N) → Sort u_1` -/
def mMotTy : Expr := .forallE (hyg "m" 8) tN (.sort u1) .default

/-- `(motive : N → Sort u_1) → (m : N) → (Unit → motive N.z) → ((k : N) → motive (N.s k)) →
motive m` -/
def matchTy : Expr :=
  .forallE `motive mMotTy (.forallE (hyg "m" 8) tN
    (.forallE `h_1 (.forallE `_ tUnit (.app (.bvar 2) cZ) .default)
      (.forallE `h_2 (.forallE `k tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
        (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .default

/-- `fun motive m h_1 h_2 => N.casesOn (fun x => motive x) m (h_1 Unit.unit) (fun n => h_2 n)` -/
def matchVal : Expr :=
  .lam `motive mMotTy (.lam (hyg "m" 8) tN
    (.lam `h_1 (.forallE `_ tUnit (.app (.bvar 2) cZ) .default)
      (.lam `h_2 (.forallE `k tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
        (.app (.app (.app (.app (.const `N.casesOn [u1]) (.lam `x tN (.app (.bvar 4) (.bvar 0)) .default))
          (.bvar 2)) (.app (.bvar 1) (.const `Unit.unit [])))
          (.lam (hyg "n" 22) tN (.app (.bvar 1) (.bvar 0)) .default)) .default) .default) .default)
    .default

def add_match_1 : DefinitionVal :=
  { name := `add.match_1, levelParams := [`u_1], type := matchTy, value := matchVal,
    hints := .abbrev, safety := .safe, all := [`add.match_1] }

/-- The motive `fun m => N` of `add`'s structural recursion. -/
def motN : Expr := .lam `m tN tN .default

/-- `N.below.{1} (fun m => N) x` -/
def belowN (x : Expr) : Expr := .app (.app (below l1) motN) x

/-- `(n m : N) → N.below (fun m => N) m → N` -/
def fTy : Expr := .forallE `n tN (.forallE `m tN (.forallE `f (belowN (.bvar 0)) tN .default) .default)
  .default

/-- `fun n m f => add.match_1 (fun m => N.below (fun m => N) m → N) m (fun _ x => n)
(fun k x => N.s x.1) f` -/
def fVal : Expr :=
  .lam `n tN (.lam `m tN (.lam `f (belowN (.bvar 0))
    (.app (.app (.app (.app (.app (.const `add.match_1 [l1])
      (.lam (hyg "m" 8) tN (.forallE (hyg "x" 23) (belowN (.bvar 0)) tN .default) .default))
      (.bvar 1))
      (.lam `_ tUnit (.lam (hyg "x" 23) (belowN cZ) (.bvar 4) .default) .default))
      (.lam `k tN (.lam (hyg "x" 23) (belowN (.app cS (.bvar 0)))
        (.app cS (.proj `PProd 0 (.bvar 0))) .default) .default)) (.bvar 0)) .default) .default)
    .default

def add_f : DefinitionVal :=
  { name := `add._f, levelParams := [], type := fTy, value := fVal, hints := .abbrev,
    safety := .safe, all := [`add._f] }

/-- `(n m : N) → N` -/
def addTy : Expr := .forallE `n tN (.forallE `m tN tN .default) .default

/-- `fun n m => N.brecOn.{1} (fun m => N) m (add._f n)` -/
def addVal : Expr :=
  .lam `n tN (.lam `m tN (.app (.app (.app (.const `N.brecOn [l1]) motN) (.bvar 0))
    (.app (.const `add._f []) (.bvar 1))) .default) .default

def add_def : DefinitionVal :=
  { name := `add, levelParams := [], type := addTy, value := addVal, hints := .regular 1,
    safety := .safe, all := [`add] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo add_def, .defnInfo add_f, .defnInfo add_match_1, .defnInfo N_brecOn,
    .defnInfo N_brecOn_go, .defnInfo N_below, .defnInfo N_casesOn,
    .recInfo N_rec, .ctorInfo Nz_ctor, .ctorInfo Ns_ctor, .inductInfo N_ind,
    .recInfo PProd_rec, .ctorInfo PProd_mk, .inductInfo PProd_ind,
    .defnInfo Unit_unit, .defnInfo Unit_def,
    .recInfo PUnit_rec, .ctorInfo PUnit_unit, .inductInfo PUnit_ind]

/-- The erased term `add (N.s N.z) (N.s N.z)`. -/
def e : Expr := .app (.app (.const `add []) mj) mj

/-- The view `#erase` reads: `P` as a list, no `@[extern]` or `implemented_by` attributes,
`@[inline]` on `add.match_1`, `Unit` and `Unit.unit`, as in the environment that elaborates the
program. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? n := if n == `add.match_1 || n == `Unit || n == `Unit.unit then some .inline else none
  implementedBy? _ := none

/-- The configuration `structural := .kernel`. -/
def cfg : ErasureConfig := { structural := .kernel }

end EraseProof.Test.NVS
