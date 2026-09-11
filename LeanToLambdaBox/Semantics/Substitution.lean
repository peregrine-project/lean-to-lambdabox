import LeanToLambdaBox.Basic

/-!
# de Bruijn substitution kit for λ□ terms

The environment lookup (`LBTerm.envLookup`) and the shift/substitution operations on
`LBTerm`, shared by every layer that reasons about λ□ reduction. Also here: the
application-spine helpers (`LBTerm.mkApps`, `LBTerm.spineHead`, `LBTerm.spineArgs`),
the fixpoint-unfolding substitution `LBTerm.fixSubst`, the lambda telescope
`mkLambdas` with its two commutation laws, the data-oriented recursor
`LBTerm.recData`, and the six `List.map` forms of the hand-rolled list traversals
(`LBTerm.shiftArgs_eq_map` and its siblings) that every `LBTerm.recData` induction
needs in its `hconstruct`/`hcase`/`hfix` arm.

The conventions here **match lean4lean's `Expr.liftLooseBVars'`/`instantiate1'`**
(`shift d cutoff ≡ liftLooseBVars' · cutoff d`, `subst ≡ instantiate1'`), which is
what lines the source and target de Bruijn operations up. Preserve them.
-/

/-- Structural boolean equality of module paths. `ModPath`/`Kername` derive only
    `Repr`/`Inhabited` in `Basic.lean`, so we supply the comparison locally (rather
    than editing the shared `Basic.lean`). -/
def ModPath.beq : ModPath → ModPath → Bool
  | .MPfile dp1, .MPfile dp2 => dp1 == dp2
  | .MPdot mp1 s1, .MPdot mp2 s2 => ModPath.beq mp1 mp2 && s1 == s2
  | _, _ => false

/-- Structural boolean equality of kernames — the **full** kername (modpath ×
    identifier), matching MetaRocq's `eq_kername`/`lookup_env` (which compare the
    whole kername, not just the identifier component). -/
def Kername.beq (k1 k2 : Kername) : Bool := k1.mp.beq k2.mp && k1.id == k2.id

namespace LBTerm

/-- Look up a declaration in a `GlobalDeclarations` list. Linear scan; fine for the
    scaffolding, the list is logically a finite map.

    Compares the **full** kername (modpath × id) via `Kername.beq`, matching
    MetaRocq's `lookup_env` (which uses `eq_kername`). -/
def envLookup : GlobalDeclarations → Kername → Option GlobalDecl
  | [], _ => none
  | (k, d) :: rest, kn => if Kername.beq k kn then some d else envLookup rest kn

/-! ### Shift / subst (mutual recursion with explicit list helpers).

We deliberately avoid `List.map` inside the principal recursive functions: the
structural-recursion checker cannot see through `map` for nested inductives,
so we factor the per-list traversals out into dedicated mutually-recursive
helpers. -/

mutual
/-- Shift de Bruijn indices ≥ `cutoff` up by `d`. -/
def shift (d cutoff : Nat) : LBTerm → LBTerm
  | bvar i => if i ≥ cutoff then bvar (i + d) else bvar i
  | lambda n b => lambda n (shift d (cutoff + 1) b)
  | letIn n v b => letIn n (shift d cutoff v) (shift d (cutoff + 1) b)
  | app f a => app (shift d cutoff f) (shift d cutoff a)
  | construct ind k args => construct ind k (shiftArgs d cutoff args)
  | case info scr alts => case info (shift d cutoff scr) (shiftAlts d cutoff alts)
  | proj p e => proj p (shift d cutoff e)
  | fix defs i => fix (shiftDefs d (cutoff + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def shiftArgs (d cutoff : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => shift d cutoff t :: shiftArgs d cutoff rest

def shiftAlts (d cutoff : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, shift d (cutoff + ns.length) b) :: shiftAlts d cutoff rest

def shiftDefs (d cutoff : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := shift d cutoff fd.body } :: shiftDefs d cutoff rest
end

mutual
/-- Substitute `s` for the bound variable at depth `d`, decrementing higher indices. -/
def subst (s : LBTerm) (d : Nat) : LBTerm → LBTerm
  | bvar i =>
    if i < d then bvar i
    else if i = d then shift d 0 s
    else bvar (i - 1)
  | lambda n b => lambda n (subst s (d + 1) b)
  | letIn n v b => letIn n (subst s d v) (subst s (d + 1) b)
  | app f a => app (subst s d f) (subst s d a)
  | construct ind k args => construct ind k (substArgs s d args)
  | case info scr alts => case info (subst s d scr) (substAlts s d alts)
  | proj p e => proj p (subst s d e)
  | fix defs i => fix (substDefs s (d + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def substArgs (s : LBTerm) (d : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => subst s d t :: substArgs s d rest

def substAlts (s : LBTerm) (d : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, subst s (d + ns.length) b) :: substAlts s d rest

def substDefs (s : LBTerm) (d : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := subst s d fd.body } :: substDefs s d rest
end

/-- Substitute the bvar 0 only. -/
@[inline] def subst1 (s : LBTerm) (t : LBTerm) : LBTerm := subst s 0 t

/--
Simultaneous substitution of `ss` for de Bruijn indices `0 .. ss.length - 1`.
Implemented by sequencing `subst1` applications: substituting `ss[0]` first
reduces every higher index by one, which is exactly what we want before
substituting `ss[1]` into position 0, and so on.
-/
def substList (ss : List LBTerm) (t : LBTerm) : LBTerm :=
  ss.foldl (fun acc s => subst1 s acc) t

/-- Apply `f` to a list of arguments, left-to-right, building an application spine.
    `mkApps f [a₁, …, aₙ] = (…((f a₁) a₂)… aₙ)`. MetaRocq's `mkApps`; the shape of
    non-block constructor and applied-`fix` **values**. -/
def mkApps (f : LBTerm) : List LBTerm → LBTerm
  | [] => f
  | a :: rest => mkApps (app f a) rest

/-- The head of an application spine (peel every `.app`). MetaRocq `EAstUtils.head`.
    `spineHead (mkApps f args) = spineHead f`. -/
def spineHead : LBTerm → LBTerm
  | app f _ => spineHead f
  | t => t

/-- The argument list of an application spine (in order). `spineArgs (mkApps f args)
    = spineArgs f ++ args`; together with `spineHead` this recovers a spine's shape,
    giving `mkApps` injectivity for non-application heads. -/
def spineArgs : LBTerm → List LBTerm
  | app f a => spineArgs f ++ [a]
  | _ => []

@[simp] theorem mkApps_nil (f : LBTerm) : mkApps f [] = f := rfl

theorem mkApps_concat (f : LBTerm) (args : List LBTerm) (a : LBTerm) :
    mkApps f (args ++ [a]) = app (mkApps f args) a := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => simpa [mkApps] using ih (app f x)

theorem spineHead_mkApps (f : LBTerm) (args : List LBTerm) :
    spineHead (mkApps f args) = spineHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => rw [mkApps, ih (app f x)]; rfl

theorem spineArgs_mkApps (f : LBTerm) (args : List LBTerm) :
    spineArgs (mkApps f args) = spineArgs f ++ args := by
  induction args generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [mkApps, ih (app f x)]
    simp [spineArgs]

@[simp] theorem spineHead_lambda (n : BinderName) (b : LBTerm) :
    spineHead (lambda n b) = lambda n b := rfl
@[simp] theorem spineHead_box : spineHead box = box := rfl
@[simp] theorem spineHead_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    spineHead (construct iid c args) = construct iid c args := rfl
@[simp] theorem spineArgs_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    spineArgs (construct iid c args) = [] := rfl
@[simp] theorem spineHead_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    spineHead (fix defs i) = fix defs i := rfl
@[simp] theorem spineArgs_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    spineArgs (fix defs i) = [] := rfl

/-- Injectivity of a constructor-headed application spine: the constructor and the
    argument list are recoverable. -/
theorem mkApps_construct_inj {iid iid' : InductiveId} {c c' : Nat}
    {args args' : List LBTerm}
    (h : mkApps (construct iid c []) args = mkApps (construct iid' c' []) args') :
    iid = iid' ∧ c = c' ∧ args = args' := by
  have ha : args = args' := by
    have := congrArg spineArgs h
    rwa [spineArgs_mkApps, spineArgs_mkApps, spineArgs_construct, spineArgs_construct,
      List.nil_append, List.nil_append] at this
  subst ha
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_construct, spineHead_construct] at this
  injection this with h1 h2 _
  exact ⟨h1, h2, rfl⟩

/-- Injectivity of a `fix`-headed application spine. -/
theorem mkApps_fix_inj {defs defs' : List (@FixDef LBTerm)} {i i' : Nat}
    {argsv argsv' : List LBTerm}
    (h : mkApps (fix defs i) argsv = mkApps (fix defs' i') argsv') :
    defs = defs' ∧ i = i' ∧ argsv = argsv' := by
  have ha : argsv = argsv' := by
    have := congrArg spineArgs h
    rwa [spineArgs_mkApps, spineArgs_mkApps, spineArgs_fix, spineArgs_fix,
      List.nil_append, List.nil_append] at this
  subst ha
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_fix, spineHead_fix] at this
  injection this with h1 h2
  exact ⟨h1, h2, rfl⟩

/-- A constructor-headed spine is never a `fix`-headed spine. -/
theorem mkApps_construct_ne_fix {iid : InductiveId} {c : Nat}
    {defs : List (@FixDef LBTerm)} {i : Nat} {args argsv : List LBTerm} :
    mkApps (construct iid c []) args ≠ mkApps (fix defs i) argsv := by
  intro h
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_construct, spineHead_fix] at this
  exact LBTerm.noConfusion this

/-- The fixpoint-unfolding substitution. MetaRocq
    `fix_subst l = [tFix l (n-1); …; tFix l 1; tFix l 0]` (with `n = |l|`), i.e.
    index `i ↦ tFix l (n-1-i)`. Used by `cunfold_fix`; only differs from the naïve
    `[tFix l 0; …; tFix l (n-1)]` for mutual blocks (`n ≥ 2`), but the order is
    load-bearing for correctness. -/
def fixSubst (defs : List (@FixDef LBTerm)) : List LBTerm :=
  (List.range defs.length).reverse.map (fun j => LBTerm.fix defs j)


/-! ### A data-oriented recursor, and the list traversals in `List.map` form -/

/-- A `Prop`-motive recursor for `LBTerm` handing per-list membership induction
hypotheses rather than raw nested-inductive motives. `LBTerm` is a nested inductive
(lists of subterms inside `construct`/`case`/`fix`), so plain `induction t` is rejected;
this eliminator's list-carrying arms give back `∀ x ∈ l, P x`. -/
@[elab_as_elim]
def recData
    {P : LBTerm → Prop}
    (hbox : P .box)
    (hbvar : ∀ i, P (.bvar i))
    (hfvar : ∀ x, P (.fvar x))
    (hlam : ∀ n b, P b → P (.lambda n b))
    (hletIn : ∀ n v b, P v → P b → P (.letIn n v b))
    (happ : ∀ f a, P f → P a → P (.app f a))
    (hconst : ∀ kn, P (.const kn))
    (hconstruct : ∀ iid k args, (∀ x ∈ args, P x) → P (.construct iid k args))
    (hcase : ∀ info discr alts, P discr → (∀ a ∈ alts, P a.2) → P (.case info discr alts))
    (hproj : ∀ p e, P e → P (.proj p e))
    (hfix : ∀ defs i, (∀ d ∈ defs, P d.body) → P (.fix defs i))
    (hprim : ∀ p, P (.prim p)) :
    ∀ t, P t := by
  refine fun t => LBTerm.rec
    (motive_1 := P)
    (motive_2 := fun l => ∀ x ∈ l, P x)
    (motive_3 := fun l => ∀ a ∈ l, P a.2)
    (motive_4 := fun l => ∀ d ∈ l, P d.body)
    (motive_5 := fun (a : List BinderName × LBTerm) => P a.2)
    (motive_6 := fun (d : @FixDef LBTerm) => P d.body)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  case _ => exact hbox
  case _ => exact hbvar
  case _ => exact hfvar
  case _ => exact fun n b ih => hlam n b ih
  case _ => exact fun n v b ihv ihb => hletIn n v b ihv ihb
  case _ => exact fun f a ihf iha => happ f a ihf iha
  case _ => exact hconst
  case _ => exact fun iid k args ih => hconstruct iid k args ih
  case _ => exact fun info discr alts ihd iha => hcase info discr alts ihd iha
  case _ => exact fun p e ih => hproj p e ih
  case _ => exact fun defs i ih => hfix defs i ih
  case _ => exact hprim
  case _ => exact List.forall_mem_nil _
  case _ => exact fun t l iht ihl => List.forall_mem_cons.mpr ⟨iht, ihl⟩
  case _ => exact List.forall_mem_nil _
  case _ => exact fun a l iha ihl => List.forall_mem_cons.mpr ⟨iha, ihl⟩
  case _ => exact List.forall_mem_nil _
  case _ => exact fun d l ihd ihl => List.forall_mem_cons.mpr ⟨ihd, ihl⟩
  case _ => exact fun _ snd ih => ih
  case _ => exact fun _ _ _ ih => ih


/-- `shiftArgs` as a `List.map`. -/
theorem shiftArgs_eq_map (d c : Nat) (l : List LBTerm) :
    LBTerm.shiftArgs d c l = l.map (LBTerm.shift d c) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.shiftArgs, List.map, ih]

/-- `substArgs` as a `List.map`. -/
theorem substArgs_eq_map (s : LBTerm) (d : Nat) (l : List LBTerm) :
    LBTerm.substArgs s d l = l.map (LBTerm.subst s d) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.substArgs, List.map, ih]

/-- `shiftAlts` as a `List.map`; the shift cutoff of a branch body is offset by the
branch's own field binders. -/
theorem shiftAlts_eq_map (d c : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.shiftAlts d c l = l.map (fun a => (a.1, LBTerm.shift d (c + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.shiftAlts, List.map, ih]

/-- `substAlts` as a `List.map`; the substitution depth of a branch body is offset by the
branch's own field binders. -/
theorem substAlts_eq_map (s : LBTerm) (d : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.substAlts s d l = l.map (fun a => (a.1, LBTerm.subst s (d + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.substAlts, List.map, ih]

/-- `shiftDefs` as a `List.map`; a mutual block's bodies already live under their own
binders, so the cutoff does not move. -/
theorem shiftDefs_eq_map (d c : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.shiftDefs d c l = l.map (fun fd => { fd with body := LBTerm.shift d c fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.shiftDefs, List.map, ih]

/-- `substDefs` as a `List.map`; a mutual block's bodies already live under their own
binders, so the depth does not move. -/
theorem substDefs_eq_map (s : LBTerm) (d : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.substDefs s d l = l.map (fun fd => { fd with body := LBTerm.subst s d fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.substDefs, List.map, ih]

end LBTerm

namespace LeanToLambdaBox

/-! ### Lambda telescopes -/

/-- Wrap a body in a chain of lambdas, outermost binder first:
`mkLambdas [n₁, …, nₖ] body = .lambda n₁ (… (.lambda nₖ body))`. The shape a `case`
alternative's `(field-names, body)` pair takes when read back as a minor function. -/
def mkLambdas : List BinderName → LBTerm → LBTerm
  | [], body => body
  | n :: ns, body => .lambda n (mkLambdas ns body)

/-- `shift` pushes into a lambda telescope, its cutoff raised by the telescope's length. -/
theorem shift_mkLambdas (d c : Nat) (names : List BinderName) (body : LBTerm) :
    LBTerm.shift d c (mkLambdas names body)
      = mkLambdas names (LBTerm.shift d (c + names.length) body) := by
  induction names generalizing c with
  | nil => rfl
  | cons n ns ih =>
      have h : c + (ns.length + 1) = (c + 1) + ns.length := by omega
      simp only [mkLambdas, LBTerm.shift, List.length_cons, h, ih]

/-- `subst` pushes into a lambda telescope, its depth raised by the telescope's length. -/
theorem subst_mkLambdas (s : LBTerm) (d : Nat) (names : List BinderName) (body : LBTerm) :
    LBTerm.subst s d (mkLambdas names body)
      = mkLambdas names (LBTerm.subst s (d + names.length) body) := by
  induction names generalizing d with
  | nil => rfl
  | cons n ns ih =>
      have h : d + (ns.length + 1) = (d + 1) + ns.length := by omega
      simp only [mkLambdas, LBTerm.subst, List.length_cons, h, ih]

end LeanToLambdaBox
