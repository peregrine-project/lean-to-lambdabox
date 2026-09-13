import LeanToLambdaBox.Output

/-!
# Deciding the output boundary

`LBWfPeregrine` is a conjunction of bounded quantifiers: `OnProgram`'s `∀ kn` is a fold over
`Γ`, `SubTerm` is a structural walk, and the two saturation clauses read a spine's maximal
application depth. So the predicate has a Boolean twin, `lbWfPeregrineB`, and
`lbWfPeregrine_of_check` turns a `by decide +kernel` verdict into the structure. That is how a
concrete program supplies the capstone's `LBWfPeregrine Γ t` premise, the same way
`noBodylessRefsB` supplies `NoBodylessRefs Γ t`.

`decide` alone does not reach the predicate: `declsWf` quantifies over `LBTerm.envLookup Γ kn`
and carries no `Decidable` instance.

Two generic engines carry the twelve. `progB` checks a whole-term Boolean at the term and at
every constant body of `Γ`, and `progB_sound` is `OnProgram`'s introduction rule. `onProgramB`
is `progB` at `subtermAll p`, the walk that visits every `SubTerm` of a term, so a clause
stated as a per-node condition under `SubTerm` is discharged by reading that condition off
`subtermAll_sound` — its statement is never restated here. Six clauses are of that shape:
`constsOk`, `ctorDecl`, `casesExh`, `fixLambda`, `projDecl` and `printableNames`.

The other six have their own fold. `keysDistinctB` (`keys`) and `declsWfB` (`declsWf`) look at
`Γ` alone. `lbClosedB` (`closed`) threads a binder depth and `noBlockB` (`ctorApplied`) is a
whole-term recursion, both spent through `progB`. `ctorSatB` (`etaCtorsEnv` and `etaCtorsTm`
together) counts a constructor spine at its maximal application depth, which is what
`ConstructSpine`'s `appFn` guard demands — hence the second function `ctorSatBFn`, which walks
the function side of an application without treating a constructor found there as a spine
root.

Every definition here is **structurally** recursive. A catch-all arm recursing at the same
argument compiles by well-founded recursion, and a well-founded definition does not reduce in
the kernel: `decide +kernel` then reports the `Decidable` instance stuck rather than failing.
-/

namespace LeanToLambdaBox

/-! ## The subterm walk -/

mutual
/-- `p` holds at `t` and at every subterm of `t`. -/
def subtermAll (p : LBTerm → Bool) : LBTerm → Bool
  | .box => p .box
  | .bvar i => p (.bvar i)
  | .fvar x => p (.fvar x)
  | .const kn => p (.const kn)
  | .prim v => p (.prim v)
  | .lambda n b => p (.lambda n b) && subtermAll p b
  | .letIn n v b => p (.letIn n v b) && subtermAll p v && subtermAll p b
  | .app f a => p (.app f a) && subtermAll p f && subtermAll p a
  | .construct i k args => p (.construct i k args) && subtermAllArgs p args
  | .case ip d alts => p (.case ip d alts) && subtermAll p d && subtermAllAlts p alts
  | .proj q e => p (.proj q e) && subtermAll p e
  | .fix defs j => p (.fix defs j) && subtermAllDefs p defs

/-- `subtermAll` over a constructor's arguments. -/
def subtermAllArgs (p : LBTerm → Bool) : List LBTerm → Bool
  | [] => true
  | t :: r => subtermAll p t && subtermAllArgs p r

/-- `subtermAll` over case alternatives. -/
def subtermAllAlts (p : LBTerm → Bool) : List (List BinderName × LBTerm) → Bool
  | [] => true
  | (_, b) :: r => subtermAll p b && subtermAllAlts p r

/-- `subtermAll` over the definitions of a `.fix` block. -/
def subtermAllDefs (p : LBTerm → Bool) : List (@FixDef LBTerm) → Bool
  | [] => true
  | d :: r => subtermAll p d.body && subtermAllDefs p r
end

/-- The walk checks the root. -/
theorem subtermAll_root {p : LBTerm → Bool} : ∀ {t : LBTerm}, subtermAll p t = true → p t = true
  | .box, h | .bvar _, h | .fvar _, h | .const _, h | .prim _, h => h
  | .lambda _ _, h | .construct _ _ _, h | .proj _ _, h | .fix _ _, h => by
      simp only [subtermAll, Bool.and_eq_true] at h; exact h.1
  | .letIn _ _ _, h | .app _ _, h | .case _ _ _, h => by
      simp only [subtermAll, Bool.and_eq_true] at h; exact h.1.1

/-- The walk descends into each argument. -/
theorem subtermAllArgs_mem {p : LBTerm → Bool} : ∀ {l : List LBTerm} {x : LBTerm},
    subtermAllArgs p l = true → x ∈ l → subtermAll p x = true
  | _ :: _, x, h, hx => by
      simp only [subtermAllArgs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact subtermAllArgs_mem h.2 hx

/-- The walk descends into each branch body. -/
theorem subtermAllAlts_mem {p : LBTerm → Bool} :
    ∀ {l : List (List BinderName × LBTerm)} {ns : List BinderName} {b : LBTerm},
      subtermAllAlts p l = true → (ns, b) ∈ l → subtermAll p b = true
  | a :: _, ns, b, h, hx => by
      obtain ⟨ns', b'⟩ := a
      simp only [subtermAllAlts, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with heq | hx
      · cases heq; exact h.1
      · exact subtermAllAlts_mem h.2 hx

/-- The walk descends into each definition of a block. -/
theorem subtermAllDefs_mem {p : LBTerm → Bool} :
    ∀ {l : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
      subtermAllDefs p l = true → d ∈ l → subtermAll p d.body = true
  | _ :: _, d, h, hx => by
      simp only [subtermAllDefs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact subtermAllDefs_mem h.2 hx

/-- The walk is exactly `SubTerm`: what it checks, it checks at every subterm. -/
theorem subtermAll_sound {p : LBTerm → Bool} {t u : LBTerm}
    (h : subtermAll p t = true) (hu : SubTerm u t) : p u = true := by
  induction hu with
  | refl => exact subtermAll_root h
  | lambda _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.2
  | letInVal _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.1.2
  | letInBody _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.2
  | appFn _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.1.2
  | appArg _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.2
  | constructArg hx _ ih =>
      simp only [subtermAll, Bool.and_eq_true] at h; exact ih (subtermAllArgs_mem h.2 hx)
  | caseDiscr _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.1.2
  | caseAlt ha _ ih =>
      simp only [subtermAll, Bool.and_eq_true] at h; exact ih (subtermAllAlts_mem h.2 ha)
  | proj _ ih => simp only [subtermAll, Bool.and_eq_true] at h; exact ih h.2
  | fixBody hd _ ih =>
      simp only [subtermAll, Bool.and_eq_true] at h; exact ih (subtermAllDefs_mem h.2 hd)

/-! ## The two generic engines -/

/-- A whole-term Boolean at every constant body of `Γ`. -/
def bodiesAllB (Γ : GlobalDeclarations) (f : LBTerm → Bool) : Bool :=
  Γ.all fun q => match q.2 with
    | .constantDecl ⟨some b⟩ => f b
    | _ => true

/-- A whole-term Boolean at the emitted term and at every constant body: `OnProgram`'s
env+term split, decided. -/
def progB (Γ : GlobalDeclarations) (t : LBTerm) (f : LBTerm → Bool) : Bool :=
  f t && bodiesAllB Γ f

/-- A per-node Boolean at every subterm of the emitted term and of every constant body. -/
def onProgramB (Γ : GlobalDeclarations) (t : LBTerm) (p : LBTerm → Bool) : Bool :=
  progB Γ t (subtermAll p)

/-- A declared body is one of the bodies the fold ranges over. -/
theorem bodiesAllB_sound {Γ : GlobalDeclarations} {f : LBTerm → Bool} {kn : Kername}
    {b : LBTerm} (h : bodiesAllB Γ f = true)
    (hb : LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩)) : f b = true := by
  have := List.all_eq_true.1 h _ (envLookup_mem hb)
  simpa using this

/-- `OnProgram`'s introduction rule from a whole-term Boolean. -/
theorem progB_sound {Γ : GlobalDeclarations} {t : LBTerm} {f : LBTerm → Bool}
    {P : LBTerm → Prop} (hf : ∀ u, f u = true → P u) (h : progB Γ t f = true) :
    OnProgram Γ t P := by
  simp only [progB, Bool.and_eq_true] at h
  exact ⟨hf t h.1, fun _ b hb => hf b (bodiesAllB_sound h.2 hb)⟩

/-- `OnProgram`'s introduction rule from a per-node Boolean: `hp` is the clause read at one
node, which is where each clause's own statement enters. -/
theorem onProgramB_sound {Γ : GlobalDeclarations} {t : LBTerm} {p : LBTerm → Bool}
    {P : LBTerm → Prop} (hp : ∀ u, (∀ v, SubTerm v u → p v = true) → P u)
    (h : onProgramB Γ t p = true) : OnProgram Γ t P :=
  progB_sound (fun u hu => hp u (fun _ hv => subtermAll_sound hu hv)) h

/-! ## The environment clauses -/

/-- No key of the list repeats. -/
def keysDistinctB : List Kername → Bool
  | [] => true
  | k :: rest => rest.all (fun q => !Kername.beq k q) && keysDistinctB rest

/-- `LBWfPeregrine.keys`, decided. -/
theorem keysDistinctB_sound : ∀ {l : List Kername}, keysDistinctB l = true →
    l.Pairwise (fun a b => Kername.beq a b = false)
  | [], _ => List.Pairwise.nil
  | k :: rest, h => by
      simp only [keysDistinctB, Bool.and_eq_true, List.all_eq_true] at h
      refine List.Pairwise.cons (fun q hq => ?_) (keysDistinctB_sound h.2)
      simpa using h.1 q hq

/-- Every inductive declaration has a body, and every body a constructor. -/
def declsWfB (Γ : GlobalDeclarations) : Bool :=
  Γ.all fun p => match p.2 with
    | .inductiveDecl body =>
        !body.bodies.isEmpty && body.bodies.all (fun oib => !oib.ctors.isEmpty)
    | _ => true

/-- `LBWfPeregrine.declsWf`, decided. -/
theorem declsWfB_sound {Γ : GlobalDeclarations} (h : declsWfB Γ = true) :
    ∀ kn body, LBTerm.envLookup Γ kn = some (.inductiveDecl body) →
      body.bodies ≠ [] ∧ ∀ oib ∈ body.bodies, oib.ctors ≠ [] := by
  intro kn body hb
  have hall := List.all_eq_true.1 h _ (envLookup_mem hb)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hall
  exact ⟨hall.1, fun oib hoib => by simpa using hall.2 oib hoib⟩

/-! ## The clauses that thread a binder depth -/

mutual
/-- No loose de Bruijn index `≥ k`. -/
def lbClosedB : LBTerm → Nat → Bool
  | .box, _ => true
  | .bvar i, k => i < k
  | .fvar _, _ => true
  | .lambda _ b, k => lbClosedB b (k + 1)
  | .letIn _ v b, k => lbClosedB v k && lbClosedB b (k + 1)
  | .app f a, k => lbClosedB f k && lbClosedB a k
  | .const _, _ => true
  | .construct _ _ args, k => lbClosedBArgs args k
  | .case _ d alts, k => lbClosedB d k && lbClosedBAlts alts k
  | .proj _ e, k => lbClosedB e k
  | .fix defs _, k => lbClosedBDefs defs (k + defs.length)
  | .prim _, _ => true

/-- `lbClosedB` over a constructor's arguments. -/
def lbClosedBArgs : List LBTerm → Nat → Bool
  | [], _ => true
  | t :: r, k => lbClosedB t k && lbClosedBArgs r k

/-- `lbClosedB` over case alternatives, each below its own field binders. -/
def lbClosedBAlts : List (List BinderName × LBTerm) → Nat → Bool
  | [], _ => true
  | (ns, b) :: r, k => lbClosedB b (k + ns.length) && lbClosedBAlts r k

/-- `lbClosedB` over the definitions of a `.fix` block. -/
def lbClosedBDefs : List (@FixDef LBTerm) → Nat → Bool
  | [], _ => true
  | d :: r, k => lbClosedB d.body k && lbClosedBDefs r k
end

mutual
/-- `LBWfPeregrine.closed`, per term. -/
theorem lbClosedB_sound : ∀ (t : LBTerm) (k : Nat), lbClosedB t k = true → LBClosed t k
  | .box, _, _ => trivial
  | .bvar i, k, h => by simp only [lbClosedB, decide_eq_true_eq] at h; exact h
  | .fvar _, _, _ => trivial
  | .const _, _, _ => trivial
  | .prim _, _, _ => trivial
  | .lambda _ b, k, h => lbClosedB_sound b (k + 1) h
  | .letIn _ v b, k, h => by
      simp only [lbClosedB, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound v k h.1, lbClosedB_sound b (k + 1) h.2⟩
  | .app f a, k, h => by
      simp only [lbClosedB, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound f k h.1, lbClosedB_sound a k h.2⟩
  | .construct _ _ args, k, h => lbClosedBArgs_sound args k h
  | .case _ d alts, k, h => by
      simp only [lbClosedB, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound d k h.1, lbClosedBAlts_sound alts k h.2⟩
  | .proj _ e, k, h => lbClosedB_sound e k h
  | .fix defs _, k, h => lbClosedBDefs_sound defs (k + defs.length) h

/-- `lbClosedBArgs` decides `LBClosedArgs`. -/
theorem lbClosedBArgs_sound : ∀ (l : List LBTerm) (k : Nat),
    lbClosedBArgs l k = true → LBClosedArgs l k
  | [], _, _ => trivial
  | t :: r, k, h => by
      simp only [lbClosedBArgs, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound t k h.1, lbClosedBArgs_sound r k h.2⟩

/-- `lbClosedBAlts` decides `LBClosedAlts`. -/
theorem lbClosedBAlts_sound : ∀ (l : List (List BinderName × LBTerm)) (k : Nat),
    lbClosedBAlts l k = true → LBClosedAlts l k
  | [], _, _ => trivial
  | (ns, b) :: r, k, h => by
      simp only [lbClosedBAlts, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound b (k + ns.length) h.1, lbClosedBAlts_sound r k h.2⟩

/-- `lbClosedBDefs` decides `LBClosedDefs`. -/
theorem lbClosedBDefs_sound : ∀ (l : List (@FixDef LBTerm)) (k : Nat),
    lbClosedBDefs l k = true → LBClosedDefs l k
  | [], _, _ => trivial
  | d :: r, k, h => by
      simp only [lbClosedBDefs, Bool.and_eq_true] at h
      exact ⟨lbClosedB_sound d.body k h.1, lbClosedBDefs_sound r k h.2⟩
end

mutual
/-- No `.construct` node carries arguments. -/
def noBlockB : LBTerm → Bool
  | .lambda _ b => noBlockB b
  | .letIn _ v b => noBlockB v && noBlockB b
  | .app f a => noBlockB f && noBlockB a
  | .case _ d alts => noBlockB d && noBlockBAlts alts
  | .fix defs _ => noBlockBDefs defs
  | .construct _ _ [] => true
  | .construct _ _ (_ :: _) => false
  | .proj _ e => noBlockB e
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => true

/-- `noBlockB` over case alternatives. -/
def noBlockBAlts : List (List BinderName × LBTerm) → Bool
  | [] => true
  | (_, b) :: r => noBlockB b && noBlockBAlts r

/-- `noBlockB` over the definitions of a `.fix` block. -/
def noBlockBDefs : List (@FixDef LBTerm) → Bool
  | [] => true
  | d :: r => noBlockB d.body && noBlockBDefs r
end

mutual
/-- `LBWfPeregrine.ctorApplied`, per term. -/
theorem noBlockB_sound : ∀ (t : LBTerm), noBlockB t = true → NoBlock t
  | .box, _ | .bvar _, _ | .fvar _, _ | .const _, _ | .prim _, _ => trivial
  | .construct _ _ [], _ => trivial
  | .lambda _ b, h => noBlockB_sound b h
  | .proj _ e, h => noBlockB_sound e h
  | .letIn _ v b, h => by
      simp only [noBlockB, Bool.and_eq_true] at h
      exact ⟨noBlockB_sound v h.1, noBlockB_sound b h.2⟩
  | .app f a, h => by
      simp only [noBlockB, Bool.and_eq_true] at h
      exact ⟨noBlockB_sound f h.1, noBlockB_sound a h.2⟩
  | .case _ d alts, h => by
      simp only [noBlockB, Bool.and_eq_true] at h
      exact ⟨noBlockB_sound d h.1, noBlockBAlts_sound alts h.2⟩
  | .fix defs _, h => noBlockBDefs_sound defs h

/-- `noBlockBAlts` decides `NoBlockAlts`. -/
theorem noBlockBAlts_sound : ∀ (l : List (List BinderName × LBTerm)),
    noBlockBAlts l = true → NoBlockAlts l
  | [], _ => trivial
  | (_, b) :: r, h => by
      simp only [noBlockBAlts, Bool.and_eq_true] at h
      exact ⟨noBlockB_sound b h.1, noBlockBAlts_sound r h.2⟩

/-- `noBlockBDefs` decides `NoBlockDefs`. -/
theorem noBlockBDefs_sound : ∀ (l : List (@FixDef LBTerm)),
    noBlockBDefs l = true → NoBlockDefs l
  | [], _ => trivial
  | d :: r, h => by
      simp only [noBlockBDefs, Bool.and_eq_true] at h
      exact ⟨noBlockB_sound d.body h.1, noBlockBDefs_sound r h.2⟩
end

/-! ## The per-node clauses -/

/-- `NoDangling`, at one node. -/
def noDanglingNode (Γ : GlobalDeclarations) : LBTerm → Bool
  | .const kn => (LBTerm.envLookup Γ kn).isSome
  | _ => true

/-- `LBWfPeregrine.constsOk`, read at one node. -/
theorem noDangling_of_nodes {Γ : GlobalDeclarations} (u : LBTerm)
    (h : ∀ v, SubTerm v u → noDanglingNode Γ v = true) : NoDangling Γ u := by
  intro kn hsub
  have := h _ hsub
  simpa [noDanglingNode, Option.isSome_iff_ne_none] using this

/-- `CtorsDeclared`, at one node. -/
def ctorsDeclaredNode (Γ : GlobalDeclarations) : LBTerm → Bool
  | .construct iid k _ => (constructorArity Γ iid k).isSome
  | _ => true

/-- `LBWfPeregrine.ctorDecl`, read at one node. -/
theorem ctorsDeclared_of_nodes {Γ : GlobalDeclarations} (u : LBTerm)
    (h : ∀ v, SubTerm v u → ctorsDeclaredNode Γ v = true) : CtorsDeclared Γ u := by
  intro iid k args hsub
  have := h _ hsub
  simpa [ctorsDeclaredNode, Option.isSome_iff_ne_none] using this

/-- One alternative per declared constructor, each binding that constructor's fields. -/
def altsMatchB : List (List BinderName × LBTerm) → List ConstructorBody → Bool
  | [], [] => true
  | (ns, _) :: as, cb :: cs => (ns.length == cb.nargs) && altsMatchB as cs
  | _, _ => false

/-- The two-list walk is the indexed statement `CasesExhaustive` reads. -/
theorem altsMatchB_sound : ∀ {as : List (List BinderName × LBTerm)} {cs : List ConstructorBody},
    altsMatchB as cs = true →
      as.length = cs.length ∧
      ∀ i (h : i < as.length) (h' : i < cs.length), (as[i]).1.length = (cs[i]).nargs
  | [], [], _ => ⟨rfl, fun _ h => absurd h (by simp)⟩
  | (ns, b) :: as, cb :: cs, h => by
      simp only [altsMatchB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hlen, hrest⟩ := altsMatchB_sound h.2
      refine ⟨by simp [hlen], fun i hi hi' => ?_⟩
      cases i with
      | zero => simpa using h.1
      | succ j => simpa using hrest j (by simpa using hi) (by simpa using hi')

/-- `CasesExhaustive`, at one node. -/
def casesExhNode (Γ : GlobalDeclarations) : LBTerm → Bool
  | .case (iid, _) _ alts =>
      match inductiveBody Γ iid with
      | some oib => altsMatchB alts oib.ctors
      | none => false
  | _ => true

/-- `LBWfPeregrine.casesExh`, read at one node. -/
theorem casesExhaustive_of_nodes {Γ : GlobalDeclarations} (u : LBTerm)
    (h : ∀ v, SubTerm v u → casesExhNode Γ v = true) : CasesExhaustive Γ u := by
  intro iid np discr alts hsub
  have hn := h _ hsub
  simp only [casesExhNode] at hn
  split at hn
  · rename_i oib hib
    exact ⟨oib, hib, (altsMatchB_sound hn).1, (altsMatchB_sound hn).2⟩
  · exact absurd hn (by simp)

/-- `FixLambda`, at one node. -/
def fixLambdaNode : LBTerm → Bool
  | .fix defs _ => defs.all fun d => match d.body with | .lambda _ _ => true | _ => false
  | _ => true

/-- `LBWfPeregrine.fixLambda`, read at one node. -/
theorem fixLambda_of_nodes (u : LBTerm)
    (h : ∀ v, SubTerm v u → fixLambdaNode v = true) : FixLambda u := by
  intro defs i hsub fd hfd
  have hn := List.all_eq_true.1 (h _ hsub) fd hfd
  split at hn
  · rename_i nm b heq
    exact ⟨nm, b, heq⟩
  · exact absurd hn (by simp)

/-- `ProjsDeclared`, at one node. -/
def projDeclNode (Γ : GlobalDeclarations) : LBTerm → Bool
  | .proj p _ =>
      (match inductiveBody Γ p.indType with
       | some oib => (match oib.ctors with
                      | [cb] => p.fieldIdx < cb.nargs
                      | _ => false)
       | none => false)
  | _ => true

/-- `LBWfPeregrine.projDecl`, read at one node. -/
theorem projsDeclared_of_nodes {Γ : GlobalDeclarations} (u : LBTerm)
    (h : ∀ v, SubTerm v u → projDeclNode Γ v = true) : ProjsDeclared Γ u := by
  intro p e hsub
  have hn := h _ hsub
  simp only [projDeclNode] at hn
  split at hn
  · rename_i oib hib
    split at hn
    · rename_i cb hcb
      exact ⟨oib, cb, hib, hcb, by simpa using hn⟩
    · exact absurd hn (by simp)
  · exact absurd hn (by simp)

/-- The name closes and escapes no printed atom. -/
def printableNameB : BinderName → Bool
  | .named s => s.toList.all (fun c => c != '"' && c != '\\')
  | .anon => true

/-- `PrintableBinderName`, decided. -/
theorem printableBinderName_of_check {nm : BinderName} (h : printableNameB nm = true) :
    PrintableBinderName nm := by
  cases nm with
  | anon => trivial
  | named s => intro c hc; simpa using List.all_eq_true.1 h c hc

/-- `PrintableBinders`, at one node: the four binder positions of `LBTerm`. -/
def printableNode : LBTerm → Bool
  | .lambda nm _ => printableNameB nm
  | .letIn nm _ _ => printableNameB nm
  | .case _ _ alts => alts.all (fun q => q.1.all printableNameB)
  | .fix defs _ => defs.all (fun d => printableNameB d.name)
  | _ => true

/-- `LBWfPeregrine.printableNames`, read at one node. -/
theorem printableBinders_of_nodes (u : LBTerm)
    (h : ∀ v, SubTerm v u → printableNode v = true) : PrintableBinders u := by
  refine ⟨fun nm b hsub => printableBinderName_of_check (h _ hsub),
    fun nm v b hsub => printableBinderName_of_check (h _ hsub), ?_, ?_⟩
  · intro info discr alts ns b hsub hmem nm hnm
    have hall := List.all_eq_true.1 (h _ hsub) (ns, b) hmem
    exact printableBinderName_of_check (List.all_eq_true.1 hall nm hnm)
  · intro defs i fd hsub hfd
    exact printableBinderName_of_check (List.all_eq_true.1 (h _ hsub) fd hfd)

/-! ## Constructor saturation -/

/-- The `IsConstructSpine` data of `t`, if any: the head constructor and the number of
arguments stored in the node and applied to it. -/
def spineInfo : LBTerm → Option (InductiveId × Nat × Nat)
  | .construct iid k args => some (iid, k, args.length)
  | .app f _ => match spineInfo f with
      | some (iid, k, n) => some (iid, k, n + 1)
      | none => none
  | _ => none

/-- A spine at `t`, if there is one, carries at least its constructor's declared arity. -/
def spineOkB (Γ : GlobalDeclarations) (t : LBTerm) : Bool :=
  match spineInfo t with
  | some (iid, k, n) => (match constructorArity Γ iid k with | some a => a ≤ n | none => true)
  | none => true

/-- `spineInfo` computes `IsConstructSpine`. -/
theorem spineInfo_of_isConstructSpine {t : LBTerm} {iid : InductiveId} {k n : Nat}
    (h : IsConstructSpine t iid k n) : spineInfo t = some (iid, k, n) := by
  induction h with
  | construct => rfl
  | app _ ih => rw [spineInfo, ih]

/-- A spine root is constructor-headed. -/
theorem IsConstructSpine.ctorHeaded {t : LBTerm} {iid : InductiveId} {k n : Nat}
    (h : IsConstructSpine t iid k n) : CtorHeaded t := ⟨iid, k, n, h⟩

/-- The arity bound the node check carries, at the spine it is checked for. -/
theorem spineOkB_sound {Γ : GlobalDeclarations} {t : LBTerm} {iid : InductiveId} {k n : Nat}
    (hb : spineOkB Γ t = true) (h : IsConstructSpine t iid k n) :
    ∀ a, constructorArity Γ iid k = some a → a ≤ n := by
  intro a ha
  simp only [spineOkB, spineInfo_of_isConstructSpine h, ha, decide_eq_true_eq] at hb
  exact hb

mutual
/-- Every constructor spine in `t` carries at least its constructor's declared arity, each
spine counted at its maximal application depth. -/
def ctorSatB (Γ : GlobalDeclarations) : LBTerm → Bool
  | .construct iid k args => spineOkB Γ (.construct iid k args) && ctorSatBArgs Γ args
  | .app f a => spineOkB Γ (.app f a) && ctorSatBFn Γ f && ctorSatB Γ a
  | .lambda _ b => ctorSatB Γ b
  | .letIn _ v b => ctorSatB Γ v && ctorSatB Γ b
  | .case _ d alts => ctorSatB Γ d && ctorSatBAlts Γ alts
  | .proj _ e => ctorSatB Γ e
  | .fix defs _ => ctorSatBDefs Γ defs
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => true

/-- The function side of an application: a constructor found here heads a longer spine, whose
arity is checked at the outermost application, so this node carries no check of its own. This
is `ConstructSpine.appFn`'s `¬ CtorHeaded` guard. -/
def ctorSatBFn (Γ : GlobalDeclarations) : LBTerm → Bool
  | .construct _ _ args => ctorSatBArgs Γ args
  | .app f a => ctorSatBFn Γ f && ctorSatB Γ a
  | .lambda _ b => ctorSatB Γ b
  | .letIn _ v b => ctorSatB Γ v && ctorSatB Γ b
  | .case _ d alts => ctorSatB Γ d && ctorSatBAlts Γ alts
  | .proj _ e => ctorSatB Γ e
  | .fix defs _ => ctorSatBDefs Γ defs
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => true

/-- `ctorSatB` over a constructor's arguments. -/
def ctorSatBArgs (Γ : GlobalDeclarations) : List LBTerm → Bool
  | [] => true
  | t :: r => ctorSatB Γ t && ctorSatBArgs Γ r

/-- `ctorSatB` over case alternatives. -/
def ctorSatBAlts (Γ : GlobalDeclarations) : List (List BinderName × LBTerm) → Bool
  | [] => true
  | (_, b) :: r => ctorSatB Γ b && ctorSatBAlts Γ r

/-- `ctorSatB` over the definitions of a `.fix` block. -/
def ctorSatBDefs (Γ : GlobalDeclarations) : List (@FixDef LBTerm) → Bool
  | [] => true
  | d :: r => ctorSatB Γ d.body && ctorSatBDefs Γ r
end

/-- The check descends into each argument. -/
theorem ctorSatBArgs_mem {Γ : GlobalDeclarations} : ∀ {l : List LBTerm} {x : LBTerm},
    ctorSatBArgs Γ l = true → x ∈ l → ctorSatB Γ x = true
  | _ :: _, x, h, hx => by
      simp only [ctorSatBArgs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact ctorSatBArgs_mem h.2 hx

/-- The check descends into each branch body. -/
theorem ctorSatBAlts_mem {Γ : GlobalDeclarations} :
    ∀ {l : List (List BinderName × LBTerm)} {ns : List BinderName} {b : LBTerm},
      ctorSatBAlts Γ l = true → (ns, b) ∈ l → ctorSatB Γ b = true
  | a :: _, ns, b, h, hx => by
      obtain ⟨ns', b'⟩ := a
      simp only [ctorSatBAlts, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with heq | hx
      · cases heq; exact h.1
      · exact ctorSatBAlts_mem h.2 hx

/-- The check descends into each definition of a block. -/
theorem ctorSatBDefs_mem {Γ : GlobalDeclarations} :
    ∀ {l : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
      ctorSatBDefs Γ l = true → d ∈ l → ctorSatB Γ d.body = true
  | _ :: _, d, h, hx => by
      simp only [ctorSatBDefs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact ctorSatBDefs_mem h.2 hx

/-- The arity bound at a spine that is the whole term. -/
theorem ctorSatB_root {Γ : GlobalDeclarations} {t : LBTerm} {iid : InductiveId} {k n : Nat}
    (h : IsConstructSpine t iid k n) (hc : ctorSatB Γ t = true) :
    ∀ a, constructorArity Γ iid k = some a → a ≤ n := by
  cases h with
  | construct =>
      simp only [ctorSatB, Bool.and_eq_true] at hc
      exact spineOkB_sound hc.1 .construct
  | app h' =>
      simp only [ctorSatB, Bool.and_eq_true] at hc
      exact spineOkB_sound hc.1.1 (.app h')

/-- Both saturation clauses, per term. The second conjunct is what the induction spends at
`ConstructSpine.appFn`: on the function side of an application the check is `ctorSatBFn`, and
that arm carries the bound only because the spine there is not constructor-headed. -/
theorem ctorSat_sound {Γ : GlobalDeclarations} {t : LBTerm} {iid : InductiveId} {k n : Nat}
    (hsp : ConstructSpine t iid k n) :
    (ctorSatB Γ t = true → ∀ a, constructorArity Γ iid k = some a → a ≤ n) ∧
    (¬ CtorHeaded t → ctorSatBFn Γ t = true →
      ∀ a, constructorArity Γ iid k = some a → a ≤ n) := by
  induction hsp with
  | root h => exact ⟨ctorSatB_root h, fun hnc => absurd h.ctorHeaded hnc⟩
  | appFn hnc _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc; exact ih.2 hnc hc.1.2
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc; exact ih.2 hnc hc.1
  | appArg _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc; exact ih.1 hc.2
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.2
  | constructArg hx _ ih =>
      refine ⟨fun hc => ?_, fun hnc _ => absurd (IsConstructSpine.construct).ctorHeaded hnc⟩
      simp only [ctorSatB, Bool.and_eq_true] at hc
      exact ih.1 (ctorSatBArgs_mem hc.2 hx)
  | lambda _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [ctorSatB] at hc; exact ih.1 hc
      · rw [ctorSatBFn] at hc; exact ih.1 hc
  | letInVal _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc; exact ih.1 hc.1
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.1
  | letInBody _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc; exact ih.1 hc.2
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.2
  | caseDiscr _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc; exact ih.1 hc.1
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.1
  | caseAlt ha _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [ctorSatB, Bool.and_eq_true] at hc
        exact ih.1 (ctorSatBAlts_mem hc.2 ha)
      · simp only [ctorSatBFn, Bool.and_eq_true] at hc
        exact ih.1 (ctorSatBAlts_mem hc.2 ha)
  | proj _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [ctorSatB] at hc; exact ih.1 hc
      · rw [ctorSatBFn] at hc; exact ih.1 hc
  | fixBody hd _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [ctorSatB] at hc; exact ih.1 (ctorSatBDefs_mem hc hd)
      · rw [ctorSatBFn] at hc; exact ih.1 (ctorSatBDefs_mem hc hd)

/-! ## The entry point -/

/-- `LBWfPeregrine`, decided: eleven conjuncts for its twelve clauses, the last saturation
conjunct carrying both `etaCtorsEnv` and `etaCtorsTm`. -/
def lbWfPeregrineB (Γ : GlobalDeclarations) (t : LBTerm) : Bool :=
  keysDistinctB (Γ.map Prod.fst)
    && declsWfB Γ
    && progB Γ t (lbClosedB · 0)
    && onProgramB Γ t (noDanglingNode Γ)
    && progB Γ t noBlockB
    && onProgramB Γ t (ctorsDeclaredNode Γ)
    && onProgramB Γ t (casesExhNode Γ)
    && onProgramB Γ t fixLambdaNode
    && onProgramB Γ t (projDeclNode Γ)
    && progB Γ t (ctorSatB Γ)
    && onProgramB Γ t printableNode

/-- A `by decide +kernel` verdict on the emitted program is the capstone's `wf` premise. -/
theorem lbWfPeregrine_of_check {Γ : GlobalDeclarations} {t : LBTerm}
    (h : lbWfPeregrineB Γ t = true) : LBWfPeregrine Γ t := by
  simp only [lbWfPeregrineB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkeys, hdecls⟩, hclosed⟩, hconsts⟩, hblock⟩, hctor⟩, hcase⟩, hfix⟩,
    hproj⟩, hsat⟩, hname⟩ := h
  have hsatP := progB_sound
    (P := fun u => ∀ iid k n, ConstructSpine u iid k n →
      ∀ a, constructorArity Γ iid k = some a → a ≤ n)
    (fun _ hu _ _ _ hsp => (ctorSat_sound hsp).1 hu) hsat
  exact
    { keys := keysDistinctB_sound hkeys
      declsWf := declsWfB_sound hdecls
      closed := progB_sound (fun u hu => lbClosedB_sound u 0 hu) hclosed
      constsOk := onProgramB_sound noDangling_of_nodes hconsts
      ctorApplied := progB_sound noBlockB_sound hblock
      ctorDecl := onProgramB_sound ctorsDeclared_of_nodes hctor
      casesExh := onProgramB_sound casesExhaustive_of_nodes hcase
      fixLambda := onProgramB_sound fixLambda_of_nodes hfix
      projDecl := onProgramB_sound projsDeclared_of_nodes hproj
      etaCtorsEnv := fun kn b iid k n hb hsp a ha => hsatP.2 kn b hb iid k n hsp a ha
      etaCtorsTm := fun iid k n hsp a ha => hsatP.1 iid k n hsp a ha
      printableNames := onProgramB_sound printableBinders_of_nodes hname }

/-- Non-vacuity: a two-declaration program the checker accepts, and the structure it yields. -/
example :
    LBWfPeregrine
      [(rootKername "z", .constantDecl ⟨some (.construct ⟨rootKername "Nat", 0⟩ 0 [])⟩),
       (rootKername "Nat", .inductiveDecl ⟨.finite, 0,
          [⟨"Nat", false, .IntoAny, [⟨"Nat.zero", 0⟩, ⟨"Nat.succ", 1⟩], []⟩]⟩)]
      (.const (rootKername "z")) :=
  lbWfPeregrine_of_check (by decide +kernel)

/-- The checker is not constantly `true`: the same term at an empty environment names a
constant that resolves nowhere. -/
example : lbWfPeregrineB [] (.const (rootKername "z")) = false := by decide +kernel

end LeanToLambdaBox
