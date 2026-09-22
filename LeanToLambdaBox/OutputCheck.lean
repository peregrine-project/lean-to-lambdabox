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
`subtermAll_sound` — its statement is never restated here. Five clauses are of that shape:
`constsOk`, `ctorDecl`, `casesExh`, `projDecl` and `printableNames`.

The other seven have their own fold. `keysDistinctB` (`keys`) and `declsWfB` (`declsWf`) look
at `Γ` alone. `lbClosedB` (`closed`) threads a binder depth and `noBlockB` (`ctorApplied`) is a
whole-term recursion, both spent through `progB`. `ctorSatB` (`etaCtorsEnv` and `etaCtorsTm`
together) counts a constructor spine at its maximal application depth, which is what
`ConstructSpine`'s `appFn` guard demands — hence the second function `ctorSatBFn`, which walks
the function side of an application without treating a constructor found there as a spine
root. `lbExpandedTFixB` (`expandedFix`) is three walks, one per conjunct of `expanded_tFix`.

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

/-! ## Fixpoint η

Three walks, one per conjunct of `expanded_tFix`. `fixSatB` counts a `.fix` spine at its
maximal application depth, the way `ctorSatB` counts a constructor spine, so it has the same
second function `fixSatBFn` for the function side of an application. `fixLambdaNode` is
already a per-node check. `fixSelfB` threads the binder demands `expanded` carries in its
`Γ : list nat`, pushing `fixDemands defs` at a block and `0` at every other binder, and an
argument counter for the spine an index is found under.
-/

/-- The `IsFixSpine` data of `t`, if any: the block, the selected index and the number of
arguments applied to it. -/
def fixSpineInfo : LBTerm → Option (List (@FixDef LBTerm) × Nat × Nat)
  | .fix defs i => some (defs, i, 0)
  | .app f _ => match fixSpineInfo f with
      | some (defs, i, n) => some (defs, i, n + 1)
      | none => none
  | _ => none

/-- A `.fix` spine at `t`, if there is one, is applied past its principal argument. -/
def fixOkB (t : LBTerm) : Bool :=
  match fixSpineInfo t with
  | some (defs, i, n) => 0 < n && defs[i]?.all fun fd => fd.principalArgIdx < n
  | none => true

/-- `fixSpineInfo` computes `IsFixSpine`. -/
theorem fixSpineInfo_of_isFixSpine {t : LBTerm} {defs : List (@FixDef LBTerm)} {i n : Nat}
    (h : IsFixSpine t defs i n) : fixSpineInfo t = some (defs, i, n) := by
  induction h with
  | fix => rfl
  | app _ ih => rw [fixSpineInfo, ih]

/-- A spine root is `.fix`-headed. -/
theorem IsFixSpine.fixHeaded {t : LBTerm} {defs : List (@FixDef LBTerm)} {i n : Nat}
    (h : IsFixSpine t defs i n) : FixHeaded t := ⟨defs, i, n, h⟩

/-- The bound the node check carries, at the spine it is checked for. -/
theorem fixOkB_sound {t : LBTerm} {defs : List (@FixDef LBTerm)} {i n : Nat}
    (hb : fixOkB t = true) (h : IsFixSpine t defs i n) :
    n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n := by
  rw [fixOkB, fixSpineInfo_of_isFixSpine h] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨Nat.pos_iff_ne_zero.1 hb.1, fun fd hfd => ?_⟩
  have h2 := hb.2
  rw [hfd] at h2
  simpa using h2

mutual
/-- Every `.fix` spine in `t` is applied past its principal argument, each spine counted at
its maximal application depth. -/
def fixSatB : LBTerm → Bool
  | .fix defs i => fixOkB (.fix defs i) && fixSatBDefs defs
  | .app f a => fixOkB (.app f a) && fixSatBFn f && fixSatB a
  | .lambda _ b => fixSatB b
  | .letIn _ v b => fixSatB v && fixSatB b
  | .construct _ _ args => fixSatBArgs args
  | .case _ d alts => fixSatB d && fixSatBAlts alts
  | .proj _ e => fixSatB e
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => true

/-- The function side of an application: a `.fix` found here heads a longer spine, whose
arguments are counted at the outermost application, so this node carries no check of its own.
This is `FixSpine.appFn`'s `¬ FixHeaded` guard. -/
def fixSatBFn : LBTerm → Bool
  | .fix defs _ => fixSatBDefs defs
  | .app f a => fixSatBFn f && fixSatB a
  | .lambda _ b => fixSatB b
  | .letIn _ v b => fixSatB v && fixSatB b
  | .construct _ _ args => fixSatBArgs args
  | .case _ d alts => fixSatB d && fixSatBAlts alts
  | .proj _ e => fixSatB e
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => true

/-- `fixSatB` over a constructor's arguments. -/
def fixSatBArgs : List LBTerm → Bool
  | [] => true
  | t :: r => fixSatB t && fixSatBArgs r

/-- `fixSatB` over case alternatives. -/
def fixSatBAlts : List (List BinderName × LBTerm) → Bool
  | [] => true
  | (_, b) :: r => fixSatB b && fixSatBAlts r

/-- `fixSatB` over the definitions of a `.fix` block. -/
def fixSatBDefs : List (@FixDef LBTerm) → Bool
  | [] => true
  | d :: r => fixSatB d.body && fixSatBDefs r
end

/-- The check descends into each argument. -/
theorem fixSatBArgs_mem : ∀ {l : List LBTerm} {x : LBTerm},
    fixSatBArgs l = true → x ∈ l → fixSatB x = true
  | _ :: _, x, h, hx => by
      simp only [fixSatBArgs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact fixSatBArgs_mem h.2 hx

/-- The check descends into each branch body. -/
theorem fixSatBAlts_mem :
    ∀ {l : List (List BinderName × LBTerm)} {ns : List BinderName} {b : LBTerm},
      fixSatBAlts l = true → (ns, b) ∈ l → fixSatB b = true
  | a :: _, ns, b, h, hx => by
      obtain ⟨ns', b'⟩ := a
      simp only [fixSatBAlts, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with heq | hx
      · cases heq; exact h.1
      · exact fixSatBAlts_mem h.2 hx

/-- The check descends into each definition of a block. -/
theorem fixSatBDefs_mem : ∀ {l : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
    fixSatBDefs l = true → d ∈ l → fixSatB d.body = true
  | _ :: _, d, h, hx => by
      simp only [fixSatBDefs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact fixSatBDefs_mem h.2 hx

/-- The bound at a spine that is the whole term. -/
theorem fixSatB_root {t : LBTerm} {defs : List (@FixDef LBTerm)} {i n : Nat}
    (h : IsFixSpine t defs i n) (hc : fixSatB t = true) :
    n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n := by
  cases h with
  | fix =>
      simp only [fixSatB, Bool.and_eq_true] at hc
      exact fixOkB_sound hc.1 .fix
  | app h' =>
      simp only [fixSatB, Bool.and_eq_true] at hc
      exact fixOkB_sound hc.1.1 (.app h')

/-- `LBExpandedFix`, per term. The second conjunct is what the induction spends at
`FixSpine.appFn`: on the function side of an application the check is `fixSatBFn`, and that
arm carries the bound only because the spine there is not `.fix`-headed. -/
theorem fixSat_sound {t : LBTerm} {defs : List (@FixDef LBTerm)} {i n : Nat}
    (hsp : FixSpine t defs i n) :
    (fixSatB t = true → n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n) ∧
    (¬ FixHeaded t → fixSatBFn t = true →
      n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n) := by
  induction hsp with
  | root h => exact ⟨fixSatB_root h, fun hnc => absurd h.fixHeaded hnc⟩
  | appFn hnc _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc; exact ih.2 hnc hc.1.2
      · simp only [fixSatBFn, Bool.and_eq_true] at hc; exact ih.2 hnc hc.1
  | appArg _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc; exact ih.1 hc.2
      · simp only [fixSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.2
  | constructArg hx _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [fixSatB] at hc; exact ih.1 (fixSatBArgs_mem hc hx)
      · rw [fixSatBFn] at hc; exact ih.1 (fixSatBArgs_mem hc hx)
  | lambda _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [fixSatB] at hc; exact ih.1 hc
      · rw [fixSatBFn] at hc; exact ih.1 hc
  | letInVal _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc; exact ih.1 hc.1
      · simp only [fixSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.1
  | letInBody _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc; exact ih.1 hc.2
      · simp only [fixSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.2
  | caseDiscr _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc; exact ih.1 hc.1
      · simp only [fixSatBFn, Bool.and_eq_true] at hc; exact ih.1 hc.1
  | caseAlt ha _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · simp only [fixSatB, Bool.and_eq_true] at hc
        exact ih.1 (fixSatBAlts_mem hc.2 ha)
      · simp only [fixSatBFn, Bool.and_eq_true] at hc
        exact ih.1 (fixSatBAlts_mem hc.2 ha)
  | proj _ ih =>
      refine ⟨fun hc => ?_, fun _ hc => ?_⟩
      · rw [fixSatB] at hc; exact ih.1 hc
      · rw [fixSatBFn] at hc; exact ih.1 hc
  | fixBody hd _ ih =>
      refine ⟨fun hc => ?_, fun hnc _ => absurd (IsFixSpine.fix).fixHeaded hnc⟩
      simp only [fixSatB, Bool.and_eq_true] at hc
      exact ih.1 (fixSatBDefs_mem hc.2 hd)

mutual
/-- `FixSelfApplied`, decided: `ctx` is the binder demands in scope and `k` the number of
arguments `t` is itself applied to, so a de Bruijn head is read against the whole spine. -/
def fixSelfB : LBTerm → List Nat → Nat → Bool
  | .bvar n, ctx, k => match ctx[n]? with | some m => m ≤ k | none => true
  | .app f a, ctx, k => fixSelfB f ctx (k + 1) && fixSelfB a ctx 0
  | .lambda _ b, ctx, _ => fixSelfB b (0 :: ctx) 0
  | .letIn _ v b, ctx, _ => fixSelfB v ctx 0 && fixSelfB b (0 :: ctx) 0
  | .construct _ _ args, ctx, _ => fixSelfBArgs args ctx
  | .case _ d alts, ctx, _ => fixSelfB d ctx 0 && fixSelfBAlts alts ctx
  | .proj _ e, ctx, _ => fixSelfB e ctx 0
  | .fix defs _, ctx, _ => fixSelfBDefs defs (fixDemands defs ++ ctx)
  | .box, _, _ => true
  | .fvar _, _, _ => true
  | .const _, _, _ => true
  | .prim _, _, _ => true

/-- `fixSelfB` over a constructor's arguments. -/
def fixSelfBArgs : List LBTerm → List Nat → Bool
  | [], _ => true
  | t :: r, ctx => fixSelfB t ctx 0 && fixSelfBArgs r ctx

/-- `fixSelfB` over case alternatives, each below its own field binders, which demand
nothing — `repeat 0 #|br.1| ++ Γ` (`EEtaExpandedFix.v:43`). -/
def fixSelfBAlts : List (List BinderName × LBTerm) → List Nat → Bool
  | [], _ => true
  | (ns, b) :: r, ctx =>
      fixSelfB b (List.replicate ns.length 0 ++ ctx) 0 && fixSelfBAlts r ctx

/-- `fixSelfB` over the definitions of a `.fix` block, under the demands the caller has
already pushed. -/
def fixSelfBDefs : List (@FixDef LBTerm) → List Nat → Bool
  | [], _ => true
  | d :: r, ctx => fixSelfB d.body ctx 0 && fixSelfBDefs r ctx
end

/-- The check descends into each argument. -/
theorem fixSelfBArgs_mem : ∀ {l : List LBTerm} {ctx : List Nat} {x : LBTerm},
    fixSelfBArgs l ctx = true → x ∈ l → fixSelfB x ctx 0 = true
  | _ :: _, ctx, x, h, hx => by
      simp only [fixSelfBArgs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact fixSelfBArgs_mem h.2 hx

/-- The check descends into each branch body, under that branch's own field binders. -/
theorem fixSelfBAlts_mem :
    ∀ {l : List (List BinderName × LBTerm)} {ctx : List Nat} {ns : List BinderName} {b : LBTerm},
      fixSelfBAlts l ctx = true → (ns, b) ∈ l →
        fixSelfB b (List.replicate ns.length 0 ++ ctx) 0 = true
  | a :: _, ctx, ns, b, h, hx => by
      obtain ⟨ns', b'⟩ := a
      simp only [fixSelfBAlts, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with heq | hx
      · cases heq; exact h.1
      · exact fixSelfBAlts_mem h.2 hx

/-- The check descends into each definition of a block. -/
theorem fixSelfBDefs_mem : ∀ {l : List (@FixDef LBTerm)} {ctx : List Nat} {d : @FixDef LBTerm},
    fixSelfBDefs l ctx = true → d ∈ l → fixSelfB d.body ctx 0 = true
  | _ :: _, ctx, d, h, hx => by
      simp only [fixSelfBDefs, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact fixSelfBDefs_mem h.2 hx

/-- Every located de Bruijn occurrence carries what its binder demands. -/
theorem fixSelf_sound {ctx : List Nat} {k : Nat} {t : LBTerm} {m k' : Nat}
    (h : BVarDemand ctx k t m k') : fixSelfB t ctx k = true → m ≤ k' := by
  induction h with
  | bvar hn => intro hc; rw [fixSelfB, hn] at hc; simpa using hc
  | appFn _ ih => intro hc; simp only [fixSelfB, Bool.and_eq_true] at hc; exact ih hc.1
  | appArg _ ih => intro hc; simp only [fixSelfB, Bool.and_eq_true] at hc; exact ih hc.2
  | lambda _ ih => intro hc; rw [fixSelfB] at hc; exact ih hc
  | letInVal _ ih => intro hc; simp only [fixSelfB, Bool.and_eq_true] at hc; exact ih hc.1
  | letInBody _ ih => intro hc; simp only [fixSelfB, Bool.and_eq_true] at hc; exact ih hc.2
  | constructArg hx _ ih => intro hc; rw [fixSelfB] at hc; exact ih (fixSelfBArgs_mem hc hx)
  | caseDiscr _ ih => intro hc; simp only [fixSelfB, Bool.and_eq_true] at hc; exact ih hc.1
  | caseAlt ha _ ih =>
      intro hc
      simp only [fixSelfB, Bool.and_eq_true] at hc
      exact ih (fixSelfBAlts_mem hc.2 ha)
  | proj _ ih => intro hc; rw [fixSelfB] at hc; exact ih hc
  | fixBody hd _ ih => intro hc; rw [fixSelfB] at hc; exact ih (fixSelfBDefs_mem hc hd)

/-- `LBExpandedFix`, decided. -/
def lbExpandedFixB (Γ : GlobalDeclarations) (t : LBTerm) : Bool := progB Γ t fixSatB

/-- `LBFixSelfApplied`, decided. -/
def lbFixSelfAppliedB (Γ : GlobalDeclarations) (t : LBTerm) : Bool :=
  progB Γ t fun u => fixSelfB u [] 0

/-- `LBExpandedTFix`, decided: the three conjuncts of `expanded_tFix`. -/
def lbExpandedTFixB (Γ : GlobalDeclarations) (t : LBTerm) : Bool :=
  lbExpandedFixB Γ t && onProgramB Γ t fixLambdaNode && lbFixSelfAppliedB Γ t

/-- `LBWfPeregrine.expandedFix`, decided. -/
theorem lbExpandedTFixB_sound {Γ : GlobalDeclarations} {t : LBTerm}
    (h : lbExpandedTFixB Γ t = true) : LBExpandedTFix Γ t := by
  simp only [lbExpandedTFixB, lbExpandedFixB, lbFixSelfAppliedB, Bool.and_eq_true] at h
  obtain ⟨⟨hfix, hlam⟩, hself⟩ := h
  exact ⟨progB_sound (fun _ hu _ _ _ hsp => (fixSat_sound hsp).1 hu) hfix,
    onProgramB_sound fixLambda_of_nodes hlam,
    progB_sound (fun _ hu _ _ hd => fixSelf_sound hd hu) hself⟩

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
    && lbExpandedTFixB Γ t
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
      expandedFix := lbExpandedTFixB_sound hfix
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

/-! ### The fixpoint clause, separated

One block, four bodies, each isolating one conjunct of `expanded_tFix`. -/

/-- A one-member block whose body is `fun _ => b`. -/
private def demoBlock (b : LBTerm) : List (@FixDef LBTerm) := [⟨.anon, .lambda .anon b, 0⟩]

/-- The spine conjunct bites: a constant whose body is a **bare** `.fix` node — the shape the
eraser registered before `Erasure.etaExpandFix` — is rejected, because `expanded_tFix` admits
a `.fix` only under a non-empty spine. -/
example : lbExpandedTFixB
    [(rootKername "f", .constantDecl ⟨some (.fix (demoBlock (.bvar 0)) 0)⟩)]
    (.const (rootKername "f")) = false := by decide +kernel

/-- The η-expanded shape `Erasure.etaExpandFix` emits is accepted at the same block. -/
example : lbExpandedTFixB
    [(rootKername "f", .constantDecl
        ⟨some (.lambda .anon (.app (.fix (demoBlock (.bvar 0)) 0) (.bvar 0)))⟩)]
    (.const (rootKername "f")) = true := by decide +kernel

/-- The self-application conjunct is not implied by the other two: this block is η-expanded
and λ-headed, and is still rejected, because the member body's self-reference `.bvar 1`
carries no argument where `fixDemands` asks for `1 + rarg = 1`. -/
example : lbExpandedTFixB
    [(rootKername "f", .constantDecl
        ⟨some (.lambda .anon (.app (.fix (demoBlock (.bvar 1)) 0) (.bvar 0)))⟩)]
    (.const (rootKername "f")) = false := by decide +kernel

/-- The same block with the self-reference applied to one argument is accepted: the shape a
`visitMutual` run emits, and the one the corpus measurement finds at all 56 self-references. -/
example : lbExpandedTFixB
    [(rootKername "f", .constantDecl
        ⟨some (.lambda .anon
          (.app (.fix (demoBlock (.app (.bvar 1) (.bvar 0))) 0) (.bvar 0)))⟩)]
    (.const (rootKername "f")) = true := by decide +kernel

end LeanToLambdaBox
