import EraseProof.Semantics.Iota
import EraseProof.Bridge.CLNames

/-!
# The syntax a recognized `casesOn` is read through, and the grading of a certified term

What the decode of the ι steps (`EraseProof.Semantics.DecodeAt`) reads of the program: the
syntax tests of the shipping recognizer `Erasure.casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`)
and their readings through `toCL?`; the constructor records a block's split reads; the quotient
records con-leche stores. Also: a term the run-time certificate `CLOk` types is graded through its
marks (`GradedU`).
-/
open Lean Erasure

namespace EraseProof

universe w

/-- A term `CLOk` certifies is graded through its marks: the certificate's second run types the
reading of `unmark t`, which is then closed (`CLTyped.closed`) and graded in every model
(`SemCases.infer0`). Reference: none (DV-33). -/
theorem CLOk.gradedU {env : ConLeche.Env} {t : Expr} (h : CLOk env t) : GradedU.{w} env t := by
  obtain ⟨c, F, T, hc, hinf⟩ := h.2
  have hb := CLTyped.closed h.2 hc
  exact ⟨c, hc, hb, fun V _ m φ => SemCases.infer0 m φ hinf (toCL?_hasFvar hc) hb⟩

namespace Decode

/-! ## The recognizer's syntax tests -/

/-- `isBVarAt`, read. -/
theorem isBVarAt_eq {args : List Expr} {i m : Nat} (h : isBVarAt args i m = true) :
    args[i]? = some (.bvar m) := by
  unfold isBVarAt at h
  split at h
  · rename_i j hj; rw [hj, beq_iff_eq.mp h]
  · exact nomatch h

/-- The level arguments `isConstAt` accepts are the level parameters. -/
theorem params_of_zip : ∀ {us : List Level} {lps : List Name}, us.length = lps.length →
    (∀ x ∈ us.zip lps, (match x with | (.param a, b) => a == b | _ => false) = true) →
    us = lps.map .param
  | [], [], _, _ => rfl
  | u :: us, l :: lps, hl, h => by
    have h0 := h (u, l) List.mem_cons_self
    have ih := params_of_zip (us := us) (lps := lps) (by simpa using hl)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases u <;> simp at h0
    simp [h0, ih]
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- `isConstAt`, read. -/
theorem isConstAt_eq {e : Expr} {c : Name} {lps : List Name} (h : isConstAt e c lps = true) :
    e = .const c (lps.map .param) := by
  unfold isConstAt at h
  split at h
  · rename_i c' us
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hl⟩, hall⟩ := h
    rw [params_of_zip hl hall]
  · exact nomatch h

/-- A spine is its head applied to its arguments. -/
theorem spine_foldl {h : Expr} : ∀ {e : Expr} {as : List Expr}, spine e = (h, as) →
    e = as.foldl .app h := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro as hs
    rcases hsf : spine f with ⟨h', as'⟩
    simp only [spine, hsf, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rw [List.foldl_append, ← ihf hsf]; rfl
  | _ => intro as hs; simp only [spine, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl

/-- `isMinorBody`, read: the variable `m` applied to `bvar (L-1), …, bvar (L-nf)`. -/
theorem isMinorBody_eq {e : Expr} {m L nf : Nat} (h : isMinorBody e m L nf = true) :
    ∃ as : List Expr, e = as.foldl .app (.bvar m) ∧ as.length = nf ∧
      ∀ f < nf, as[f]? = some (.bvar (L - 1 - f)) := by
  unfold isMinorBody at h
  split at h
  · rename_i hd as hs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨rfl, hl⟩, hb⟩ := h
    exact ⟨as, spine_foldl hs, hl, fun f hf => isBVarAt_eq (hb f hf)⟩
  · exact nomatch h

/-- `ctorAlts`, read: one alternative per constructor, with its field count. -/
theorem ctorAlts_spec {P : List ConstantInfo} : ∀ {cs : List Name} {alts : List CasesAltInfo},
    ctorAlts P cs = some alts → alts.length = cs.length ∧ ∀ {i : Nat} {c : Name} {cv : ConstructorVal},
      cs[i]? = some c → findConst P c = some (.ctorInfo cv) → altFields alts i = cv.numFields
  | [], alts, h => by
    simp only [ctorAlts, Option.some.injEq] at h; subst h; exact ⟨rfl, fun hi => by simp at hi⟩
  | c :: cs, alts, h => by
    unfold ctorAlts at h
    split at h
    · rename_i cv' as hc' has
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hi⟩ := ctorAlts_spec has
      refine ⟨by simp [hl], fun {i c'' cv} hci hf => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hci; subst hci
        rw [hc', Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hf; subst hf
        rfl
      | succ i => exact hi (by simpa using hci) hf
    · exact nomatch h

/-! ## Their readings in con-leche's syntax -/

/-- The reading of a spine is the spine of the readings. -/
theorem toCL?_foldl : ∀ (as : List Expr) (f : Expr) {c : ConLeche.Expr},
    toCL? (as.foldl .app f) = some c →
    ∃ cf cas, toCL? f = some cf ∧ List.Forall₂ (fun a ca => toCL? a = some ca) as cas ∧
      c = ConLeche.Expr.mkAppN cf cas
  | [], _, c, h => ⟨c, [], h, .nil, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨cf', cas, hf', hall, rfl⟩ := toCL?_foldl as (.app f a) h
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hf'
    obtain ⟨cf, hcf, ca, hca, rfl⟩ := hf'
    exact ⟨cf, ca :: cas, hcf, .cons hca hall, rfl⟩

/-- The reading of `n` λs is `n` λs over the reading of the body. -/
theorem toCL?_peelLams : ∀ (n : Nat) {e b : Expr} {ce : ConLeche.Expr}, peelLams n e = some b →
    toCL? e = some ce → ∃ cb, toCL? b = some cb ∧ clLams ce = (n + (clLams cb).1, (clLams cb).2)
  | 0, e, b, ce, h, hc => by
    simp only [peelLams, Option.some.injEq] at h; subst h; exact ⟨ce, hc, by simp⟩
  | n + 1, e, b, ce, h, hc => by
    cases e <;> simp only [peelLams, reduceCtorEq] at h
    rename_i t b' _
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨ct, -, cb', hcb', rfl⟩ := hc
    obtain ⟨cb, hcb, hl⟩ := toCL?_peelLams n h hcb'
    refine ⟨cb, hcb, ?_⟩
    simp only [clLams, hl, Prod.mk.injEq, and_true]
    omega

/-- A spine whose head is no λ has no leading λ. -/
theorem clLams_mkAppN : ∀ (as : List ConLeche.Expr) {f : ConLeche.Expr}, clLams f = (0, f) →
    clLams (ConLeche.Expr.mkAppN f as) = (0, ConLeche.Expr.mkAppN f as)
  | [], _, hf => hf
  | a :: as, f, _ => clLams_mkAppN as (f := .app f a) rfl

/-- Arguments that are the field variables read as `fbv`. -/
theorem forall₂_fbv {as : List Expr} {cas : List ConLeche.Expr} {n L : Nat}
    (hall : List.Forall₂ (fun a ca => toCL? a = some ca) as cas) (hl : as.length = n)
    (hb : ∀ f < n, as[f]? = some (.bvar (L - 1 - f))) : cas = SemCases.fbv n L := by
  have hl' := SemCases.forall₂_length hall
  apply List.ext_getElem?
  intro f
  by_cases hf : f < n
  · obtain ⟨ca, hca, hr⟩ := SemCases.forall₂_getElem? hall (hb f hf)
    simp only [toCL?, Option.some.injEq] at hr
    rw [hca, ← hr]
    simp [SemCases.fbv, hf]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [SemCases.fbv]; omega)]

/-- The level parameters, read. -/
theorem mapM_param (lps : List Name) :
    (lps.map Level.param).mapM Level.toCL = some ((lps.map Name.toCL).map ConLeche.Level.param) := by
  induction lps with
  | nil => rfl
  | cons l lps ih => simp [List.mapM_cons, Level.toCL, ih]

/-! ## A block's constructor records -/

/-- The name of a constructor record. Reference: none. -/
def ctorName? : ConLeche.ConstantInfo → Option ConLeche.Name
  | .ctorInfo cv .. => some cv.name
  | _ => none

/-- A tail of recursor records holds no constructor
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:227 blockSplitRecs`). -/
theorem blockSplitRecs_ctors : ∀ {block : List ConLeche.ConstantInfo}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitRecs block = some rs → block.filterMap ctorName? = []
  | [], _, _ => rfl
  | .recInfo .. :: _, _, h => by
    simp only [ConLeche.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨_, h', -⟩ := h
    simpa [ctorName?] using blockSplitRecs_ctors h'
  | .axiomInfo .. :: _, _, h | .defnInfo .. :: _, _, h | .thmInfo .. :: _, _, h
  | .indInfo .. :: _, _, h | .ctorInfo .. :: _, _, h => nomatch h

/-- The constructors a block's split reads are its constructor records, in order
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:235 blockSplitCtors`). -/
theorem blockSplitCtors_ctors : ∀ {block : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitCtors block = some (cs, rs) → cs.map (·.1.name) = block.filterMap ctorName?
  | .ctorInfo .. :: _, _, _, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp [ctorName?, blockSplitCtors_ctors h']
  | [], _, _, h | .recInfo .. :: _, _, _, h | .axiomInfo .. :: _, _, _, h
  | .defnInfo .. :: _, _, _, h | .thmInfo .. :: _, _, _, h | .indInfo .. :: _, _, _, h => by
    simp only [ConLeche.blockSplitCtors] at h
    obtain ⟨rs', h', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact (blockSplitRecs_ctors h').symm

/-- The constructors a block's split reads are its constructor records, in order
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_ctors : ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplit block = some (cvTs, cs, rs) → cs.map (·.1.name) = block.filterMap ctorName?
  | .indInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [List.filterMap_cons, ctorName?]
    exact blockSplit_ctors h'
  | [], _, _, _, h | .recInfo .. :: _, _, _, _, h | .axiomInfo .. :: _, _, _, _, h
  | .defnInfo .. :: _, _, _, _, h | .thmInfo .. :: _, _, _, _, h | .ctorInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact blockSplitCtors_ctors h'

/-- The constructor records `blockOf?` writes carry the translated names of the constructors. -/
theorem ctorRecords_names {T : ConLeche.Name} : ∀ {cs : List ConstructorVal}
    {L : List ConLeche.ConstantInfo},
    cs.map (fun c => (cvOf? c.toConstantVal).bind fun cv =>
      some (ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields T)) = L.map some →
    L.filterMap ctorName? = cs.map (Name.toCL ·.name)
  | [], [], _ => rfl
  | c :: cs, x :: L, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hx, hl⟩ := h
    cases hcv : cvOf? c.toConstantVal <;>
      simp only [hcv, Option.bind_none, Option.bind_some, Option.some.injEq, reduceCtorEq] at hx
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    subst hx
    simp [ctorName?, ctorRecords_names hl]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- The constructors `blockOf?` looks up by name have those names. -/
theorem ctorLookup_names {P : List ConstantInfo} : ∀ {ns : List Name} {cs : List ConstructorVal},
    ns.map (fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = cs.map some → cs.map (·.name) = ns
  | [], [], _ => rfl
  | n :: ns, c :: cs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hc, hl⟩ := h
    split at hc
    · rename_i c' hf
      cases hc
      simp only [List.map_cons, ctorLookup_names hl, List.cons.injEq, and_true]
      exact (findDecl_mem (P := P) hf).2
    · exact nomatch hc
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-! ## Quotient records -/

/-- **A quotient record of `P` is stored as its pin expects**: con-leche matches the translated
record to the quotient package's pin at its slot (`CL ConLeche/Kernel/Basis.lean:175
quotPinHit`) and stores the pin's constant at the record's level-parameter names
(`CL ConLeche/Kernel/Basis.lean:169 quotAt`, `CL ConLeche/Kernel/Checker.lean:467
checkQuotRecord`), under the translated name. Reference: the quotient constants
`MR P/PCUICWcbvEval.v:231 eval` treats as axioms of the environment. -/
theorem _root_.EraseProof.ConLecheAccepts.find?_quot {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : QuotVal}
    (hv : findDecl P c = some (.quotInfo v)) :
    ∃ cv, cvOf? v.toConstantVal = some cv ∧ ConLeche.quotPinHit (quotKindOf v.kind) cv = true ∧
      env.find? (Name.toCL c) = some (ConLeche.quotAt (quotKindOf v.kind) cv) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hcv] at hL
  | some cv =>
  have hd : declOf? P (.quotInfo v) = some [.quotDecl (quotKindOf v.kind) cv] := by
    simp [declOf?, hcv]
  obtain ⟨⟨e, e', hrun⟩, hst⟩ := h.stored hmem hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hpin : ConLeche.quotPinHit (quotKindOf v.kind) cv = true := hk.1
  have hf := find?_of_single rfl hst
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, rfl, hpin, ?_⟩
  rw [ConLeche.ConstantInfo.name, quotAt_cv hpin] at hf
  rw [← hn]; exact hf

end Decode

end EraseProof
