import EraseProof.Typing.Basic
import LeanToLambdaBox.Erasure.Pure

/-!
# Universe instantiation of the translation

The shipping eraser instantiates a constant's level parameters `ps` by the levels `us` of an
occurrence with the structural `Erasure.Pure.instLevels`. Its model meaning is lean4lean's
`VExpr.instL`: `TrS.instLevels` says that the translation of the instantiated term is the
instantiated translation, in the instantiated context, exactly (a `TrS`, not a `TrExpr`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- `Pure.instLevel`'s lookup of a parameter `n` in `ps.zip us` returns the level at `n`'s first
index in `ps`. Reference: none in MetaRocq (PCUIC indexes universe instances by position). -/
theorem find_zip {n : Name} : ∀ {ps : List Name} {us : List Level}, ps.length = us.length →
    ps.idxOf n < ps.length →
    ((ps.zip us).find? (·.1 == n)).map (·.2) = us[ps.idxOf n]?
  | [], _, _, h => by simp at h
  | p :: ps, u :: us, hl, h => by
    by_cases hp : (p == n) = true
    · simp [List.zip, hp, List.idxOf_cons]
    · have hl' : ps.length = us.length := by simpa using hl
      have h' : ps.idxOf n < ps.length := by
        simp [List.idxOf_cons, hp] at h; omega
      have ih := find_zip hl' h'
      simp only [List.zip] at ih
      simpa [List.zip, hp, List.idxOf_cons] using ih
  | _ :: _, [], hl, _ => by simp at hl

/-- A successful `mapM (VLevel.ofLevel Us)` translates each level at its own index. Reference: none
in MetaRocq (no level translation). -/
theorem mapM_get {Us : List Name} : ∀ {us : List Level} {us' : List VLevel},
    us.mapM (VLevel.ofLevel Us) = some us' → ∀ i (hi : i < us.length),
      ∃ hi' : i < us'.length, VLevel.ofLevel Us us[i] = some us'[i]
  | [], _, _, i, hi => by simp at hi
  | u :: us, us', h, i, hi => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨u', h1, us'', h2, rfl⟩ := h
    cases i with
    | zero => exact ⟨by simp, h1⟩
    | succ i =>
      obtain ⟨hi', h3⟩ := mapM_get h2 i (by simpa using hi)
      exact ⟨by simpa using hi', h3⟩

/-- The model meaning of `Pure.instLevel` on one level: if `u` translates to `u'` over the
parameters `ps`, then `Pure.instLevel ps us u` translates to `u'.inst us'` over `Us`, where `us'` is
the translation of `us`. Reference: `subst_instance` on levels
(`MR common/theories/Universes.v:2480 UnivSubst`), whose meaning in PCUIC needs no translation. -/
theorem ofLevel_instLevel {ps Us : List Name} {us : List Level} {us' : List VLevel}
    (hus : us.mapM (VLevel.ofLevel Us) = some us') (hlen : us.length = ps.length) :
    ∀ {u : Level} {u' : VLevel}, VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (Pure.instLevel ps us u) = some (u'.inst us')
  | .zero, u', h => by simp [VLevel.ofLevel] at h; subst h; rfl
  | .succ l, u', h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨l', h1, rfl⟩ := h
    simp [Pure.instLevel, VLevel.ofLevel, ofLevel_instLevel hus hlen h1, VLevel.inst]
  | .max a b, u', h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', h1, b', h2, rfl⟩ := h
    simp [Pure.instLevel, VLevel.ofLevel, ofLevel_instLevel hus hlen h1,
      ofLevel_instLevel hus hlen h2, VLevel.inst]
  | .imax a b, u', h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', h1, b', h2, rfl⟩ := h
    simp [Pure.instLevel, VLevel.ofLevel, ofLevel_instLevel hus hlen h1,
      ofLevel_instLevel hus hlen h2, VLevel.inst]
  | .param n, u', h => by
    simp only [VLevel.ofLevel] at h
    split at h
    · rename_i hi
      cases h
      have hfind := find_zip (n := n) hlen.symm hi
      have hi' : ps.idxOf n < us.length := hlen ▸ hi
      obtain ⟨hi'', hget⟩ := mapM_get hus _ hi'
      simp only [Pure.instLevel]
      split
      · rename_i p u hp
        rw [hp] at hfind
        simp only [Option.map_some, List.getElem?_eq_getElem hi', Option.some.injEq] at hfind
        subst hfind
        simp only [VLevel.inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'',
          Option.getD_some]
        exact hget
      · rename_i hp
        rw [hp] at hfind
        simp [List.getElem?_eq_getElem hi'] at hfind
    · cases h
  | .mvar _, u', h => by simp [VLevel.ofLevel] at h

/-- `ofLevel_instLevel` on a list of levels (the levels of a constant occurrence). Reference: the
`tConst` case of `subst_instance_constr` (`MR P/PCUICAst.v:404`). -/
theorem mapM_instLevel {ps Us : List Name} {us : List Level} {us' : List VLevel}
    (hus : us.mapM (VLevel.ofLevel Us) = some us') (hlen : us.length = ps.length) :
    ∀ {vs : List Level} {vs' : List VLevel}, vs.mapM (VLevel.ofLevel ps) = some vs' →
      (vs.map (Pure.instLevel ps us)).mapM (VLevel.ofLevel Us) = some (vs'.map (VLevel.inst us'))
  | [], vs', h => by simp at h; subst h; rfl
  | v :: vs, vs', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v', h1, vs'', h2, rfl⟩ := h
    simp [List.mapM_cons, ofLevel_instLevel hus hlen h1, mapM_instLevel hus hlen h2]

section
variable {venv : VEnv}

/-- Port of lean4lean `TrExprS.instL` (`l4l Verify/Typing/Lemmas.lean:1579`), under binders
(`Δ.instL`) and exact for the non-normalising `Pure.instLevels` (so `TrS`, not `TrExpr`, and no
`VEnv.WF`). Reference: `subst_instance` typing (`MR P/PCUICAst.v:404` on terms). -/
theorem TrS.instLevels (hus : us.mapM (VLevel.ofLevel Us) = some us')
    (hlen : us.length = ps.length) (H : TrS venv ps Δ e e') :
    TrS venv Us (Δ.instL us') (Pure.instLevels ps us e) (e'.instL us') := by
  have hls : ∀ l ∈ us', l.WF Us.length := VLevel.WF.of_mapM_ofLevel hus
  induction H with
  | bvar h1 => exact .bvar (VLCtx.find?_instL h1)
  | fvar h1 => exact .fvar (VLCtx.find?_instL h1)
  | sort h1 => exact .sort (ofLevel_instLevel hus hlen h1)
  | const h1 h2 h3 =>
    exact .const h1 (mapM_instLevel hus hlen h2) (by simp [h3])
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (VLCtx.instL_toCtx _ ▸ h1.instL hls) (VLCtx.instL_toCtx _ ▸ h2.instL hls) ih1 ih2
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (VLCtx.instL_toCtx _ ▸ h1.instL hls) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ h1.instL hls) (by simpa using h2.instL hls) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (VLCtx.instL_toCtx _ ▸ h1.instL hls) ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih

end

end EraseProof
