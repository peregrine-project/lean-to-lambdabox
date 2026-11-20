import EraseProof.Spec
import EraseProof.Test.NV1Data

/-!
# `declOf?` on an inductive outside its own `all`, on an unsafe one and on a nested one

A non-head inductive is accepted only if it lies in its head's `all` and in its own; an unsafe
inductive rejects the program, and so does a nested one (`numNested ≠ 0`); NV-1's inductive is still translated.
-/

open Lean EraseProof EraseProof.Test

namespace EraseProof.Test.DeclOf

theorem stray_rejected :
    declOf? [.inductInfo NV1.B_ind, .inductInfo { NV1.B_ind with name := `B2 }]
      (.inductInfo { NV1.B_ind with name := `B2 }) = none := by decide +kernel

theorem inBlock_accepted :
    declOf? [.inductInfo { NV1.B_ind with all := [`B, `B2] },
        .inductInfo { NV1.B_ind with name := `B2, all := [`B, `B2] }]
      (.inductInfo { NV1.B_ind with name := `B2, all := [`B, `B2] }) = some [] := by
  decide +kernel

theorem nv1_head_accepted : (declOf? NV1.P (.inductInfo NV1.B_ind)).isSome = true := by
  decide +kernel

theorem unsafe_rejected : declOf? [] (.inductInfo { NV1.B_ind with isUnsafe := true }) = none := by
  decide +kernel

theorem nested_rejected :
    declOf? [.inductInfo { NV1.B_ind with numNested := 1 }]
      (.inductInfo { NV1.B_ind with numNested := 1 }) = none := by
  decide +kernel

end EraseProof.Test.DeclOf
