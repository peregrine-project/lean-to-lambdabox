(* Lean's Decidable when irrelevant constructor args are erased and peregrine does not unbox:
   `Decidable.intro (decide : Bool)`, a block with one field. *)
type decidable = Intro of bool
let dec_of_bool b = Intro b
[@@inline always]
