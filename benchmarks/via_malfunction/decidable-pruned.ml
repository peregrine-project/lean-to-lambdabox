(* Lean's Decidable when irrelevant constructor args are erased: `Decidable.intro (decide : Bool)`, a
   single-constructor single-field type that peregrine's unboxing represents as the Bool itself. *)
type decidable = Intro of bool [@@unboxed]
let dec_of_bool b = Intro b
[@@inline always]
