(* Lean's Decidable is a structure `Decidable.intro (decide : Bool) (reflects_decide : proof)`; with all
   constructor arguments kept, the erased proof field is a box. *)
type decidable = Intro of bool * Obj.t
let box = let rec f _ = Obj.repr f in Obj.repr f
let dec_of_bool b = Intro (b, box)
[@@inline always]
