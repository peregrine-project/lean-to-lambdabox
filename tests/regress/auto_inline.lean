import LeanToLambdaBox

/-!
The option `auto_inline_typeclass_dispatch`. It is off by default: `off.ast.inlinings` lists nothing.
Turned on, it marks instances and trivial aliases for inlining in `on.ast.inlinings`, and leaves the
program unchanged (`on.ast` equals `off.ast`). The `#guard_msgs` below lists each decision. A
candidate is marked only if:
- its body, with the constants marked so far inlined into it, has at most 40 nodes: in the chain
  `i0` to `i3`, where each instance calls the previous one twice, `i2` is refused, and `i3` is marked
  because it then refers to `i2` without inlining it;
- its erased body is a value, so that inlining it repeats no computation: `instApp` (a constructor
  applied to a call) and `instLet` (a `let` of a call) are refused, `instLam` (a λ) is marked;
- it is not tagged `@[noinline]`: `instNo` and `dblNo` are refused, `dblYes` is marked;
- it is not recursive: `depthInst` is erased to a fixpoint and is not considered.
-/

-- peregrine: validate on.ast --attributes=on.ast.inlinings
-- peregrine: eval run.ast --attributes=run.ast.inlinings

inductive N | z | s (n : N)

def dbl (n : N) : N := .s (.s n)

class C0 where f : N → N
class C1 where f : N → N
class C2 where f : N → N
class C3 where f : N → N
instance i0 : C0 := ⟨fun n => .s n⟩
instance i1 : C1 := ⟨fun n => C0.f (C0.f n)⟩
instance i2 : C2 := ⟨fun n => C1.f (C1.f n)⟩
instance i3 : C3 := ⟨fun n => C2.f (C2.f n)⟩

class Tbl where get : N → N
instance instApp : Inhabited N := ⟨dbl .z⟩
instance instLet : Tbl := let s := dbl .z; ⟨fun _i => s⟩
instance instLam : Tbl := ⟨fun i => dbl i⟩

class OpNo where op : N → N
@[noinline] instance instNo : OpNo := ⟨fun n => .s n⟩
@[noinline] def dblNo : N → N := dbl
def dblYes : N → N := dbl

class Depth (n : N) where val : N
def depthInst (n : N) : Depth n :=
  N.casesOn (motive := fun n => Depth n) n ⟨.z⟩ (fun m => ⟨.s (depthInst m).val⟩)
attribute [instance] depthInst

/-- Every candidate, combined so that each one is used. -/
def useAll (n : N) : N :=
  C3.f <| dblNo <| dblYes <| OpNo.op <| N.casesOn (motive := fun _ => N) (default : N)
    (Tbl.get (self := instLet) n) (fun _m => Tbl.get (self := instLam) (Depth.val (n := n)))

#erase useAll to "off.ast"

/--
info: Auto-inlining trivial alias C3.f (inlined size 3).
---
info: Auto-inlining trivial alias C2.f (inlined size 3).
---
info: Auto-inlining trivial alias C1.f (inlined size 3).
---
info: Auto-inlining trivial alias C0.f (inlined size 3).
---
info: Auto-inlining typeclass instance i0 (inlined size 6).
---
info: Auto-inlining typeclass instance i1 (inlined size 26).
---
info: Not auto-inlining typeclass instance i2: inlined size 66 exceeds 40.
---
info: Auto-inlining typeclass instance i3 (inlined size 16).
---
info: Not auto-inlining trivial alias dblNo: it is tagged @[noinline].
---
info: Auto-inlining trivial alias dblYes (inlined size 1).
---
info: Auto-inlining trivial alias OpNo.op (inlined size 3).
---
info: Not auto-inlining typeclass instance instNo: it is tagged @[noinline].
---
info: Auto-inlining trivial alias Inhabited.default (inlined size 4).
---
info: Not auto-inlining typeclass instance instApp: its body is not a value.
---
info: Auto-inlining trivial alias Tbl.get (inlined size 3).
---
info: Not auto-inlining typeclass instance instLet: its body is not a value.
---
info: Auto-inlining typeclass instance instLam (inlined size 6).
---
info: Auto-inlining trivial alias Depth.val (inlined size 4).
---
info: val main: unit -> unit
-/
#guard_msgs (info, drop warning) in
#erase useAll config {auto_inline_typeclass_dispatch := true} to "on.ast"

def run : N := useAll (.s .z)
#erase run config {auto_inline_typeclass_dispatch := true} to "run.ast"
