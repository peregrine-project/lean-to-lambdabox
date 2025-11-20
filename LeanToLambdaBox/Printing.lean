import LeanToLambdaBox.Basic

inductive sexpr: Type where
  | atom (a: String)
  | list (l: List sexpr)
deriving Inhabited

def sexpr.toString: sexpr -> String
  | atom a => a
  | list l => "(" ++ (l.map sexpr.toString |> String.intercalate " ") ++ ")"

instance : ToString sexpr where
  toString := sexpr.toString

class Serialize (α: Type): Type where
  to_sexpr: α → sexpr

open Serialize

def quote_atom (s: String): sexpr := "\"" ++ s ++ "\"" |> .atom

instance : Serialize Nat where
  to_sexpr | n => .atom n.repr

instance : Serialize LocalName where
  to_sexpr
  | .named name => .list [ .atom "nNamed", quote_atom name ]
  | .anon => .atom "nAnon"

instance : Serialize Ident where
  to_sexpr := quote_atom

instance [Serialize α]: Serialize (List α) where
  to_sexpr | l => l |>.map to_sexpr |> .list

def modpath.to_sexpr: ModPath -> sexpr
  | .MPfile dp => .list [ .atom "MPfile", Serialize.to_sexpr dp ]
  | .MPdot mp id => .list [ .atom "MPdot", to_sexpr mp, Serialize.to_sexpr id ]

instance : Serialize ModPath where to_sexpr := modpath.to_sexpr

instance : Serialize Kername where
  to_sexpr
  | ⟨mp, id⟩ => .list [ to_sexpr mp, to_sexpr id ] 

instance: Serialize InductiveId where
  to_sexpr | ⟨kn, idx⟩  => .list [ .atom "inductive", to_sexpr kn, to_sexpr idx ]

instance [Serialize α] [Serialize β]: Serialize (α × β) where
  to_sexpr | (a, b)  => .list [ to_sexpr a, to_sexpr b ]

instance: Serialize ProjectionInfo where
  to_sexpr | ⟨indinfo, npars, idx⟩ => .list [ .atom "projection", to_sexpr indinfo, to_sexpr npars, to_sexpr idx ]

instance [Serialize α] [Serialize β]: Serialize (α × β) where
  to_sexpr | (a, b) => .list [ to_sexpr a, to_sexpr b ]

instance: Serialize PrimTag where
  to_sexpr | .primInt => .atom "primInt"

instance: Serialize (BitVec n) where
  to_sexpr b := let i := b.toFin.toNat; .atom ("\"" ++ i.repr ++ "\"")

instance: Serialize PrimVal where
  to_sexpr | ⟨.primInt, i⟩ => to_sexpr (PrimTag.primInt, (i: BitVec 63))

mutual
  partial def LBTerm.to_sexpr: LBTerm -> sexpr
  | .box => .atom "tBox"
  | .bvar n => .list [ .atom "tRel", to_sexpr n ]
  | .lambda na t => .list [ .atom "tLambda", to_sexpr na, t.to_sexpr ]
  | .letIn na b t => .list [ .atom "tLetIn", to_sexpr na, b.to_sexpr, t.to_sexpr ]
  | .app u v => .list [ .atom "tApp", u.to_sexpr, v.to_sexpr ]
  | .const k => .list [ .atom "tConst", to_sexpr k ]
  | .construct ind n args => .list [ .atom "tConstruct", to_sexpr ind, to_sexpr n, .list (args.map LBTerm.to_sexpr)  ]
  | .case indn c brs => .list [
      .atom "tCase",
      to_sexpr indn,
      c.to_sexpr,
      .list (brs.map fun (names, branch) => .list [ to_sexpr names, LBTerm.to_sexpr branch ])
      ]
  | .proj p c => .list [ .atom "tProj", to_sexpr p, c.to_sexpr ]
  | .fix mfix idx => .list [ .atom "tFix", .list (mfix.map edef.to_sexpr), to_sexpr idx ]
  | .fvar .. => unreachable!
  | .prim p => .list [ .atom "tPrim", to_sexpr p]

  partial def edef.to_sexpr: @FixDef LBTerm -> sexpr
  | ⟨name, body, principal⟩ => .list [ .atom "def", to_sexpr name, body.to_sexpr, to_sexpr principal ]
end

instance : Serialize LBTerm where to_sexpr := LBTerm.to_sexpr

def LBType.to_sexpr: LBType -> sexpr
| .box => .atom "TBox"
| .any => .atom "TAny"
| .arr dom codom => .list [.atom "TArr", dom.to_sexpr, codom.to_sexpr]
| .var i => .list [.atom "TVar", Serialize.to_sexpr i]
| .ind iid => .list [.atom "TInd", Serialize.to_sexpr iid]
| .const kn => .list [.atom "TConst", Serialize.to_sexpr kn]
| .app fn arg => .list [.atom "TApp", fn.to_sexpr, arg.to_sexpr]
  
instance: Serialize LBType where to_sexpr := LBType.to_sexpr

instance : Serialize ConstructorBody where
  to_sexpr cb := to_sexpr ((cb.name, cb.args), cb.originalArity) -- tuples are not associative on the same side in Rocq and Lean.

instance : Serialize ProjectionBody where
  to_sexpr pb := to_sexpr (pb.name, pb.type)

instance : Serialize AllowedEliminations where
  to_sexpr
  | .IntoSProp => .atom "IntoSProp"
  | .IntoPropSProp => .atom "IntoPropSProp"
  | .IntoSetPropSProp => .atom "IntoSetPropSProp"
  | .IntoAny => .atom "IntoAny"

instance : Serialize Bool where
  to_sexpr
  | .true => .atom "true"
  | .false => .atom "false"

instance: Serialize TypeVarInfo where
  to_sexpr inf := .list [.atom "type_var_info", to_sexpr inf.name, to_sexpr inf.isLogical, to_sexpr inf.isArity, to_sexpr inf.isSort]

instance : Serialize OneInductiveBody where
  to_sexpr | ⟨name, prop, kelim, tvars, ctors, projs⟩ => .list [ .atom "one_inductive_body", to_sexpr name, to_sexpr prop, to_sexpr kelim, to_sexpr tvars, to_sexpr ctors, to_sexpr projs ]

instance : Serialize RecursivityKind where
  to_sexpr
  | .finite => .atom "Finite"
  | .cofinite => .atom "CoFinite"
  | .bifinite => .atom "BiFinite"

instance : Serialize MutualInductiveBody where
  to_sexpr | ⟨reckind, nparams, bodies⟩ => .list [ .atom "mutual_inductive_body", to_sexpr reckind, to_sexpr nparams, to_sexpr bodies ]

instance : [Serialize α] -> Serialize (Option α) where
  to_sexpr
  | .none => .atom "None"
  | .some a => .list [.atom "Some", to_sexpr a]

instance : Serialize ConstantBody where
  to_sexpr cb := .list [.atom "constant_body", to_sexpr cb.type, to_sexpr cb.body] 

instance : Serialize GlobalDecl where
  to_sexpr
  | .constantDecl cb => .list [ .atom "ConstantDecl", to_sexpr cb ]
  | .inductiveDecl mib => .list [ .atom "InductiveDecl", to_sexpr mib ]
  | .typeAliasDecl body => .list [ .atom "TypeAliasDecl", to_sexpr body ]

/-- The Rocq/Coq lexer expects `"` characters in string literals to be represented by the sequence `""`. This is cursed. -/
def rocq_escape (s: String): String :=
  s.toList |>.map (fun c: Char => if c = '"' then [c, c] else [c]) |>.flatten |>.asString

/-- Print with surrounding `"` characters and internal `"` characters doubled, for copy-pasting into Rocq. -/
def rocq_print (s: String): IO Unit := do
  IO.print '"'
  IO.print <| rocq_escape s
  IO.print '"'
