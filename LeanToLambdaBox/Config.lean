/-- How constructors are represented in the expression tree. -/
inductive ConstructorStyle: Type where
  /-- Constructors appear alone in the expression tree, and are applied to their arguments as functions. They may be underapplied. -/
  | value
  /-- Constructions appear in the expression tree in a node together with all their arguments. -/
  | applied

structure Config: Type where
  constructors: ConstructorStyle
