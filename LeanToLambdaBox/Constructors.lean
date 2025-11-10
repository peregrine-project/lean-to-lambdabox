import LeanToLambdaBox.TypedML

open TypedML

namespace Constructors

def mkApp (f: Expression c globals inductives locals) (args: List (Expression c globals inductives locals)) :=
  match args with
  | [] => f
  | x::xs => mkApp (.app f x) xs

inductive CollectResult α: Nat -> Type where
  | enough n (revargs: SizedList α n) (extra: List α): CollectResult α n
  | missing m n (revargs: SizedList α m): CollectResult α (m+n)

def collect (args: List α) (count: Nat): CollectResult α count := Nat.zero_add count ▸ collectAux 0 .nil args count
where
  collectAux (m: Nat) (collected: SizedList α m) (remaining: List α) (count: Nat): CollectResult α (m+count) :=
  match count, remaining with
  | 0, args => .enough m collected args
  | c+1, [] => .missing m (c+1) collected
  | c+1, h::t =>
    Nat.succ_add_eq_add_succ m c ▸ collectAux (m+1) (.cons m h collected) t c

def etaIn
    (m n: Nat)
    (revargs: SizedList (Expression cfg globals inductives locals) m)
    (whenDone: (endlocals: LocalValueContext) -> SizedList (Expression cfg globals inductives endlocals) (m+n) -> Expression cfg globals inductives endlocals)
  : Expression cfg globals inductives locals
  :=
  match n with
  | 0 => whenDone locals revargs
  | n+1 =>
    let ⟨_, ext⟩ := locals.extend;
    -- WeakenExpression is a no-op, so this could be implemented as an unsafe cast if the compiler does not specialize enough.
    let brevargs := revargs.map ext.weakenExpression;
    let whenDoneB := Nat.succ_add_eq_add_succ m n ▸ whenDone;
    .lambda .anonymous ext (etaIn (m+1) n (.cons m (.local ext.newId) brevargs) whenDoneB)

variable {cfg: Config} {hvalue: cfg.constructors = .value}
include cfg hvalue

theorem notApplied: ¬ (cfg.constructors = .applied) := by
  intro
  rewrite [hvalue] at *
  contradiction

def cfg' {cfg: Config} := { cfg with constructors := .applied }

mutual

def transformExpression (e: Expression cfg globals inductives locals): Expression (@cfg' cfg) globals inductives locals :=
  transformExpressionAux e []

def transformExpressionAux (e: Expression cfg globals inductives locals) (args: List (Expression (@cfg' cfg) globals inductives locals)): Expression (@cfg' cfg) globals inductives locals :=
    match e with
    | .global id => mkApp (.global id) args
    | .local id => mkApp (.local id) args
    | .lambda name ext e => mkApp (.lambda name ext (transformExpression e)) args
    | .app f x => transformExpressionAux f (transformExpression x :: args)
    | .constructorApp h .. => False.elim (@notApplied cfg hvalue h)
    | .constructorVal _ cid =>
      let whenDone endlocals (revargs: SizedList _ cid.arity): Expression cfg' globals inductives endlocals :=
        .constructorApp rfl cid (revargs.rev |> ExpressionSizedList.ofSizedList);
      match h: cid.arity, collect args cid.arity with
      | .(_), .enough _ revargs extra => mkApp (whenDone locals (h ▸ revargs)) extra
      | .(m+n), .missing m n revargs => etaIn m n revargs (h ▸ whenDone)

-- This is in the mutual block because this allows the implicit parameter hvalue to transformExpression to be inferred for some reason
def transformProgram (p: Program cfg aliases globals inductives): Program (@cfg' cfg) aliases globals inductives :=
  match p with
  | .empty => .empty
  | .typeAlias p name ext tvarnames t => .typeAlias (transformProgram p) name ext tvarnames t
  | .mutualInductiveDecl p ext decl => .mutualInductiveDecl (transformProgram p) ext decl
  | .valueDecl p name ext e t =>.valueDecl (transformProgram p) name ext (transformExpression e) t
end

end Constructors
