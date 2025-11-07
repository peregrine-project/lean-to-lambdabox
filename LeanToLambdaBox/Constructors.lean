module
public import LeanToLambdaBox.TypedML

open TypedML

namespace Constructors

variable {cfg: Config} {hvalue: cfg.constructors = .value}
include cfg hvalue

theorem notApplied: ¬ (cfg.constructors = .applied) := by
  intro
  rewrite [hvalue] at *
  contradiction

def cfg' := { cfg with constructors := .applied }

def mkApp (f: Expression c globals inductives locals) (args: List (Expression c globals inductives locals)) :=
  match args with
  | [] => f
  | x::xs => mkApp (.app locals f x) xs

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

/-- Noncomputable because it depends on weakenExpression -/
noncomputable def etaIn
    (m n: Nat)
    (revargs: SizedList (Expression cfg globals inductives locals) m)
    (whenDone: forall locals, SizedList (Expression cfg globals inductives locals) (m+n) -> Expression cfg globals inductives locals)
  : Expression cfg globals inductives locals
  :=
  match n with
  | 0 => whenDone locals revargs
  | n+1 =>
    let ⟨bodylocals, ext⟩ := locals.extend;
    -- This could be implemented as an unsafe cast if types are right. Or maybe, depending on implementation, the compiler can specialize enough.
    let brevargs: SizedList (Expression cfg globals inductives bodylocals) m := revargs.map (locals.weakenExpression ext);
    let whenDoneB := Nat.succ_add_eq_add_succ m n ▸ whenDone
    let body: Expression cfg globals inductives bodylocals := etaIn (m+1) n (.cons m (.local bodylocals ext.newId) brevargs) whenDoneB;
    .lambda locals bodylocals ext body

mutual
-- noncomputable because of etaIn
noncomputable def transformExpression locals (e: Expression cfg globals inductives locals): Expression cfg' globals inductives locals :=
  transformExpressionAux locals e []

noncomputable def transformExpressionAux locals (e: Expression cfg globals inductives locals) (args: List (Expression cfg' globals inductives locals)): Expression cfg' globals inductives locals :=
    match e with
    | .global locals id => mkApp (.global locals id) args
    | .local locals id => mkApp (.local locals id) args
    | .lambda locals bodylocals ext e =>
        let e' := transformExpression bodylocals e;
        mkApp (.lambda locals bodylocals ext e') args
    | .constructorApp h .. => False.elim (@notApplied cfg hvalue h)
    | .app locals f x =>
      let x' := transformExpression locals x;
      transformExpressionAux locals f (x' :: args)
    | .constructorVal _ locals cid =>
      let whenDone locals (revargs: SizedList _ cid.arity): Expression cfg' globals inductives locals :=
        .constructorApp rfl locals cid (revargs.rev |> ExpressionSizedList.ofSizedList);
      match h: cid.arity, collect args cid.arity with
      | .(_), .enough _ revargs extra => mkApp (whenDone locals (h ▸ revargs)) extra
      | .(m+n), .missing m n revargs => etaIn m n revargs (h ▸ whenDone)

-- This is in the mutual block because this allows the implicit parameter hvalue to transformExpression to be inferred for some reason
/- Noncomputable because of transformExpression -/
noncomputable def transformProgram (p: Program cfg aliases globals inductives): Program cfg' aliases globals inductives :=
  match p with
  | .empty => .empty
  | .valueDecl tvars aliases globals newglobals ext inductives p e t =>
    let p' := transformProgram p;
    let e' := transformExpression .empty e;
    .valueDecl tvars aliases globals newglobals ext inductives p' e' t
  | .mutualInductiveDecl tvars aliases globals inductives newinductives spec ext p decl =>
    let p' := transformProgram p;
    .mutualInductiveDecl tvars aliases globals inductives newinductives spec ext p' decl 
  | .typeAlias tvars aliases newaliases ext globals inductives p t =>
    let p' := transformProgram p;
    .typeAlias tvars aliases newaliases ext globals inductives p' t
end

end Constructors
