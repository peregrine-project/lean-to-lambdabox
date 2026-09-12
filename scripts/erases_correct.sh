#!/usr/bin/env bash
# The premise audit of T5: `erases_correct` has the eight binders and no named premise.
# Elaborates three checks and diffs their output against test/erases_correct.expected.
#   * `#check @erases_correct` — the binder list, which a re-added premise would change;
#   * an `example` assigning `@erases_correct` to the premise-free statement, which fails
#     to elaborate if the theorem takes anything beyond its five type binders;
#   * `erases_correct_target_shape`, closed by `Iff.rfl` against `ErasesCorrectStmt`, whose
#     printed type is `doc/rework/01-DESIGN.md` §5's spelling of the eight binders.
# Exit code is the diff's.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

probe=$(mktemp --suffix=.lean) || exit 2
actual=$(mktemp) || exit 2
trap 'rm -f "$probe" "$actual"' EXIT

cat > "$probe" <<'EOF'
import LeanToLambdaBox
open Lean Lean4Lean LeanToLambdaBox
set_option pp.mvars false

#check @LeanToLambdaBox.erases_correct

example : ∀ {env : VEnv} {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Γspec Γ : GlobalDeclarations}, ErasesCorrectStmt env bo Us fl Γspec Γ :=
  @erases_correct

theorem erases_correct_target_shape {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    ErasesCorrectStmt env bo Us fl Γspec Γ ↔
    ∀ {e v : Expr} {ve : VExpr} {t₀ t : LBTerm},
      env.WF → TrExprS env Us [] e ve → SEval env bo Us fl [] e v →
      Erases env Us [] e t₀ → Lower Γspec t₀ t → ErasesEnv env bo Γspec t₀ →
      LowerEnv Γspec Γ → UpstreamAsks env →
      ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' :=
  Iff.rfl

#check @erases_correct_target_shape
EOF

lake env lean "$probe" | sed "s|$probe|<probe>|g" > "$actual" 2>&1

diff -u test/erases_correct.expected "$actual"
