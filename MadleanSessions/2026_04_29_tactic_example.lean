/-
Simple Macro example, Custom tactic,
29-04-2026, Faculty of Mathematics of UCM
Jorge Mayoral

A simple macro/tactic example that implements an And proof builder called auto.

It only supports the introduction and elimination rules for conjunction (∧), namely:

      a : A
      b : B                  ab : A ∧ B          ab : A ∧ B
intro --------------   elim1 ----------   elim2 --------------
      ⟨a, b⟩ : A ∧ B         ab.left : A         ab.right : B

Using these rules, we can define an algorithm that, given a collection of hypotheses and a target goal, recursively applies the rules above to construct a proof.

Rules:

Exact match: one of the hypotheses has the same type as the goal.
Introduction: if the target has the form ?1 ∧ ?2, apply conjunction introduction and recursively solve the subgoals ?1 and ?2.
Elimination: if a hypothesis has the form ab : ?1 ∧ ?2, extend the context with the hypotheses ab.left : ?1 and ab.right : ?2.

Example:

example (ab : A ∧ B) : B ∧ A :=
1. The goal is to prove B ∧ A.
2. Since the goal is a conjunction, apply introduction and construct ⟨?1, ?2⟩ : B ∧ A.
3. By applying elimination to ab, we obtain two additional hypotheses:
  ab.left : A
  ab.right : B
4. The subgoal ?1 has type B, which exactly matches the hypothesis ab.right, so we assign ?1 := ab.right.
5. The subgoal ?2 has type A, which exactly matches the hypothesis ab.left, so we assign ?2 := ab.left.
6. The final proof term is:
  ⟨ab.right, ab.left⟩ : B ∧ A
-/
import Lean
variable (A B : Prop)
open Lean Elab Tactic Meta in

partial def autoSearch (goal : Expr) (hyps : Array Expr) (depth : Nat) : MetaM Expr := do
  -- DEBUG: Show current depth and goal at every recursive call
  dbg_trace "⟪autoSearch⟫ depth={depth} goal={← ppExpr goal}"

  if depth == 0 then
    dbg_trace "depth limit reached for goal: {← ppExpr goal}"
    throwError "auto: search depth exceeded"

  -- 1. Direct match: does any hypothesis have exactly this type?
  dbg_trace "[1] trying direct hyp match ({hyps.size} hyps)"
  for h in hyps do
    let hTy ← inferType h
    dbg_trace "checking hyp : {← ppExpr hTy}"
    if ← isDefEq hTy goal then
      dbg_trace "direct match found: {← ppExpr h} : {← ppExpr hTy}"
      return h

  -- 2. And-introduction: goal is `α ∧ β`
  dbg_trace " [2] trying And-intro"
  if let some (α, β) := andParts? goal then
    dbg_trace "goal is a conjunction: ({← ppExpr α}) ∧ ({← ppExpr β})"
    try
      dbg_trace "→ searching for LHS: {← ppExpr α}"
      let lhs ← autoSearch α hyps (depth - 1)
      dbg_trace "LHS found: {← ppExpr lhs}"
      dbg_trace "→ searching for RHS: {← ppExpr β}"
      let rhs ← autoSearch β hyps (depth - 1)
      dbg_trace "RHS found: {← ppExpr rhs}"
      let result ← mkAppM ``And.intro #[lhs, rhs]
      dbg_trace "And.intro succeeded: {← ppExpr result}"
      return result
    catch e =>
      dbg_trace "And-intro failed: {← e.toMessageData.toString}"
      pure ()

  -- 3. And-elimination: expand hypotheses that are conjunctions
  dbg_trace " [3] trying And-elim (expanding conjunctive hyps)"
  let mut extraHyps : Array Expr := #[]
  for h in hyps do
    let hTy ← inferType h
    if let some _ := andParts? hTy then
      dbg_trace "splitting hyp: {← ppExpr h} : {← ppExpr hTy}"
      let l ← mkAppM ``And.left  #[h]
      let r ← mkAppM ``And.right #[h]
      dbg_trace "→ And.left  : {← ppExpr (← inferType l)}"
      dbg_trace "→ And.right : {← ppExpr (← inferType r)}"
      extraHyps := extraHyps.push l |>.push r
  if extraHyps.size > 0 then
    dbg_trace "added {extraHyps.size} projected hyps, recursing..."
    return ← autoSearch goal (hyps ++ extraHyps) (depth - 1)

  dbg_trace "all strategies exhausted for: {← ppExpr goal}"
  throwError "auto: cannot construct {goal}"

where
  /-- If `e` is `And α β`, return `some (α, β)`, else `none`. -/
  andParts? (e : Expr) : Option (Expr × Expr) :=
    if e.isAppOfArity ``And 2
    then some (e.appFn!.appArg!, e.appArg!)
    else none


open Lean Elab Tactic Meta in
/-- The `auto` tactic: invokes `autoSearch` on the current goal. -/
elab "auto" : tactic => do
  let goal ← getMainGoal
  let goalTy ← goal.getType
  -- DEBUG: Show the goal type we're trying to solve
  logInfo m!"[auto] goal type: {← ppExpr goalTy}"

  let lctx ← getLCtx
  let hyps := lctx.decls.toArray.filterMap fun
    | some d => if d.isImplementationDetail then none else some d.toExpr
    | none   => none
  -- DEBUG: Show all collected hypotheses
  logInfo m!"[auto] collected {hyps.size} hypotheses"
  for h in hyps do
    logInfo m!"hyp: {← ppExpr h} : {← inferType h}"

  let result ← autoSearch goalTy hyps 10
  -- DEBUG: Show what term we're closing the goal with
  logInfo m!"[auto] closing goal with: {← ppExpr result}"
  goal.assign result


-- ============================================================
-- Examples
-- ============================================================
set_option trace.Elab true in
def ex1 (a : A) (b : B) : A ∧ B := by auto
def ex2 (ab : A ∧ B) : B ∧ A := by auto
def ex3 (ab : A ∧ B) : A ∧ B := by auto
def ex4 (a : A) (b : B) : A ∧ (B ∧ A) := by auto
-- def ex5 (a : A) : A ∧ B := by auto -- auto: cannot construct A ∧ B

example (ab : A ∧ B) : B ∧ A := by exact ⟨ab.right, ab.left⟩
