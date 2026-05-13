/-
Lean Forecast: v4.30.0
13-05-2026, Faculty of Mathematics of UCM
Juanjo Madrigal
-/

-- # Some interesting links

-- https://lean-lang.org/doc/reference/latest/
-- https://github.com/leanprover/reference-manual
-- https://github.com/leanprover/reference-manual/pull/836
-- https://pr-836--lean-reference-manual-review.netlify.app/reference/releases/v4.30.0/#release-v4___30___0
-- https://github.com/bigmac0/reference-manual/blob/09a945e76b20068d05a761e0fbf0146f6a357886/highlight/release-highlights-v2.md



-- # cbv
-- https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-cbv

def fact : Nat → Nat
| 0 => 1
| n+1 => (n+1) * fact n

example : fact 5 = 120 := by rfl
-- example : fact 5 > 0   := by rfl

example : fact 5 = 120 := by cbv
example : fact 5 > 0   := by cbv

-- try to set `cbv.maxSteps 20`
set_option cbv.maxSteps 200 in
example : fact 5 > 0 := by cbv

-- similar in some aspects to `native_decide`
example : fact 5 > 0 := by native_decide

def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n

-- cbv may not finish the prrof
example : 1 ∈ countdown 2 := by
  cbv
  exact .tail _ (.head _)



-- # sym => / grind =>

-- some links related to e-graphs, grind and interactive mode

-- https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind-tactic
-- https://lean-lang.org/doc/tutorials/latest/grind-index-map/
-- egg (rust) : https://www.youtube.com/watch?v=LKELTEOFY-s
-- https://cfaed.tu-dresden.de/files/Images/people/chair-cc/theses/2407_Rossel_MA.pdf
-- https://github.com/leanprover/lean4/blob/master/src/Init/Grind/Interactive.lean

example (x y : Nat) : x ≥ y + 1 → x > 0 := by
  -- grind
  grind =>
    show_asserted
    show_true
    -- show_false
    show_eqcs
    -- show_cases
    show_state
    show_local_thms
    show_term
    show_goals
    finish

example (p : Nat → Prop) (x y z w : Int) :
  (x = 1 ∨ x = 2) →
  (w = 1 ∨ w = 4) →
  (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
  (z = 1 ∨ z = 0) → x + y ≤ 6
:= by
  grind
  -- grind =>
  --   show_asserted
  --   cases?
  --   cases #6c8c
  --   · cases #4228
  --   · cases #4228 <;> lia
  -- sym =>
  --   intro a b c d
  --   show_asserted
  --   cases?
  --   cases #6c
  --   · cases #4228
  --   · cases #4228 <;> lia

-- change `grind` to `grind?`
example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind

-- bonus! change `by` to `by?`
example : 3 = 3 := by simp



-- # mvcgen

-- https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/
-- https://lean-lang.org/doc/tutorials/latest/mvcgen/

/-

from 'do' notation to terms

def A : m a := do
  instruction1
  instruction2
  instruction3
  instruction4
  ...

let x = 3; y = x + 1; z = y + 1 in x + y + z
(\x -> (\y -> (\z -> x + y + z) $ y + 1) $ x + 1) $ 3

mvcgen : translating invariants in imperative programs to proofs in unfolded terms

-/



-- # bonus : reservoir

-- https://reservoir.lean-lang.org/
