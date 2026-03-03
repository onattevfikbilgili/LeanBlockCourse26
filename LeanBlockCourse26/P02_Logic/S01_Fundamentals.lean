/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite

/-
# Fundamentals of Lean Proofs
=====================

This module introduces the most basic building blocks for constructing proofs in Lean:
- Proving equalities with `rfl`
- Using hypotheses with `assumption`
- Precise matching with `exact`
- Basic implications (`→`) and the `intro` tactic
- Rewriting with `rw`

Note: Tactic usage counts in this course are approximate, measured against
Mathlib in February 2025.


## Proofs by reflexivity - the `rfl` tactic

The `rfl` tactic proves goals that are true by definition
and is (explicitly) used around 4000 times in mathlib and many
times more implicitly through `rw`, `exact`, `simp`, ...
-/

-- Simple equality: proves that 42 equals itself
theorem simple_int_eq : 42 = 42 := by
  rfl

#check simple_int_eq

theorem simple_int_eq' : (42 = 42 : Prop) := by
  rfl

-- Works with variables: proves that any proposition equals itself
example (P : Prop) : P = P := by
  rfl

-- also works in term mode
example (P : Prop) : P = P := rfl

-- Works with logical equivalence: proves that any proposition is equivalent to itself
example (P : Prop) : P ↔ P := by
  rfl

-- does *not* work in term mode!
-- example (P : Prop) : P ↔ P := rfl

-- Works with definitional equality: proves that 2 + 2 is 4 *by definition*
-- Why is this true? Because 4 = 0.succ.succ.succ.succ, 2 = 0.succ.succ
-- and a + b.succ = (a + b).succ, so unraveling everything, both sides reduce to
-- 0.succ.succ.succ.succ, which is four!
--
-- BUT: this only works because we are cleverly modelling Nat through DTT
-- as an inductive type, not explicitly through Peano axioms! -> P05
example : 2 + 2 = 4 := by
  rfl

-- Even works with type-level equality.
-- We will explore types in more detail later.
example (α : Type) : α = α := by
  rfl

-- Note that this does *not* work since ↔ only works
-- with Prop not arbitrary Type
-- example (α : Type) : α ↔ α := by
--   rfl


/-
## Using hypotheses - the `assumption` tactic

The `assumption` tactic looks through the available hypotheses and tries to find one
that exactly matches the goal. This is useful when you already have exactly what you
need to prove in your context. This tactic is essentially unused in mathlib.
We will learn in a bit why.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
-- Note that the linter flags `h₁` as an unused assumption
example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) : 1 < n := by
  assumption

-- This also works because 1 < n is the same as n > 1 by reflexivity
example (n : ℕ) (h₁ : 10 > n) (h₂ : n > 1) : 1 < n := by
  assumption

example (n : ℕ) : (1 < n : Prop) = (n > 1 : Prop) := rfl

-- Given proposition `P` and its proof, prove `P`
--
-- `(P : Prop)` is just a proposition, it can be true, false, unprovable
-- a trivial lemma, a known theorem, an open conjecture, or complete garbage
-- 
-- `(p : P)` is an instanciation of `P` and therefore a proof to lean.
-- Notably we are not working with booleans or even ⊤ here!
example (P : Prop) (p : P) : P := by
  assumption

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
-- `(P Q : Prop)` is just a short grouping of `(P : Prop) (Q : Prop)`
-- linting again complains about `(q : Q)` being unused, but 
-- `(Q : Prop)` is fine because `(q : Q)` uses it (until you remove it)
example (P Q : Prop) (p : P) (q : Q) : P := by
  assumption

/-
## Precise matching - the `exact` tactic

The `exact` tactic allows us to provide a term that precisely matches the goal type.
Unlike assumption, which searches for matches, exact requires us to specify exactly
which term we want to use, but otherwise has the same effect. The `rfl` tactic in fact
was just syntax sugar for `exact rfl`. The tactic `exact?` looks for any term that can be
used to close the goal. This tactic is used over 40,000 times in mathlib.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
-- `_` makes the linter not complain, refers to intentionally unnamed variable
-- same as in many other languages
example (n : ℕ) (_ : 10 > n) (h₂ : 1 < n) : 1 < n := by  
  exact h₂ -- `exact` is leans `return` (in tactic mode, in term mode its implicit)

-- Given proposition `P` and its proof, prove `P`
example (P : Prop) (p : P) : P := by
  exact p

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
example (P Q : Prop) (p : P) (_ : Q) : P := by
  exact p


/-
## Exercise Block 1
-/

-- Exercise 1.1
-- State and prove that `3 + 2 = 5`


-- Exercise 1.2
-- State and prove that given any arbitrary proposition `M`
-- and a proof of it, we know that the proposition holds
