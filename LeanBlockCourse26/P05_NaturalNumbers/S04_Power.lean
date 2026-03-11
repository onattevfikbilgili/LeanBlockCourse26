/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse26.P05_NaturalNumbers.S03_Multiplication
import ProofGolf

/-
# Exponentiation
=====================
-/

namespace MyNat

-- Define exponentiation recursively
def pow (n m : MyNat) : MyNat :=
  match m with
  | zero => 1
  | succ k => pow n k * n

-- Register the `^` notation via the `Pow` typeclass
instance instPow : Pow MyNat MyNat where pow := pow

-- The two definitional lemmas for exponentiation
theorem pow_zero (n : MyNat) : n ^ (0 : MyNat) = 1 := rfl

theorem pow_succ (n m : MyNat) : n ^ (succ m) = n ^ m * n := rfl


/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem zero_pow_zero : (0 : MyNat) ^ (0 : MyNat) = 1 := rfl

-- Exercise 1.2
-- Rewrite with `pow_succ` to get `0 ^ m * 0`, then apply `mul_zero`.
theorem zero_pow_succ (m : MyNat) : (0 : MyNat) ^ (succ m) = 0 := by
  rw [pow_succ, mul_zero]

-- Exercise 1.3
-- Unfold `1` as `succ 0`, rewrite with `pow_succ` and `pow_zero`, then
-- apply `one_mul`.
theorem pow_one (n : MyNat) : n ^ (1 : MyNat) = n := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

-- Exercise 1.4
-- By induction on `n`. The base case follows from `pow_zero`. For the
-- inductive step, rewrite with `pow_succ` and apply the inductive
-- hypothesis and `mul_one`.
theorem one_pow (n : MyNat) : (1 : MyNat) ^ n = 1 := by
  induction n with
  | zero => rw [← zero_eq_zero, pow_zero]
  | succ m ih => rw [pow_succ, ih, mul_one]

-- Exercise 1.5
-- Unfold `2` as `succ 1`, rewrite with `pow_succ` and `pow_one`.
theorem pow_two (n : MyNat) : n ^ (2 : MyNat) = n * n := by
  rw [two_eq_succ_one, pow_succ, pow_one]

-- Exercise 1.6
-- By induction on `k`. The base case follows from `add_zero`, `pow_zero`,
-- and `mul_one`. For the inductive step, rewrite with `add_succ` and
-- `pow_succ` on both sides, apply the inductive hypothesis, and
-- rearrange with `mul_assoc`.
theorem pow_add (n m k : MyNat) : n ^ (m + k) = n ^ m * n ^ k := by
  induction k with
  | zero => rw [← zero_eq_zero, add_zero, pow_zero, mul_one]
  | succ m ih => rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

-- Exercise 1.7
-- By induction on `k`. The base case follows from `pow_zero` and `mul_one`.
-- For the inductive step, rewrite all three `pow_succ` terms, apply the
-- inductive hypothesis, and rearrange with `mul_assoc` and `mul_comm`.
theorem mul_pow (n m k : MyNat) : (n * m) ^ k = n ^ k * m ^ k := by
  induction k with
  | zero => rw [← zero_eq_zero, pow_zero, pow_zero, pow_zero, mul_one]
  | succ k' ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    repeat rw [mul_assoc]
    rw [mul_comm n (_ * m), mul_assoc, mul_comm m n]

-- Exercise 1.8
-- By induction on `k`. The base case follows from `mul_zero` and `pow_zero`.
-- For the inductive step, rewrite with `pow_succ`, apply the inductive
-- hypothesis, then use `mul_succ` and `pow_add`.
theorem pow_pow (n m k : MyNat) : (n ^ m) ^ k = n ^ (m * k) := by
  induction k with
  | zero => rw [← zero_eq_zero, mul_zero, pow_zero, pow_zero]
  | succ k' ih => rw [pow_succ, ih, mul_succ, pow_add]

-- Exercise 1.9 (Master)
-- Expand all squares with `pow_two`, distribute with `mul_add` and `add_mul`,
-- rewrite `2 * n * m` with `two_mul` and `add_mul`, and rearrange with
-- `add_assoc`, `add_right_comm`, and `mul_comm`.
theorem add_sq (n m : MyNat) :
    (n + m) ^ (2 : MyNat) = n ^ (2 : MyNat) + m ^ (2 : MyNat) + 2 * n * m := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm m n]
  rw [← add_assoc, ← add_assoc]

/-
## Bonus (Master): State (and prove) Fermat's Last Theorem

Fermat's Last Theorem states that if `x, y, z > 0` and
`m ≥ 3` then `x^m + y^m ≠ z^m`. Since we have not yet
introduced inequalities, you will need to restate this
using several inequalities.

The shortest solution known to humans would translate into
many millions of lines of Lean code. Kevin Buzzard is working
on translating the proof by Wiles and Taylor into Lean, although
this task will take many years.
-/

theorem fermats_last_theorem (x y z m : MyNat)
    (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x^m + y^m ≠ z^m := by
  sorry

/-
# Tactic Addendum: `simp`
=====================

Many of the proofs above were tedious — long `rw` chains rearranging terms
via associativity and commutativity, with no deep mathematical insight.
The following rearrangement of 8 variables illustrates the problem. `#golf`
your solution and try to make the *term mode* as compact as possible.
-/

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry






end MyNat
