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
  sorry

-- Exercise 1.3
-- Unfold `1` as `succ 0`, rewrite with `pow_succ` and `pow_zero`, then
-- apply `one_mul`.
theorem pow_one (n : MyNat) : n ^ (1 : MyNat) = n := by
  sorry

-- Exercise 1.4
-- By induction on `n`. The base case follows from `pow_zero`. For the
-- inductive step, rewrite with `pow_succ` and apply the inductive
-- hypothesis and `mul_one`.
theorem one_pow (n : MyNat) : (1 : MyNat) ^ n = 1 := by
  sorry

-- Exercise 1.5
-- Unfold `2` as `succ 1`, rewrite with `pow_succ` and `pow_one`.
theorem pow_two (n : MyNat) : n ^ (2 : MyNat) = n * n := by
  sorry

-- Exercise 1.6
-- By induction on `k`. The base case follows from `add_zero`, `pow_zero`,
-- and `mul_one`. For the inductive step, rewrite with `add_succ` and
-- `pow_succ` on both sides, apply the inductive hypothesis, and
-- rearrange with `mul_assoc`.
theorem pow_add (n m k : MyNat) : n ^ (m + k) = n ^ m * n ^ k := by
  sorry

-- Exercise 1.7
-- By induction on `k`. The base case follows from `pow_zero` and `mul_one`.
-- For the inductive step, rewrite all three `pow_succ` terms, apply the
-- inductive hypothesis, and rearrange with `mul_assoc` and `mul_comm`.
theorem mul_pow (n m k : MyNat) : (n * m) ^ k = n ^ k * m ^ k := by
  sorry

-- Exercise 1.8
-- By induction on `k`. The base case follows from `mul_zero` and `pow_zero`.
-- For the inductive step, rewrite with `pow_succ`, apply the inductive
-- hypothesis, then use `mul_succ` and `pow_add`.
theorem pow_pow (n m k : MyNat) : (n ^ m) ^ k = n ^ (m * k) := by
  sorry

-- Exercise 1.9 (Master)
-- Expand all squares with `pow_two`, distribute with `mul_add` and `add_mul`,
-- rewrite `2 * n * m` with `two_mul` and `add_mul`, and rearrange with
-- `add_assoc`, `add_right_comm`, and `mul_comm`.
theorem add_sq (n m : MyNat) :
    (n + m) ^ (2 : MyNat) = n ^ (2 : MyNat) + m ^ (2 : MyNat) + 2 * n * m := by
  sorry

-- Exercise 1.10 (Master) – State (and prove?) Fermat's Last Theorem

end MyNat
