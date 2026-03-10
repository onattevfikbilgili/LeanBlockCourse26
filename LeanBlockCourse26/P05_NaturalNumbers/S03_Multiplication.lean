/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.ByContra
import LeanBlockCourse26.P05_NaturalNumbers.S02_Addition
import ProofGolf

/-
# Multiplication
=====================
-/

namespace MyNat

/-
## Exercise Block B01

Define multiplication inductively, register the `*` notation, and derive
the two definitional lemmas.
-/

-- Exercise 1.1 – Define multiplication `mul` inductively
def mul (n m : MyNat) : MyNat :=
  match m with
  | MyNat.zero => 0
  | MyNat.succ k => (mul n k) + n

-- Exercise 1.2 – Register the `*` notation via the `Mul` typeclass
instance instMul : Mul MyNat where mul := mul

-- Exercise 1.3 – Show that `n * 0 = 0`
-- Both sides reduce to `0` by the definition of `mul`.
theorem mul_zero (n : MyNat) : n * 0 = 0 := by rfl

-- Exercise 1.4 – Show that `n * succ m = n * m + n`
-- Both sides reduce to `(mul n m) + n` by the definition of `mul`.
theorem mul_succ (n m : MyNat) : n * succ m = n * m + n := by rfl


/-
## Exercise Block B02
-/

-- Exercise 2.1 – Multiplicative identity on the right
-- Unfold `1` as `succ 0`, then apply `mul_succ` and `mul_zero`, and simplify
-- with `zero_add`.
theorem mul_one (n : MyNat) : n * 1 = n := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

-- Exercise 2.2 – Multiplication by zero on the left
-- By induction on `n`. The base case is immediate. For the inductive step,
-- `0 * S(n) = 0 * n + 0` by `mul_succ`, which equals `0` by the inductive
-- hypothesis and `add_zero`.
theorem zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => trivial
  | succ => trivial

-- Exercise 2.3 – Successor distributes over multiplication on the left
-- By induction on `m`. The base case is immediate. For the inductive step,
-- `S(n) * S(m) = S(n) * m + S(n)` by `mul_succ`, which by the inductive
-- hypothesis equals `(n * m + m) + S(n)`. Rewrite using `mul_succ` on the
-- right-hand side and rearrange with `add_assoc`, `add_succ`, and `add_comm`.
theorem succ_mul (n m : MyNat) : (succ n) * m = n * m + m := by
  induction m with
  | zero => rw [← zero_zero, add_zero, mul_zero, mul_zero]
  | succ =>
    expose_names
    rw [add_succ, mul_succ, mul_succ, add_succ,
        add_assoc, add_comm n a, ← add_assoc, a_ih]

-- Exercise 2.4 – Commutativity
-- By induction on `m`. The base case uses `zero_mul`. The inductive step
-- follows from `succ_mul` and the inductive hypothesis.
theorem mul_comm (n m : MyNat) : n * m = m * n := by
  induction m with
  | zero => rw [← zero_zero, mul_zero, zero_mul]
  | succ m h => rw [mul_succ, succ_mul, h]

-- Exercise 2.5 – Multiplicative identity on the left
-- Follows directly from `mul_comm` and `mul_one`.
theorem one_mul (m : MyNat) : 1 * m = m := by
  rw [mul_comm, mul_one]

-- Exercise 2.6 – Double
-- Unfold `2` as `succ 1` and apply `succ_mul` and `one_mul`.
theorem two_mul (m : MyNat) : 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]

-- Exercise 2.7 – Right distributivity
-- By induction on `m`. The base case simplifies all products to zero.
-- The inductive step rewrites with `succ_add` and `mul_succ` on both sides,
-- then applies the inductive hypothesis and rearranges with `add_assoc`
-- and `add_comm`.
theorem mul_add (n m k : MyNat) : n * (m + k) = n * m + n * k := by
  induction m with
  | zero => rw [← zero_zero, zero_add, mul_zero, zero_add]
  | succ => expose_names; rw [succ_add, mul_succ, mul_succ, a_ih, add_right_comm]

-- Exercise 2.8 – Left distributivity
-- Follows from `mul_comm` and `mul_add`.
theorem add_mul (n m k : MyNat) : (n + m) * k = n * k + m * k := by
  rw [mul_comm, mul_add, mul_comm n k, mul_comm k m]

-- Exercise 2.9 – Associativity
-- By induction on `m`. The base case simplifies via `mul_zero` and `zero_mul`.
-- The inductive step uses `mul_succ`, `succ_mul`, `add_mul`, and the
-- inductive hypothesis.
theorem mul_assoc (n m k : MyNat) : (n * m) * k = n * (m * k) := by
  induction m with
  | zero => rw [← zero_zero]; repeat rw [zero_mul, mul_zero]; rw [zero_mul]
  | succ => expose_names; rw [succ_mul, mul_succ, add_mul, mul_add, a_ih]

end MyNat
