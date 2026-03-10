/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases
import LeanBlockCourse26.P05_NaturalNumbers.S01_Definition
import ProofGolf

/-
# Addition
=====================

Addition is an operator `+` on two natural numbers that produces a third
natural number and is defined inductively through two axioms:

(i)  n + 0 = n
(ii) m + S(n) = S(m + n)
-/


namespace MyNat


/-
## Defining Addition: Attempt #1

We can define addition axiomatically.
-/

-- We need to define the operator axiomatically since its actual implementation is in the axioms ...
noncomputable axiom axiom_add (m n : MyNat) : MyNat

-- ... that `axiom_add n 0 = n` ...
axiom axiom_add_zero (n : MyNat) : axiom_add n 0 = n

-- ... and `axiom_add m n.succ = (axiom_add m n).succ`
axiom axiom_add_succ (m n : MyNat) : axiom_add m n.succ = (axiom_add m n).succ

-- Note that axiomatically defined types of course still `#check` out ...
#check axiom_add
#check axiom_add 0
#check axiom_add 0 0

-- but we cannot actually `#eval` this addition, so we mark it `noncomputable`
-- #eval axiom_add 0 0

/-
## Exercise Block B01
-/

-- Exercise 1.1 – Prove that `x + 2 = x + 2`
example (x : MyNat) : axiom_add x 2 = axiom_add x 2 := rfl

-- Exercise 1.2 – Prove that `a + (b + 0) + (c + 0) = a + b + c`
example (a b c : MyNat) :
    axiom_add a (axiom_add (axiom_add b 0) (axiom_add c 0)) = axiom_add a (axiom_add b c) := by
  repeat rw [axiom_add_zero] -- need to explicitly invoke the axiom `axiom_add_zero`

-- Exercise 1.3 – Prove that `succ n = n + 1`
theorem succ_eq_add_one' (n : MyNat) : succ n = axiom_add n 1 := by
  rw [one_eq_succ_zero, axiom_add_succ, axiom_add_zero]

-- Exercise 1.4 – Prove that `2 + 2 = 4?`
example : axiom_add 2 2 = 4 := by
  obtain h : 2 = succ (succ 0) := by rfl
  rw [h, axiom_add_succ, axiom_add_succ, axiom_add_zero]
  rfl


/-
**Remark:** So far we have proved very elementary statements that can and usually should
be derived from first principles. Now we are starting to build up a framework and
we should develop the habit of actually reusing what we previously used rather than
brute forcing each statement back to the core definition of `MyNat` and `add`.
-/

example : axiom_add 2 2 = 4 := by
  nth_rw 2 [two_eq_succ_one]
  rw [axiom_add_succ, one_eq_succ_zero, axiom_add_succ, axiom_add_zero]
  rfl

/-
But shouldn't all of these be *definitionally* equal? Something is off ...

## Defining Addition: Attempt #2

We can define addition through the inductive definition of `MyNat`
-/

def add (m n : MyNat) : MyNat :=
  match n with
  | zero => m                 -- same as `axiom add_zero'`
  | succ k => (add m k).succ  -- same as `axiom add_succ'`

#eval add 2 3

/-
## Using the `+` notation

To write `m + n` instead of `add m n`, we can use the `Add` typeclass
provided by Lean, which also means we inherit the `+` notation.
-/

instance instAdd : Add MyNat where add := add

example : 2 + 2 = add 2 2 := rfl

theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := rfl

/-
**Comment:** All B01 exercises now just become `rfl` true. We can still prove and
then use lemmas `add_zero` and `add_succ` (which Lean actually does).
-/

-- Compare `Nat.add_zero` ...
theorem add_zero (a : MyNat) : a + 0 = a := rfl

-- ... `Nat.add_succ` defined for `Nat` type in Lean
theorem add_succ (a b : MyNat) : a + b.succ = (a + b).succ := rfl

/-
## Proof by induction on an inductive type

We can prove that `0 + n = n` by induction on `n`.
-/

theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => exact add_zero 0       -- or just `rfl` so `add_zero` is optional here ...
  | succ n ih => rw [add_succ, ih] -- ... but the `rw` tactic actually needs `add_succ` here!


/-
## Exercise Block B02

**Remark 1:** `0` without any additional context will be interpreted as `Nat.zero`.
If there is additional `MyNat` context around it, type inference will be able
to understand that this should actually instead be `MyNat.zero`. If you should
run into issues where this does *not* work, you can explicitly specify the
type as usual through `(0 : MyNat)`.

**Remark 2:** If you encounter `MyNat.zero` but want to apply a theorem that
uses `(0 : MyNat)` then the type checker can sometimes not consolidate these
two. For this we can simply define a little `zero_zero` helper with which we
can rewrite.
-/

theorem zero_zero : 0 = MyNat.zero := rfl

-- Exercise 2.1
-- By induction on `m`. For the base case, both sides simplify to `succ n`.
-- For the inductive step, `succ n + S(m) = S(succ n + m)` by definition of
-- addition, which equals `S(succ(n + m))` by the inductive hypothesis, and
-- this is `succ(n + S(m))` again by definition of addition.
theorem succ_add (n m : MyNat) : succ n + m = succ (n + m) := by
  induction m with
  | zero =>
    rw [← zero_zero]
    rw [add_zero, add_zero]
  | succ =>
    expose_names
    rw [add_succ, add_succ, a_ih]

-- Exercise 2.2 – Commutativity
-- By induction on `m`. The base case `n + 0 = 0 + n` holds by `add_zero`
-- and `zero_add`. For the inductive step, `n + S(m) = S(n + m)` by definition,
-- which equals `S(m + n)` by the inductive hypothesis, and this is
-- `S(m) + n` by `succ_add`.
theorem add_comm (n m : MyNat) : n + m = m + n := by
  induction m with
  | zero =>
    rw [← zero_zero, add_zero, zero_add]
  | succ =>
    expose_names
    rw [add_succ, succ_add, a_ih]

-- Exercise 2.3 – Associativity
-- By induction on `k`. The base case is immediate. For the inductive step,
-- `(n + m) + S(k) = S((n + m) + k)` by definition, which equals
-- `S(n + (m + k))` by the inductive hypothesis, and this is
-- `n + S(m + k) = n + (m + S(k))` by definition.
theorem add_assoc (n m k : MyNat) : (n + m) + k = n + (m + k) := by
  induction k with
  | zero => rfl
  | succ =>
    expose_names
    rw [add_succ, a_ih, ← add_succ, add_succ m]

-- Exercise 2.4 – Right commutativity
-- By associativity, `(n + m) + k = n + (m + k)`. By commutativity of the
-- inner sum, `n + (m + k) = n + (k + m)`. By associativity again,
-- `n + (k + m) = (n + k) + m`.
theorem add_right_comm (n m k : MyNat) : n + m + k = n + k + m := by
  rw [add_assoc, add_comm m k, add_assoc]

-- Exercise 2.5 (Master)
-- Follows directly from the injectivity of the successor (seventh Peano axiom).
example (n m : MyNat) (h : succ (n + 37) = succ (m + 42)) : n + 37 = m + 42 := by
  exact MyNat.noConfusion h id

-- Exercise 2.6 (Master)
example (n m : MyNat) (h1 : n = 37) (h2 : n = 37 → m = 42) : m = 42 := by
  exact h2 h1

-- Exercise 2.7 (Master)
example (n m : MyNat) (h1 : n = m) (h2 : n ≠ m) : False := by
  exact h2 h1

end MyNat
