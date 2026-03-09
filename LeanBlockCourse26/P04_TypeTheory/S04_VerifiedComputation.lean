/-
# S04: Verified Computation and Trust

The payoff: verified computation with Subtype, axiom tracing with
`#print axioms`, and the trust model.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic

open BigOperators Bool Nat



/-!
## (Inductive) type classes and their instances

### Inhabited
-/

#check Inhabited
#check @instInhabitedNat

#eval @Inhabited.default Nat _


-- This works and shows `0`because `Nat` is shown to be an instance of type class `Inhabited` ...
#eval @Inhabited.default Nat _

-- ... by providing its zero constructor as thge default element
instance : Inhabited Nat where
  default := Nat.zero

/-!
### Nonempty
-/

#check Nonempty

-- This works ...
#check Nonempty.intro Nat

-- ... but `eval` complains about `proofs are not computationally relevant` ...
-- #eval Nonempty.intro Nat
#check Nonempty.intro Nat

-- A `Prop` is nonempty if it has a term `p` ...
variable (P : Prop) (p : P)
instance : Nonempty P := Nonempty.intro p

-- ... but `eval` again does not work because `Prop` is stateless
-- #eval Nonempty.intro Nat
#check Nonempty.intro P

/-!
### Decidable and DecidablePred
-/

#check Decidable
#check DecidablePred

#check @instDecidableAnd

def p_nat_even := (fun n : Nat => n  % 2 = 0) 

noncomputable instance pNatEvenDecidableClassical : DecidablePred p_nat_even :=
    Classical.decPred p_nat_even


-- instance pNatEvenDecidableConstructive : DecidablePred p_nat_even :=
  -- intro n
  -- | isFalse => sorry
  -- | isTrue => sorry

/-!
## Verified computation

The pattern:
1. Write an algorithm with a plain type signature.
2. Prove a property as a separate theorem.
3. Bundle into Subtype — the return type carries the guarantee.
-/

section VerifiedFilter

variable {α : Type}

-- Step 1: algorithm. `[DecidablePred p]` lets `if` branch on a Prop.

/-
`List` is defined inductively on lean with constructors for an empty
list (`nil`) and an dependent constructor `cons` that appends and element
`(head : α)` to a given existing list `(tail : List α)`.

inductive List (α : Type u) where
  | nil : List α 
  | cons (head : α) (tail : List α) : List α

We can use `[...]` notation with `[] = List.nil`
-/

def propFilter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => [] 
  | head :: tail =>
      let filtered_tail := propFilter p tail
      if (p head) then
        head :: filtered_tail
      else
        filtered_tail

-- We can actually evaluate this computationally ...
#eval propFilter (fun n : Nat => n  % 2 = 0)  [1, 2, 3, 4, 5, 6]


-- ... but only if we know `DecidablePred` holds and is computable

noncomputable instance : DecidablePred p_nat_even := Classical.decPred p_nat_even

-- Complains about `Classical.choice` axiom being used
-- #eval propFilter p_nat_even [1, 2, 3, 4, 5, 6]

-- Exercise: prove that `propFilter` is sound
-- Step 2a: prove soundness — everything in the output satisfies p.
theorem propFilter_sound (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  intro x hx
  induction xs with
  | nil =>
     unfold propFilter at hx  -- optional
     exfalso
     exact (List.mem_nil_iff x).mp hx
  | cons y ys ih => 
     unfold propFilter at hx -- not optional
     split at hx
     case isTrue h =>
      cases hx with
       | head => exact h
       | tail _ hmem => exact ih hmem
     case isFalse h =>
      exact ih hx

theorem propFilter_sound' (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  intro x hx
  induction xs
  · contradiction
  next y ys ih =>
    by_cases h : p y
    · rw [show propFilter p (y :: ys) = y :: propFilter p ys from if_pos h] at hx
      obtain _ | ⟨_, hmem⟩ := hx
      · exact h
      · exact ih hmem
    · rw [show propFilter p (y :: ys) = propFilter p ys from if_neg h] at hx
      exact ih hx

#print axioms propFilter_sound'

-- Step 2b: prove completeness — everything in `xs` but not in the output does not satisfy `p`.
theorem propFilter_complete (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x, x ∈ xs ∧ x ∉ propFilter p xs → ¬ p x := by
  intro x ⟨x_in_xs, hx⟩ px
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
      unfold propFilter at hx
      split at hx
      case isTrue h =>
        cases x_in_xs with
        | head => exact hx List.mem_cons_self
        | tail _ hmem => exact ih hmem (fun h' => hx (.tail _ h'))
      case isFalse h =>
        cases x_in_xs with
        | head => exact h px
        | tail _ hmem => exact ih hmem hx

theorem propFilter_complete' (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x, x ∈ xs ∧ x ∉ propFilter p xs → ¬ p x := by
  intro x ⟨x_in_xs, hx⟩ px
  induction xs
  · contradiction
  next y ys ih =>
    by_cases h : p y
    · rw [show propFilter p (y :: ys) = y :: propFilter p ys from if_pos h] at hx
      obtain _ | ⟨_, hmem⟩ := x_in_xs
      · exact hx List.mem_cons_self
      · exact ih hmem (fun h' => hx (List.mem_cons_of_mem _ h'))
    · rw [show propFilter p (y :: ys) = propFilter p ys from if_neg h] at hx
      obtain _ | ⟨_, hmem⟩ := x_in_xs
      · exact h px
      · exact ih hmem hx

-- Step 3: bundle algorithm + proof into Subtype.
-- Note: we cannot state `∀ x, (x ∈ ys ∧ p x) ∨ (x ∉ ys ∧ ¬ p x)` because
-- for `x ∉ xs` we have `x ∉ ys` but cannot conclude `¬ p x`.
def verifiedFilter (p : α → Prop) [DecidablePred p] (xs : List α) :
    { ys : List α // (∀ x ∈ ys, p x) ∧ (∀ x, x ∈ xs ∧ x ∉ ys → ¬ p x) } :=
  ⟨propFilter p xs, propFilter_sound p xs, propFilter_complete p xs⟩

#eval (verifiedFilter (fun n : Nat => n % 2 = 0) [1, 2, 3, 4, 5, 6]).val

end VerifiedFilter


-- We can turn the proof of the infinitude of primes from P01S04 into a simple verified algorithm
def exists_infinite_primes_algorithm (n : ℕ) :
    { p : ℕ // n ≤ p ∧ Nat.Prime p } :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

-- This works ...
#eval exists_infinite_primes_algorithm 4 

-- ... even though the theorem used axioms ...
#print axioms exists_infinite_primes_algorithm

-- ... in particular in the definition of  `p` through `minFac` ...
#print axioms minFac        -- [propext, Classical.choice, Quot.sound]

/-
... but looking at the code we see that minFac only uses the axioms for
the proof of `decreasing_by` and the actual core algorithm `minFacAux``
is purely constructive.

```
def minFacAux (n : ℕ) : ℕ → ℕ
  | k =>
    if n < k * k then n
    else
      if k ∣ n then k
      else
        minFacAux n (k + 2)
termination_by k => sqrt n + 2 - k
decreasing_by simp_wf; apply minFac_lemma n k; assumption

def minFac (n : ℕ) : ℕ :=
  if 2 ∣ n then 2 else minFacAux n 3
```

But note that unlike our subtype example, `minFac` does not bundle
the (to us) relevant property that the output is prime. Instead 
we had to invoke `minFac_prime`.
-/

-- Note that these using axioms is not a problem for us:
#print axioms minFac_prime  -- [propext, Classical.choice, Quot.sound]
#print axioms minFac_dvd    -- [propext, Classical.choice, Quot.sound]
#print axioms minFac_pos    -- [propext, Classical.choice, Quot.sound]

#print axioms dvd_factorial         -- propext
#print axioms Nat.dvd_add_iff_right -- propext


/-
Any axiom is just a `theorem` without a proof or a `def` without an
implementation. It satisfies the typechecker, but does not produce
computable code.

```
axiom myChoice (P : Prop) : P ∨ ¬ P
```

But we need to  be careful with this, because as soon as we define
a contradiction, everything collapses:

```
axiom myFallacy : False

theorem weHaveAProblem : 2 = 3 := by
  exfalso
  exact myFallacy 
```
-/

#check False


