/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NthRewrite
import LeanBlockCourse26.P03_SetTheory.S01_SubsetsComplements

variable {α : Type*}

/-
# Sets: Intersections and Unions
=====================

## Intersection Basics

The intersection of two sets `S` and `T`, denoted `S ∩ T`, is defined as the
set of elements `x` for which `x ∈ S ∧ x ∈ T`.
-/

example (S T : Set α) : S ∩ T = {x | x ∈ S ∧ x ∈ T} := rfl

lemma mem_inter_iff (x : α) (S T : Set α) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by
  rfl

#check Set.mem_inter_iff

lemma mem_of_mem_inter_right {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := by
  rw [mem_inter_iff] at h -- optional because we are just rewriting with equal definition
  exact h.2

example {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := h.2

lemma inter_subset_left (S T : Set α) : S ∩ T ⊆ S := by
  rw [subset_def]
  intro x h
  rw [mem_inter_iff] at h
  exact h.left

example (S T : Set α) : S ∩ T ⊆ S := 
  fun _ h => h.left

lemma mem_inter {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := by
  rw [mem_inter_iff]
  constructor
  all_goals assumption

example {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T :=  ⟨h₁, h₂⟩

/-
## Exercise Block B01
-/

-- Exercise 1.1
lemma inter_subset_swap (S T : Set α) : S ∩ T ⊆ T ∩ S := by
  sorry

-- Exercise 1.2
lemma subset_inter (R S T : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  sorry

-- Exercise 1.3
lemma inter_comm (S T : Set α) : S ∩ T = T ∩ S := by
  sorry

-- Exercise 1.4
lemma inter_assoc (R S T : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) := by
  sorry
