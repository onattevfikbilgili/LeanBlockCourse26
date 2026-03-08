/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set
import ProofGolf

/-
Let us review something that we already briefly used in the last exercise block:

So far we have always seen variables as explicit arguments to statements, usually
looking something like `(P : Prop)`. Here we are doing three things differently:

1. We are using `variable` to declare a variable that is used in any statement that follows.
2. We are using curly brackets `{}` to denote an implicit argument.
3. We are using `Type*` to denote an unspecified type (more on this later).
-/

-- So far we have specified all arguments explicitly ...
theorem explicit_argument (P : Prop) (p : P) : P := p

-- ... but in this case specifying `p : P` already implies `P : Prop`.
theorem implicit_argument {P : Prop} (p : P) : P := p

/--
Both of these state the same, but specifying `{P : Prop}` reduces the number of arguments
you need to specify when invoking it.
-/
example (R S : Prop) (r : R) (s : S) : R ∧ S := by
  constructor
  · exact explicit_argument R r
  · exact implicit_argument s

-- Note that you can always override any implicit arguments with `@`
example (R S : Prop) (r : R) (s : S) : R ∧ S := by
  constructor
  · exact @implicit_argument R r  -- now we *need* to specify the `R` ...
  · exact @implicit_argument _ s  -- ... though you can refuse to elaborate through `_`

/-
Using `variable` allows us to have cleaner theorem statements whenever arguments are
shared. Other languages also have global variables but usually these are very much
discouraged. In Lean however they are very important and used throughout mathlib:
if you are working on a file that collects statements about finite simple graphs,
you do not want to specify for each that it requires to be given a
simple graph `(G : SimpleGraph V)` with implicit vertex type `{V : Type*}` which
is also finite `[FinType V]` (the square brackets we will elaborate on later).

We can scope these shared arguments through a `namespace`.
-/

namespace sharedArgumentExample

variable {P : Prop} (R S : Prop)

theorem implicit_argument' (p : P) : P := p

example (r : R) (s : S) : R ∧ S := by
  constructor
  · exact implicit_argument' r
  · exact implicit_argument' s

example (r : R) (s : S) : R ∧ S := by
  constructor
  · exact @implicit_argument' R r
  · exact @implicit_argument' _ s

end sharedArgumentExample

-- Because the `namespace` was closed, this no longer knows about `{P : Prop}`
example {P : Prop} (p : P) : P := p

-- To access results from a `namespace` you need to re-open it or explicitly specify it.
-- #check implicit_argument'                    -- This does *not* work ...
#check sharedArgumentExample.implicit_argument' -- ... but this does!

/-
# Sets
=====================

`S : Set α` means `S` is a set of elements of type `α`.

Note that all of the named statements in this section are already in mathlib
in the namespace `Set` which one can access by either preceding the name with `Set.`
or by opening the namespace with `open Set`.
-/

variable {α : Type*}

/-
A `Set` in mathlib is just a predicate `α → Prop`.

```
def Set (α : Type u) := α → Prop
```

Importantly it:

(i)  Needs an underlying type `α` that all set elements are instances of
(ii) Is defined through a predicate `α → Prop` with `e : α` an element of `S` iff `P e`

Notation like `{ ... }`, `∈`, `∉`, `⊆`, `∅`, ... are nice syntactic sugar on top of this.
But note that mathlib actually does *not* want you to think of sets like this:

"Although `Set` is defined as `α → Prop`, this is an implementation detail which should
not be relied on. Instead, `setOf` and membership of a set (`∈`) should be used to
convert between sets and predicates."
-/

-- `x ∈ S` is notation for `Membership x S` and `{x | P x}` for `setOf P`
theorem mem_setOf (x₀ : α) (P : α → Prop) : x₀ ∈ { x | P x} ↔ P x₀ := by rfl

-- example (x₀ : α) (P : α → Prop) : Membership x₀ (setOf P) ↔ P x₀ := rfl

-- `Nonempty S` means the type `S` is not empty, which can be proven with `use`...
example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := by
  use x

-- ... or directly through term mode
example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := ⟨x, h⟩

-- `{x}` constructs the set containing `x`
theorem mem_singleton_iff {x y : α} : x ∈ ({y} : Set α) ↔ x = y :=  by rfl

-- Both sides are definitionally equal (`x ∈ ({y} : Set α)` unfolds to `x = y`),
-- so the `rfl` tactic closes this via `Iff.rfl`. Term mode `rfl` only proves
-- `a = a`, not `a ↔ a`, so it does not work directly.
example {x y : α} : x ∈ ({y} : Set α) ↔ x = y := by
  apply Iff.intro <;> intro h <;> exact h

-- The `: Set α` annotation disambiguates `{y}` from other set-like types (e.g. `Finset`);
-- `Set.singleton y` is an unambiguous alternative that does not need it
example {x y : α} : x ∈ Set.singleton y ↔ x = y := by rfl

-- `{x, y}` constructs the set containing two elements `x` and `y`
theorem mem_pair (t x y : α) : t ∈ ({x, y} : Set α) ↔ t = x ∨ t = y := by rfl

/-
`S ⊆ T` is syntax for `HasSubset` and is (essentially) defined as
`∀ x, x ∈ S → x ∈ T`. `S ⊂ T` is syntax for `HasSSubset` and is
(again essentially) defined as `S ⊆ T ∧ ¬T ⊆ S`.
-/

-- This is `Set.subset_def` in mathlib ...
theorem subset_def {S T : Set α} : (S ⊆ T) = ∀ x ∈ S, x ∈ T := rfl

-- ... but `∀ x ∈ S` makes `x : α` and `x ∈ S` explicit, which we could avoid through
theorem subset_def_impl {S T : Set α} : (S ⊆ T) = ({x : α} → x ∈ S → x ∈ T) := rfl

-- This is `Set.ssubset_def` in mathlib
theorem ssubset_def {S T : Set α} : (S ⊂ T) = (S ⊆ T ∧ ¬T ⊆ S) := rfl

/-
## Set Reflexivity

Every set is a subset of itself — `Set.Subset.rfl` in mathlib.
-/

theorem Subset.rfl (S : Set α) : S ⊆ S := by rfl

example (S : Set α) : S ⊆ S := by
  rw [subset_def] -- You can rewrite definitions, but here this is optional
  intro x h
  exact h

/-
## Set Transitivity

If `S ⊆ T` and `T ⊆ R` then `S ⊆ R` — `Set.Subset.trans` in mathlib.
-/

theorem Subset.trans {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := by
  rw [subset_def] at * -- again optional
  intro x (xs : x ∈ S)
  have xt : x ∈ T := h₁ x xs
  have xr : x ∈ R := h₂ x xt
  exact xr

example {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := by
  intro x (xs : x ∈ S)
  have xt : x ∈ T := h₁ xs -- if we do not rewrite then `x` is implicit here ...
  have xr : x ∈ R := h₂ xt -- ... and here
  exact xr

example {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := fun _ xs => h₂ (h₁ xs)

/-
## Empty Set

The empty set `∅` is the set of elements of type `α` for which `False` holds
(`Set.empty_def` in mathlib), and is a subset of every set (`Set.empty_subset`).
-/

theorem empty_def : ∅ = {x : α | False} := rfl

-- The empty set is a subset of every set — `Set.empty_subset` in mathlib
theorem empty_subset (S : Set α) : ∅ ⊆ S := by
  rw [empty_def, subset_def]
  intro x h
  exfalso
  rw [mem_setOf] at h
  exact h

example (S : Set α) : ∅ ⊆ S := by
  intro x h
  exfalso
  exact h

-- this does not use any axioms though, just `False.elim`
#golf example (S : Set α) : ∅ ⊆ S := by
  intro x h
  contradiction

/-
## Exercise Block B01

Try to find compact term mode proofs whenever possible.
-/

namespace P03S01B01

variable {S T : Set α}

-- Exercise 1.1
example {x : α} (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := by
  rw [subset_def] at h₁
  exact h₁ x h₂

example {x : α} (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := by
  rw [subset_def_impl] at h₁
  exact h₁ h₂

example {x : α} (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := by
  exact h₁ h₂

example {x : α} (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := h₁ h₂

-- Exercise 1.2
example {x : α} (R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R := by
  rw [subset_def] at *
  have xt : x ∈ T := h₁ x h₃
  have xr : x ∈ R := h₂ x xt
  exact xr

example {x : α} (R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R :=
  h₂ <| h₁ h₃

example {x : α} (R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R := by
  have h₄ : S ⊆ R := Subset.trans h₁ h₂
  rw [subset_def] at h₄
  exact h₄ x h₃

example {x : α} (R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R :=
  (Subset.trans h₁ h₂) h₃

-- Exercise 1.3
example {x : α} {R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R := by
  intro xs
  exact h₂ (h₁ xs)

example {x : α} {R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R :=
  fun xs => h₂ (h₁ xs)

-- Exercise 1.4
-- Note that `x ∉ T` is just notation for `¬(x ∈ T)` and hence `(x ∈ T) → False`
example (h : S ⊆ T) {x : α} (hx : x ∉ T) : x ∉ S := by
  intro xs
  exact hx (h xs)

example (S T : Set α) (h : S ⊆ T) (x : α) (hx : x ∉ T) : x ∉ S :=
  fun xs => hx (h xs)

-- Exercise 1.5 (Master)
example {R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R := by
  constructor
  · intro a as
    exact h₂ (h₁.left as)
  · intro r
    obtain c := h₁.2
    exact c (Subset.trans h₂ r)

example {R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R :=
  ⟨fun _ xs => h₂ (h₁.left xs), fun rs => h₁.right (Subset.trans h₂ rs)⟩

-- Exercise 1.6 (Master)

-- The empty set is the subset of any set `S` ...
example : ∃ U, U ⊆ S := by
  use ∅
  exact empty_subset S

example : ∃ U, U ⊆ S := ⟨∅, empty_subset S⟩

-- ... as is the set `S` itself
example : ∃ U, U ⊆ S := by
  use S

example : ∃ U, U ⊆ S := ⟨S, by rfl⟩

end P03S01B01

/-
## Set equality

`S = T` if and only if `x ∈ S ↔ x ∈ T` for all `x`.
-/

-- This is `Set.ext_iff` in mathlib ...
theorem ext_iff {S T : Set α} : S = T ↔ ∀ x, x ∈ S ↔ x ∈ T := Set.ext_iff

-- ... and the `ext` tactic also knows about it
example {S T : Set α} : S = T ↔ ∀ x, x ∈ S ↔ x ∈ T := by
  constructor
  · intro st x
    constructor
    · intro xs
      rw [← st]
      exact xs
    · intro xt
      rw [st]
      exact xt
  · intro h
    ext x
    exact h x

#golf example {S T : Set α} : S = T ↔ ∀ x, x ∈ S ↔ x ∈ T := by
  constructor
  · exact fun st x => ⟨fun xs => st ▸ xs, fun xt => st.symm ▸ xt⟩
  · intro h
    ext x
    exact h x

/-
## Side remark: extensionality axioms

Extensionality tells us when two objects of a specific form are equal. We just
saw set extensionality, which uses `funext` and `propext`:

```
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))
```

`funext` is just the extensionality of functions we have previously
already seen and used with the `ext` tactic

```
theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g := by
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
  let extfunApp (f : Quot eqv) (x : α) : β x :=
    Quot.liftOn f
      (fun (f : ∀ (x : α), β x) => f x)
      (fun _ _ h => h x)
  change extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
  exact congrArg extfunApp (Quot.sound h)
```

`propext` is extensionality of propositions, stating that `P ↔ Q` implies `P = Q`.
This is the only reason why we can `rw` with equivalences.

```
axiom propext {a b : Prop} : (a ↔ b) → a = b
```

`funext` also depends on `Quot.sound`, another axiom:

```
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
```
-/

/-
## Complements

For a set `S`, the complement `Sᶜ` is defined as the set of all elements of type
`α` that are not contained in `S`. Note that Lean always defines what "universe"
a set lives in through its type `α`, that is a complement is always well defined.
-/

example (S : Set α) : Sᶜ = {x | x ∉ S} := rfl

theorem mem_compl_iff (S : Set α) (x : α) : x ∈ Sᶜ ↔ x ∉ S := by rfl

/-
## Exercise Block B02

Do *not* use or look up the statements or other theorems in mathlib, only use
named theorems that we defined in this file. Once you proved a named theorem,
look up its actual proof in mathlib.
-/

namespace P03S01B02

variable {S T : Set α}

-- Exercise 2.1
theorem Subset.antisymm (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  rw [ext_iff]
  intro x
  constructor
  · intro s
    exact h₁ s
  · intro t
    exact h₂ t

example (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  ext x
  exact ⟨fun s => h₁ s, fun t => h₂ t⟩

example (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T :=
  ext_iff.mpr (fun _ => ⟨fun s => h₁ s, fun t => h₂ t⟩)

-- Let's see how mathlib proves it ...
#check Set.Subset.antisymm

example (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  apply Set.ext
  intro x
  constructor
  · intro x
    exact h₁ x
  · intro x
    exact h₂ x

example (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  apply Set.ext
  intro x
  constructor
  · exact fun x => h₁ x
  · exact fun x => h₂ x

-- this is how it is implemented in mathlib
example (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T :=
  Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩

-- Exercise 2.2
theorem Subset.antisymm_iff : (S = T) ↔ (S ⊆ T ∧ T ⊆ S) := by
  constructor
  · intro st
    rw [ext_iff] at st
    constructor
    all_goals intro x ; have hx := st x
    · intro xs
      exact hx.mp xs
    · intro xt
      exact hx.mpr xt
  · rintro ⟨st, ts⟩
    exact Subset.antisymm st ts

example : (S = T) ↔ (S ⊆ T ∧ T ⊆ S) := by
  constructor
  · intro st
    rw [st]
    trivial
  · rintro ⟨st, ts⟩
    exact Subset.antisymm st ts

-- Let's see how mathlib proves it ...
#check Set.Subset.antisymm_iff

example : (S = T) ↔ (S ⊆ T ∧ T ⊆ S) :=
  ⟨fun st => ⟨st.subset, st.symm.subset⟩, fun ⟨st, ts⟩ => Subset.antisymm st ts⟩

-- Exercise 2.3 (Master)
example {x : α} (h₁ : x ∈ S) (h₂ : x ∉ T) : ¬S ⊆ T := by
  intro st
  have xt := st h₁
  contradiction

example {x : α} (h₁ : x ∈ S) (h₂ : x ∉ T) : ¬S ⊆ T :=
  fun st => h₂ <| st h₁

-- Exercise 2.4
theorem compl_subset_compl_of_subset (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ := by
  rw [subset_def]
  intro x xtc
  rw [mem_compl_iff] at *
  intro xs
  let xt := h₁ xs
  exact xtc xt

example (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ := by
  intro x xtc xs
  have xt := h₁ xs
  contradiction

example (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ :=
  fun _ xtc xs => xtc <| h₁ xs

-- Let's see how mathlib proves it ...
#check Set.compl_subset_compl_of_subset

example (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ :=
  Set.compl_subset_compl.2 h₁

-- Exercise 2.5 (Master)
theorem compl_compl (S : Set α) : Sᶜᶜ = S := by
  ext s
  rw [mem_compl_iff Sᶜ s, mem_compl_iff S s]
  push_neg
  rfl

/-
Side remark: how exactly does `rw` match and do we need arguments?
-/

example (S : Set α) : Sᶜᶜ = S := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `S s` for `mem_compl_iff` and matches once
  push_neg
  rfl

example (S : Set α) : Sᶜᶜᶜ = Sᶜ := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜ s` for `mem_compl_iff` and matches *twice*
  push_neg
  rfl

example (S : Set α) : Sᶜᶜᶜᶜ = Sᶜᶜ := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜ s` for `mem_compl_iff` and matches once
  push_neg
  rfl

example (S : Set α) : Sᶜᶜᶜᶜ = Sᶜᶜ := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜ s` for `mem_compl_iff` and matches *twice*
  push_neg
  rfl

example (S : Set α) : Sᶜᶜᶜᶜ = Sᶜᶜ := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜ s` for `mem_compl_iff` and matches *twice*
  rw [mem_compl_iff] -- this infers arguments `Sᶜ s` for `mem_compl_iff` and matches *twice*
  push_neg
  rfl

example (S : Set α) : Sᶜᶜ = Sᶜᶜᶜᶜ := by
  ext s
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜᶜ s` for `mem_compl_iff` and matches once
  rw [mem_compl_iff] -- this infers arguments `Sᶜ s` for `mem_compl_iff` and matches once
  push_neg
  rfl

example (S : Set α) : Sᶜᶜᶜᶜ = Sᶜᶜ := by
  ext s
  repeat rw [mem_compl_iff] -- this reduces it all the way until no `_ ∈ _ᶜ` remains
  push_neg
  rfl

-- Exercise 2.6
theorem compl_subset_compl (S T : Set α) : Tᶜ ⊆ Sᶜ ↔ S ⊆ T := by
  constructor
  · intro h
    have := compl_subset_compl_of_subset h
    rw [compl_compl, compl_compl] at this
    exact this
  · intro h
    apply compl_subset_compl_of_subset
    exact h

example (S T : Set α) : Tᶜ ⊆ Sᶜ ↔ S ⊆ T :=
  ⟨fun h₁ => compl_compl S ▸ compl_compl T ▸ compl_subset_compl_of_subset h₁,
  compl_subset_compl_of_subset⟩

-- Exercise 2.7 (Master)
example (h : S ⊆ T) {x : α} (hx : x ∈ Tᶜ) : x ∈ Sᶜ := by
  rw [mem_compl_iff] at *
  intro xs
  have xt := h xs
  contradiction

example (h : S ⊆ T) {x : α} (hx : x ∈ Tᶜ) : x ∈ Sᶜ :=
  fun xs => hx (h xs)

-- Exercise 2.8 (Master)
example {R : Set α} (h₁ : R ⊆ S) (h₂ : S ⊆ T) : Tᶜ ⊆ Rᶜ := by
  apply compl_subset_compl_of_subset
  exact Subset.trans h₁ h₂

example (R S T : Set α) (h₁ : R ⊆ S) (h₂ : S ⊆ T) : Tᶜ ⊆ Rᶜ :=
  compl_subset_compl_of_subset (Subset.trans h₁ h₂)

-- Exercise 2.9
example (x : α) (S : Set α) : x ∈ Sᶜ ↔ (x ∈ S → False) := by
  rfl

end P03S01B02
