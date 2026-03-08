---
title: "let vs have in tactic mode"
parent: Addendum
nav_order: 9996
---

# `let` vs `have` in tactic mode
{: .no_toc }

*March 8, 2026*

---

In the course we use `have` to introduce intermediate results in proofs. Lean also has `let` in tactic mode. For propositions, both behave identically. For data, they differ in a way that matters.

## The rule

- **`have`** creates an **opaque** binding. The body is not visible to tactics like `simp`, `dsimp`, or `rfl`.
- **`let`** creates a **transparent** binding. The body is visible and can be unfolded.

## For propositions: no difference

Due to **proof irrelevance**, all proofs of the same proposition are definitionally equal. Whether the body is visible doesn't matter — the kernel considers any two proofs of `P` interchangeable.

```lean
example (h : P ∧ Q) : Q ∧ P := by
  have hp : P := h.1    -- opaque, but doesn't matter
  have hq : Q := h.2
  exact ⟨hq, hp⟩

example (h : P ∧ Q) : Q ∧ P := by
  let hp : P := h.1     -- transparent, but behaves the same
  let hq : Q := h.2
  exact ⟨hq, hp⟩
```

Both proofs work. For propositions, prefer `have` by convention (Mathlib style guide).

## For data: real difference

When the binding has a `Type` (not `Prop`) value, transparency matters:

```lean
example : Nat := by
  let x := 5
  exact x        -- works: x is transparently 5

example : 5 = 5 := by
  let x := 5
  show x = x     -- works: the kernel can see x = 5, so x = x is 5 = 5
  rfl
```

But with `have`:

```lean
example : 5 = 5 := by
  have x := 5
  show x = x     -- works: x = x is trivially true
  rfl             -- works, but note: the goal is `x = x`, not `5 = 5`
```

The difference becomes visible when you need the actual value:

```lean
example : 5 = 5 := by
  have x := 5
  show x = 5     -- fails: the kernel does not know x is 5
  rfl
```

## In the Infoview

The Infoview reflects the distinction:

| Tactic | Infoview shows |
|--------|----------------|
| `have q : Q := proof` | `q : Q` |
| `let q : Q := proof` | `q : Q := proof` |

With `have`, the body disappears from the context. With `let`, it stays visible.

## Guideline

| Context | Use |
|---------|-----|
| Intermediate proof step (any `Prop` goal) | `have` |
| Local computation with a value you need later | `let` |
| Unsure and working with propositions | `have` (convention) |
