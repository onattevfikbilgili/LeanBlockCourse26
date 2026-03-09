---
title: "Case splitting and naming syntax"
parent: Addendum
nav_order: 0
---

# Case splitting and naming syntax
{: .no_toc }

*March 9, 2026 · `P02–P05`*

---

When you split a proof into cases — via `induction`, `cases`, `split`, `by_cases`, or destructuring a hypothesis — you need two things: **focus on a branch** and **name the new variables**. Lean offers several mechanisms, and they overlap. This note sorts out what exists, what to prefer, and what to avoid.

- TOC
{:toc}

## The three focusing mechanisms

After any tactic that creates multiple goals, you need to select which goal to work on.

### `·` (focus dot)

Works after any multi-goal tactic. Positional (takes goals in order). Does not name anything.

```lean
induction xs
· contradiction       -- nil case
· rename_i y ys ih    -- cons case: name variables separately
  ...
```

### `case tag args =>`

Selects a goal by its **tag name** (the constructor or case name). Also renames inaccessible hypotheses.

```lean
induction xs
case nil => contradiction
case cons y ys ih => ...
```

This works after any goal-creating tactic — `induction`, `cases`, `split`, `constructor`, `refine`, `apply`. It is the standard approach for goals from `refine` and `apply`, which don't support `with`.

The `next args =>` syntax is shorthand for `case _ args =>` (wildcard tag, positional). It exists but offers no advantage over `case` with an explicit tag.

### `with | tag args =>`

Part of the `induction` / `cases` syntax itself. Dispatches all branches inline.

```lean
induction xs with
| nil => contradiction
| cons y ys ih => ...
```

Unlike `case`, this is **structural**: Lean warns about missing cases. It is the Mathlib-preferred style for `induction` and `cases`.

## Destructuring hypotheses: `rcases`, `obtain`, `rintro`

These use a **pattern language** with `⟨⟩` for structures and `|` for alternatives:

```lean
obtain ⟨p, q⟩ := h          -- AND: h : P ∧ Q
obtain p | q := h             -- OR:  h : P ∨ Q
rcases h with ⟨p, q⟩ | r     -- nested patterns
rintro ⟨p, q⟩                 -- intro + destructure in one step
```

These are the standard Mathlib tactics for working with hypotheses. They do not require knowing constructor names — the patterns reflect the logical structure (`⟨,⟩` for "and", `|` for "or").

## `rename_i`

Not a focusing mechanism. Renames the most recent inaccessible (auto-generated) hypotheses in the current goal. Useful inside a `·` block when you need names but don't want full structured syntax:

```lean
· rename_i y ys ih
  ...
```

## What to prefer

| Situation | Recommended | Example |
|-----------|-------------|---------|
| Induction | `with \| tag =>` | `induction xs with \| nil => ... \| cons y ys ih => ...` |
| Cases on a hypothesis | `with \| tag =>` or `rcases`/`obtain` | `cases h with \| inl p => ... \| inr q => ...` |
| Destructuring `∧`, `∨`, `↔` | `obtain` or `rcases` | `obtain ⟨p, q⟩ := h` |
| Intro + destructure | `rintro` | `rintro ⟨p, q⟩ \| r` |
| Goals from `apply`/`refine`/`constructor` | `case tag =>` | `case left => ...` |
| Goals from `split` | `case tag =>` or `·` | `case isTrue h => ...` |
| Goals from `by_cases` | `·` | `· ...` (positive) / `· ...` (negative) |
| Quick proof, don't care about names | `·` | `· contradiction` |

## What to avoid

**`cases'` and `induction'`** (from `Mathlib.Tactic.Cases`) use a flat `with x y z` naming syntax inherited from Lean 3. They are flagged by the Mathlib `DeprecatedSyntaxLinter` and banned from Mathlib's codebase. They still work, but prefer the alternatives above.

```lean
-- Avoid:
induction' xs with y ys ih

-- Prefer:
induction xs with
| nil => ...
| cons y ys ih => ...
```

## Summary

Three ways to **focus**: `·` (positional, no names), `case tag =>` (by name), `with | tag =>` (inline, structural). One way to **rename**: `rename_i`. One **pattern language**: `⟨⟩ |` shared by `rcases`, `obtain`, and `rintro`.
