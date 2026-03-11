import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.TFAE

/-
## Euclid's theorem: there are infinitely many prime

How exactly is this result stated?

### [Wikipedia](https://en.wikipedia.org/wiki/Euclid%27s_theorem)

"Euclid's theorem (...) asserts that there are infinitely many prime numbers."

### Aigner and Ziegler: Proofs from THE BOOK

* "It shows that the sequence of primes does not end."
* "a finite set {p1,...,pr} cannot be the collection of all prime numbers"
* "We will show that any two Fermat numbers are relatively prime; hence there must be infinitely
   many primes.
* "The set of primes cannot be finite"
* "The function counting the number of primes that are less than or equal to a real number x is
   unboundend, and so there are infinitely many primes"
* "Our final proof goes a considerable step further and demonstrates not only that there are
   infinitely many primes, but also that the series ∑p 1/p diverges.""
-/


/-
You will now have to work with mathlib, i.e., understand its definitions and finds its results.

To do this, you should:

(I)   Look up the correct section of the area / type / structure that you are interested in
      and read the comments and basic definitions of at least the main files (`Defs.lean` and
      `Basic.lean`). Either understand the definitions or, if they are too opaque and disappear
      in formal abstraction, find the relevant equivalent definition statements to `rw` with.

(II)  Hover or cmd-click anything that is unclear or unexpected and click through in VS Code.

(III) Use `exact?` or `simp?` whenever you think you have a nuclear expression that *should*
      be in mathlib to try and find it. Often it is advisable to extract the statement into
      separate `example` for this. You can also manually search the files, guess the 
      expected theorem name based on the [mathlib naming convention](https://leanprover-community.github.io/contribute/naming.html),
      use [leansearch.net](https://leansearch.net) or [Loogle](https://loogle.lean-lang.org),
      talk to people on [Is there code for X? on zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Complexity.20theory/with/578655619)
      or ask ChatGPT, Claude, ... with online research tools and maybe even a lean environment.
-/

theorem infinitude_of_primes_tfae : [

    -- The set of primes is infinite (could do sth similar with `{ p : ℕ // p.Prime }`)
    { p : ℕ | p.Prime }.Infinite,

    -- For any finite set we can find a prime number outside of it
    ∀ (S : Finset ℕ), (∃ p ∉ S, p.Prime),

    -- For any finite set *of prime numbers* we can find a prime number outside of it
    (∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime)),

    -- For any natural number there exists a prime strictly greater than it
    (∀ n : ℕ, (∃ p > n, p.Prime)),

    -- There exists an injection from the Natural numbers into the primes
    ∃ (P : ℕ → ℕ) (h : P.Injective), (∀ k, (P k).Prime) ].TFAE := by

  tfae_have 1 ↔ 2 := by sorry

  tfae_have 2 ↔ 3 := by sorry

  tfae_have 4 ↔ 2 := by sorry

  tfae_have 1 ↔ 5 := by sorry

  tfae_finish





















