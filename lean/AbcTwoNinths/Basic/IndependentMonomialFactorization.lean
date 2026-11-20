/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Prime Support of a Side Ratio

The prime support of `b / c` is the union of the prime divisors of `b` and `c`. Its signed prime
exponents are the differences of the two factorizations.

## Main results
* `AbcTwoNinths.Basic.supp`
* `AbcTwoNinths.Basic.coeff`
* `AbcTwoNinths.Basic.suppPrime`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section
open Real

/-- The prime support of the quotient $b/c$ is the union of the prime divisors of $b$ and $c$. -/
def supp (t : _root_.AbcTwoNinths.Basic.Triple) : Finset ℕ := t.b.primeFactors ∪ t.c.primeFactors
/--
The valuation of $b/c$ at $p$ is the signed difference of the two natural-number factorizations.
-/
def coeff (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) : ℤ := (t.b.factorization p : ℤ) - t.c.factorization p

/-- Every member of the prime support of $b/c$ is prime. -/
theorem suppPrime (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ} (hp : p ∈ _root_.AbcTwoNinths.Basic.supp t) : p.Prime := by
  rcases Finset.mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h

end

end AbcTwoNinths.Basic
