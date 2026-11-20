/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Smooth Part Factorization

The module defines the smooth part from the primes below the cutoff and gives its prime-power factorization. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.smoothPartFactorization`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
The prime factors of `A` at most the real cutoff `Q`. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def smoothPrimeFactors (A : ℕ) (Q : ℝ) : Finset ℕ := by
  classical
  exact A.primeFactors.filter fun q => (q : ℝ) ≤ Q

/-- The smooth part. This is used in the proof of Proposition 4.1 of the paper. -/
noncomputable def smoothPart (A : ℕ) (Q : ℝ) : ℕ :=
  ∏ q ∈ _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q, q ^ A.factorization q

/--
The `Q` -smooth part of positive `A` divides `A` , and its logarithm is the sum of the
valuation-weighted logarithms of the prime divisors at most `Q` .
-/
theorem smoothPartFactorization {A : ℕ} (hA : 0 < A) (Q : ℝ) :
    _root_.AbcTwoNinths.ExteriorE2.smoothPart A Q ∣ A ∧
      Real.log (_root_.AbcTwoNinths.ExteriorE2.smoothPart A Q : ℝ) =
        ∑ q ∈ _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q, (A.factorization q : ℝ) * Real.log (q : ℝ) := by
  have hs : _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q ⊆ A.primeFactors := by
    classical
    exact Finset.filter_subset _ _
  constructor
  · unfold _root_.AbcTwoNinths.ExteriorE2.smoothPart
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans
      (Nat.prod_primeFactors_pow_factorization hA.ne').symm.dvd
  · unfold _root_.AbcTwoNinths.ExteriorE2.smoothPart
    push_cast
    rw [Real.log_prod (fun q hq => pow_ne_zero _ (by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (hs hq)).ne_zero))]
    simp only [Real.log_pow]

end

end AbcTwoNinths.ExteriorE2
