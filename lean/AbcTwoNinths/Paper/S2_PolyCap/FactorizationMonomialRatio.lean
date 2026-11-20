/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Factorization Monomial Ratio

The module expresses a rational factorization ratio as a signed monomial and computes its length. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.factorizationRatioLength`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open scoped BigOperators

/--
The rational product of prime powers over a finite superset of the prime factors recovers a nonzero natural number.
-/
theorem expandFactorization (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ)
    (hS : n.primeFactors ⊆ S) :
    (∏ q ∈ S, (q : ℚ) ^ n.factorization q) = (n : ℚ) := by
  classical
  rw [← Finset.prod_subset hS]
  · exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  · intro q _ hq
    have hzero : n.factorization q = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hq
    rw [hzero, pow_zero]

/--
Differences of prime exponents over a common positive support represent the ratio of two nonzero natural numbers.
-/
theorem factorizationRatio {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (S : Finset ℕ)
    (hS : x.primeFactors ∪ y.primeFactors ⊆ S) (hpos : ∀ q ∈ S, 0 < q) :
    (∏ q ∈ S, (q : ℚ) ^ ((x.factorization q : ℤ) - y.factorization q)) =
      (x : ℚ) / y := by
  classical
  calc
    _ = ∏ q ∈ S, (q : ℚ) ^ x.factorization q / (q : ℚ) ^ y.factorization q := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [zpow_sub₀ (by exact_mod_cast (hpos q hq).ne'), zpow_natCast, zpow_natCast]
    _ = _ := by
      rw [Finset.prod_div_distrib, _root_.AbcTwoNinths.PolyCap.expandFactorization x hx S,
        _root_.AbcTwoNinths.PolyCap.expandFactorization y hy S]
      · exact fun q hq => hS (Finset.mem_union_right _ hq)
      · exact fun q hq => hS (Finset.mem_union_left _ hq)

/--
The weighted absolute length of the factorization difference is at most the sum of the two logarithms. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem factorizationRatioLength {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (S : Finset ℕ) (hS : x.primeFactors ∪ y.primeFactors ⊆ S)
    (hpos : ∀ q ∈ S, 1 ≤ q) :
    (∑ q ∈ S, |(x.factorization q : ℝ) - y.factorization q| * Real.log q) ≤
      Real.log x + Real.log y := by
  classical
  have hexp (n : ℕ) (hn : n ≠ 0) (hs : n.primeFactors ⊆ S) :
      (∑ q ∈ S, (n.factorization q : ℝ) * Real.log q) = Real.log n := by
    have he : (∏ q ∈ S, (q : ℝ) ^ n.factorization q) = (n : ℝ) := by
      exact_mod_cast _root_.AbcTwoNinths.PolyCap.expandFactorization n hn S hs
    rw [← he, Real.log_prod]
    · simp only [Real.log_pow]
    · intro q hq
      exact pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by have := hpos q hq; omega))
  rw [← hexp x hx (fun q hq => hS (Finset.mem_union_left _ hq)),
    ← hexp y hy (fun q hq => hS (Finset.mem_union_right _ hq)), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpos q hq))
  rw [abs_le]
  constructor <;> linarith [show 0 ≤ (x.factorization q : ℝ) by positivity,
    show 0 ≤ (y.factorization q : ℝ) by positivity]

end

end AbcTwoNinths.PolyCap
