/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.Products

/-!
# Roof Mass

The module expresses the distinguished prime's valuation mass as a factorization term and preserves it under reindexing. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.roofMass`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section



private theorem logFactorOn {k : ℕ} (hk : k ≠ 0) (s : Finset ℕ)
    (hs : k.primeFactors ⊆ s) :
    (∑ i : s, (k.factorization i : ℝ) * Real.log (i.val : ℝ)) = Real.log (k : ℝ) := by
  classical
  rw [Finset.sum_coe_sort s (fun q : ℕ => (k.factorization q : ℝ) * Real.log (q : ℝ)),
    ← Finset.sum_subset hs]
  · have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_pow_factorization hk)
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [h, Real.log_prod]
    · simp only [Real.log_pow]
    · intro q hq
      exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)
  · intro q _ hq
    have hz : k.factorization q = 0 := by
      by_contra hh
      exact hq (Finsupp.mem_support_iff.mpr hh)
    simp [hz]

/--
For coprime nonzero numerator and denominator, the weighted absolute exponent sum is the logarithm of their product. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem roofMass {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) (hc : n.Coprime d) :
    (∑ i : _root_.AbcTwoNinths.ExteriorE2.Support n d, |(((_root_.AbcTwoNinths.ExteriorE2.vec n d).toAdd i : ℤ) : ℝ)| *
      Real.log (_root_.AbcTwoNinths.ExteriorE2.base n d i : ℝ)) = Real.log ((n : ℝ) * d) := by
  classical
  have habs (i : _root_.AbcTwoNinths.ExteriorE2.Support n d) :
      |(((_root_.AbcTwoNinths.ExteriorE2.vec n d).toAdd i : ℤ) : ℝ)| =
        (n.factorization i : ℝ) + (d.factorization i : ℝ) := by
    change |(((n.factorization i : ℤ) - d.factorization i : ℤ) : ℝ)| = _
    push_cast
    by_cases h : n.factorization i = 0
    · simp [h, abs_of_nonneg (Nat.cast_nonneg (d.factorization i) : (0 : ℝ) ≤ _)]
    · have hz : d.factorization i = 0 := by
        by_contra h'
        have hni : i.val ∣ n := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr h)
        have hdi : i.val ∣ d := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr h')
        exact (_root_.AbcTwoNinths.ExteriorE2.prime n d i).not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hni hdi)
      simp [hz, abs_of_nonneg (Nat.cast_nonneg (n.factorization i) : (0 : ℝ) ≤ _)]
  simp only [habs, add_mul, Finset.sum_add_distrib, _root_.AbcTwoNinths.ExteriorE2.base]
  rw [logFactorOn hn _ Finset.subset_union_left, logFactorOn hd _ Finset.subset_union_right,
    Real.log_mul (by exact_mod_cast hn) (by exact_mod_cast hd)]

end

end AbcTwoNinths.Selection
