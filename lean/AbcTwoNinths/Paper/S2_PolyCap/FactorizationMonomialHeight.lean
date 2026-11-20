/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.DepthAndQuotientHeight
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationMonomialPowers

/-!
# Factorization Monomial Height

The module bounds rational height of an evaluated factorization monomial by its weighted exponents. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.monomialHeightLe`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The logarithmic height of a monomial in positive integers is at most the sum of their logarithms weighted by the absolute exponents. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem monomialHeightLe {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℤ)
    (hq : ∀ i, 0 < q i) :
    _root_.AbcTwoNinths.Basic.padicRationalHeight (∏ i, (q i : ℚ) ^ e i) ≤
      ∑ i, |(e i : ℝ)| * Real.log (q i) := by
  rw [_root_.AbcTwoNinths.PolyCap.monomialSplit q e hq]
  refine (_root_.AbcTwoNinths.PolyCap.ratioHeightLe (Finset.prod_pos (fun i _ => pow_pos (hq i) _))
    (Finset.prod_pos (fun i _ => pow_pos (hq i) _))).trans ?_
  push_cast
  rw [Real.log_prod, Real.log_prod, ← Finset.sum_add_distrib]
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_pow, Real.log_pow, ← add_mul]
    congr 1
    have hi : ((e i).toNat : ℤ) + ((-e i).toNat : ℤ) = |e i| := by
      obtain h | h := le_total 0 (e i)
      · rw [abs_of_nonneg h, Int.toNat_of_nonpos (show -e i ≤ 0 by omega),
          Int.toNat_of_nonneg h]
        simp
      · rw [abs_of_nonpos h, Int.toNat_of_nonpos h,
          Int.toNat_of_nonneg (show 0 ≤ -e i by omega)]
        simp
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) hi
  · exact fun i _ => pow_ne_zero _ (by exact_mod_cast (hq i).ne')
  · exact fun i _ => pow_ne_zero _ (by exact_mod_cast (hq i).ne')

end

end AbcTwoNinths.PolyCap
