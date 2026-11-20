/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.MaximalPowerDivisor

/-!
# Maximal Power Divisor Length

The module relates the length of the original exponent vector to that after division by its maximal power divisor. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.maximalDivisorLength`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
A nonzero vector of weighted length at most `4 * H` is a positive multiple at most `6 * H` of a primitive subgroup vector of length at most `4 * H`. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem maximalDivisorLength {ι : Type*} [Fintype ι] (K : AddSubgroup (ι → ℤ))
    {e : ι → ℤ} (he : e ∈ K) (hne : e ≠ 0) (l : ι → ℝ)
    (hl : ∀ j, (2 : ℝ) / 3 ≤ l j) {H : ℝ}
    (hL : ∑ j, |(e j : ℝ)| * l j ≤ 4 * H) :
    ∃ (k : ℕ) (w : ι → ℤ), 0 < k ∧ (k : ℝ) ≤ 6 * H ∧ w ∈ K ∧ k • w = e ∧
      (∀ (n : ℕ) (u : ι → ℤ), u ∈ K → n • u = w → n = 1) ∧
      ∑ j, |(w j : ℝ)| * l j ≤ 4 * H := by
  classical
  have hj : ∃ j, e j ≠ 0 := by
    by_contra! hh
    exact hne (funext hh)
  obtain ⟨j, hj⟩ := hj
  obtain ⟨k, w, hk, hkD, hw, hkw, hp⟩ := _root_.AbcTwoNinths.PolyCap.maximalDivisor K he hj
  have hpos (i : ι) : 0 ≤ l i := by linarith [hl i]
  have hjL : |(e j : ℝ)| * l j ≤ 4 * H :=
    (Finset.single_le_sum (f := fun i => |(e i : ℝ)| * l i)
      (fun i _ => mul_nonneg (abs_nonneg _) (hpos i))
      (Finset.mem_univ j)).trans hL
  have hkR : (k : ℝ) ≤ |(e j : ℝ)| := by
    have hi : (k : ℤ) ≤ |e j| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hkD
    simpa only [Int.cast_natCast, Int.cast_abs] using (Int.cast_le (R := ℝ)).2 hi
  have hbound : (k : ℝ) ≤ 6 * H := by
    have ha := mul_le_mul_of_nonneg_right hkR (hpos j)
    have hb := mul_le_mul_of_nonneg_left (hl j) (by positivity : 0 ≤ (k : ℝ))
    linarith
  refine ⟨k, w, hk, hbound, hw, hkw, hp, le_trans ?_ hL⟩
  apply Finset.sum_le_sum
  intro i _
  have hi := congrFun hkw i
  change (k : ℤ) * w i = e i at hi
  have hi' : (k : ℝ) * (w i : ℝ) = (e i : ℝ) := by exact_mod_cast hi
  rw [← hi', abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ))]
  apply mul_le_mul_of_nonneg_right _ (hpos i)
  exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast hk)

end

end AbcTwoNinths.PolyCap
