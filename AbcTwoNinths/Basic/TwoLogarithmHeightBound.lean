/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalBinomialMinor

/-!
# Two Logarithm Height Bound

Centering bounds the spread of the permutation exponents, with an explicit width for 36 indices.
The factor that clears an exponent interval of a rational p-adic unit also has valuation zero.

## Main results
* `AbcTwoNinths.Basic.permutationExponentWidth`
* `AbcTwoNinths.Basic.exactWidth36`
* `AbcTwoNinths.Basic.clearingUnit`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open scoped BigOperators

/--
Two bounded weight families of equal total mass have weighted sums differing by at most their common bound times the centered absolute deviation.
-/
theorem centeredExponentWidth {ι : Type*} [Fintype ι]
    (t r s : ι → ℝ) (c R : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ R) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ R)
    (htot : ∑ i, r i = ∑ i, s i) :
    |(∑ i, t i * r i) - ∑ i, t i * s i| ≤ R * ∑ i, |t i - c| := by
  have hcenter :
      (∑ i, t i * r i) - ∑ i, t i * s i = ∑ i, (t i - c) * (r i - s i) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, htot]
    ring
  rw [hcenter]
  calc
    _ ≤ ∑ i, |(t i - c) * (r i - s i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, R * |t i - c| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm R]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hr i).1, (hs i).2], by linarith [(hr i).2, (hs i).1]⟩
    _ = _ := by rw [Finset.mul_sum]

/--
The spread between two permutations of a bounded nonnegative weight family is controlled by the centered absolute deviation of the exponents.
-/
theorem permutationExponentWidth {ι : Type*} [Fintype ι]
    (t r : ι → ℝ) (c R : ℝ) (σ τ : Equiv.Perm ι)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ R) :
    |(∑ i, t i * r (σ i)) - ∑ i, t i * r (τ i)| ≤ R * ∑ i, |t i - c| := by
  apply _root_.AbcTwoNinths.Basic.centeredExponentWidth t (r ∘ σ) (r ∘ τ) c R
  · exact fun i => hr (σ i)
  · exact fun i => hr (τ i)
  · exact (Equiv.sum_comp σ r).trans (Equiv.sum_comp τ r).symm

/-- The sum of absolute distances from the midpoint of the 36 consecutive indices is 324. -/
theorem center36 :
    (∑ j : Fin 36, |(j.val : ℝ) - 35/2|) = 324 := by
  norm_num [Fin.sum_univ_succ, abs_of_nonneg, abs_of_nonpos]

/--
For K copies of 36 columns with weights at most R, one permutation sum exceeds another by at most K times 324 times R.
-/
theorem exactWidth36 (K R : ℕ) (r : Fin K × Fin 36 → ℕ)
    (hr : ∀ j, r j ≤ R) (σ τ : Equiv.Perm (Fin K × Fin 36)) :
    (∑ j, (σ j).2.val * r j) ≤ (∑ j, (τ j).2.val * r j) + K*324*R := by
  have h := _root_.AbcTwoNinths.Basic.permutationExponentWidth (fun i : Fin K × Fin 36 => (i.2.val : ℝ))
    (fun i => (r i : ℝ)) (35/2) R σ.symm τ.symm
    (fun i => ⟨by positivity, by exact_mod_cast hr i⟩)
  have hc : (∑ i : Fin K × Fin 36, |(i.2.val : ℝ) - 35/2|) = (K : ℝ) * 324 := by
    rw [Fintype.sum_prod_type]
    simp only [_root_.AbcTwoNinths.Basic.center36, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hx (π : Equiv.Perm (Fin K × Fin 36)) :
      (∑ j, ((π j).2.val : ℝ) * (r j : ℝ)) =
      ∑ i, (i.2.val : ℝ) * (r (π.symm i) : ℝ) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp π (fun i => (i.2.val : ℝ) * (r (π.symm i) : ℝ)))
  have hle := (abs_le.mp h).2
  rw [← hx σ, ← hx τ, hc] at hle
  have hR : (∑ j, ((σ j).2.val : ℝ) * (r j : ℝ)) ≤
      (∑ j, ((τ j).2.val : ℝ) * (r j : ℝ)) + (K : ℝ)*324*(R : ℝ) := by linarith
  exact_mod_cast hR

/--
For a nonzero rational of valuation zero at a prime, the factor clearing its exponent interval is nonzero and has valuation zero at that prime.
-/
theorem clearingUnit (p : ℕ) (hp : p.Prime) (a : ℚ)
    (ha : a ≠ 0) (hv : padicValRat p a = 0) (l u : ℕ) :
    ((a^l)⁻¹ * (a.den : ℚ)^(u-l)) ≠ 0 ∧
      padicValRat p ((a^l)⁻¹ * (a.den : ℚ)^(u-l)) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  refine ⟨mul_ne_zero (inv_ne_zero (pow_ne_zero _ ha)) (pow_ne_zero _ hd), ?_⟩
  have hvd : padicValNat p a.den = 0 := by
    rcases a.num_or_den_zero_padicVal hp with h | h
    · simpa [padicValRat_def, h] using hv
    · exact h
  rw [padicValRat.mul (inv_ne_zero (pow_ne_zero _ ha)) (pow_ne_zero _ hd),
    padicValRat.inv, padicValRat.pow, padicValRat.pow, padicValRat.of_nat, hv, hvd]
  simp

end

end AbcTwoNinths.Basic
