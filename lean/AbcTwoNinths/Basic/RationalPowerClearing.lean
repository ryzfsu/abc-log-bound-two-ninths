/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Rational Power Clearing

The module clears rational powers and bounds the numerator obtained from a sum of two powers.

## Main results
* `AbcTwoNinths.Basic.clearPower`
* `AbcTwoNinths.Basic.clearPowerHeight`
* `AbcTwoNinths.Basic.clearTwoPowerSum`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

set_option autoImplicit false

/--
A factor depending on the rational base and interval endpoints clears every power in that interval.
-/
theorem clearPower (a : ℚ) (ha : a ≠ 0) (l n u : ℕ)
    (hln : l ≤ n) (hnu : n ≤ u) :
    (a ^ l)⁻¹ * (a.den : ℚ) ^ (u-l) * a^n =
      ((a.num ^ (n-l) * (a.den : ℤ) ^ (u-n) : ℤ) : ℚ) := by
  have he₁ : n = l + (n-l) := by omega
  have he₂ : u-l = (u-n) + (n-l) := by omega
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hpow : a^l ≠ 0 := pow_ne_zero _ ha
  have hsplit : a^n = a^l * a^(n-l) := by rw [← pow_add, ← he₁]
  rw [hsplit, he₂, pow_add]
  push_cast
  have hadd : a * (a.den : ℚ) = a.num := by
    have h := Rat.num_div_den a
    exact (eq_div_iff hd).mp h.symm
  calc
    _ = (a * (a.den : ℚ)) ^ (n-l) * (a.den : ℚ) ^ (u-n) := by
      rw [mul_pow]
      calc
        _ = ((a^l)⁻¹ * a^l) * (a^(n-l) * (a.den : ℚ)^(n-l)) *
            (a.den : ℚ)^(u-n) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hpow, one_mul]
    _ = _ := by rw [hadd]

/--
The absolute value of the cleared power is bounded by the exponential of the interval width times the logarithmic height.
-/
theorem clearPowerHeight (a : ℚ) (l n u : ℕ)
    (hln : l ≤ n) (hnu : n ≤ u) :
    (((a.num ^ (n-l) * (a.den : ℤ) ^ (u-n) : ℤ).natAbs : ℕ) : ℝ) ≤
      exp ((u-l : ℕ) * log (max (a.num.natAbs : ℝ) (a.den : ℝ))) := by
  have hdeg : (n-l) + (u-n) = u-l := by omega
  let H := max (a.num.natAbs : ℝ) (a.den : ℝ)
  have hd : 0 < (a.den : ℝ) := by exact_mod_cast a.den_pos
  have hH : 0 < H := hd.trans_le (le_max_right _ _)
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast]
  push_cast
  change (a.num.natAbs : ℝ)^(n-l) * (a.den : ℝ)^(u-n) ≤ exp ((u-l : ℕ) * log H)
  rw [exp_nat_mul, exp_log hH, ← hdeg, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _)
    (pow_le_pow_left₀ hd.le (le_max_right _ _) _) (by positivity) (by positivity)

/--
A common factor clears a finite sum of products of two rational powers and bounds the resulting integer.
-/
theorem clearTwoPowerSum {ι : Type*} (s : Finset ι)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (la ua lb ub : ℕ) (e f : ι → ℕ) (c : ι → ℤ) (C : ℝ)
    (he : ∀ i ∈ s, la ≤ e i ∧ e i ≤ ua)
    (hf : ∀ i ∈ s, lb ≤ f i ∧ f i ≤ ub)
    (hc : ∀ i ∈ s, (c i).natAbs ≤ C) (hC : 0 ≤ C) :
    ∃ Z : ℤ,
      (Z : ℚ) = ((a^la)⁻¹ * (a.den : ℚ)^(ua-la)) *
        ((b^lb)⁻¹ * (b.den : ℚ)^(ub-lb)) *
        ∑ i ∈ s, (c i : ℚ) * a^(e i) * b^(f i) ∧
      (Z.natAbs : ℝ) ≤ (s.card : ℝ) * C *
        exp ((ua-la : ℕ) * log (max (a.num.natAbs : ℝ) (a.den : ℝ)) +
             (ub-lb : ℕ) * log (max (b.num.natAbs : ℝ) (b.den : ℝ))) := by
  let A (i : ι) : ℤ := a.num^(e i-la) * (a.den : ℤ)^(ua-e i)
  let B (i : ι) : ℤ := b.num^(f i-lb) * (b.den : ℤ)^(ub-f i)
  refine ⟨∑ i ∈ s, c i * A i * B i, ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hA := _root_.AbcTwoNinths.Basic.clearPower a ha la (e i) ua (he i hi).1 (he i hi).2
    have hB := _root_.AbcTwoNinths.Basic.clearPower b hb lb (f i) ub (hf i hi).1 (hf i hi).2
    change _ = (A i : ℚ) at hA
    change _ = (B i : ℚ) at hB
    rw [← hA, ← hB]
    ring
  · let X := (ua-la : ℕ) * log (max (a.num.natAbs : ℝ) (a.den : ℝ))
    let Y := (ub-lb : ℕ) * log (max (b.num.natAbs : ℝ) (b.den : ℝ))
    change (((∑ i ∈ s, c i * A i * B i : ℤ).natAbs : ℕ) : ℝ) ≤
      (s.card : ℝ) * C * exp (X+Y)
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sum]
    calc
      _ ≤ ∑ i ∈ s, |((c i * A i * B i : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, C * exp X * exp Y := by
        apply Finset.sum_le_sum
        intro i hi
        push_cast
        simp only [abs_mul, ← Int.cast_abs, ← Nat.cast_natAbs]
        exact mul_le_mul
          (mul_le_mul (hc i hi) (_root_.AbcTwoNinths.Basic.clearPowerHeight a la (e i) ua (he i hi).1 (he i hi).2)
            (by positivity) hC)
          (_root_.AbcTwoNinths.Basic.clearPowerHeight b lb (f i) ub (hf i hi).1 (hf i hi).2)
          (by positivity) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, exp_add]; ring

end

end AbcTwoNinths.Basic
