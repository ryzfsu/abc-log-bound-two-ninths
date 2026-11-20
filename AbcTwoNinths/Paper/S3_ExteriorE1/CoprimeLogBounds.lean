/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Coprime Log Bounds

A variable-radius bound for coprime coefficients extends to arbitrary positive coefficients by
dividing out their gcd. Multiplicative independence ensures the two-logarithm form is nonzero. This
supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.logBoundOfCoprime`
* `AbcTwoNinths.ExteriorE1.independentLogNe`
* `AbcTwoNinths.ExteriorE1.realVarRadiusLaurent1157OfCoprime`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
A uniform logarithmic bound for coprime positive coefficients extends to all positive coefficients.
-/
theorem logBoundOfCoprime {a b x y C radius : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hr : 0 < radius)
    (hC : 0 ≤ C) (h₁ h₂ : ℕ) (hp₁ : 0 < h₁) (hp₂ : 0 < h₂)
    (hne : ∀ m n : ℕ, 0 < m → 0 < n → (n : ℝ)*b - (m : ℝ)*a ≠ 0)
    (hc : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n →
      -Real.log |(n : ℝ)*b - (m : ℝ)*a| ≤ C *
        (max 4 (Real.log ((m : ℝ)/x + (n : ℝ)/y) / radius))^2) :
    -Real.log |(h₂ : ℝ)*b - (h₁ : ℝ)*a| ≤ C *
      (max 4 (Real.log ((h₁ : ℝ)/x + (h₂ : ℝ)/y) / radius))^2 := by
  let g := h₁.gcd h₂
  let m := h₁ / g
  let n := h₂ / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left h₂ hp₁
  have hm : g * m = h₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left h₁ h₂)
  have hn : g * n = h₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right h₁ h₂)
  have hm' : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm; omega)
  have hn' : 0 < n := Nat.pos_of_ne_zero (fun h => by simp [h] at hn; omega)
  have he : (h₂ : ℝ)*b - (h₁ : ℝ)*a = (g : ℝ)*((n : ℝ)*b - (m : ℝ)*a) := by
    rw [← hm, ← hn]
    push_cast
    ring
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have ha : 0 < |(n : ℝ)*b - (m : ℝ)*a| := abs_pos.mpr (hne m n hm' hn')
  have hmul : |(n : ℝ)*b - (m : ℝ)*a| ≤ |(h₂ : ℝ)*b - (h₁ : ℝ)*a| := by
    rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (g : ℝ) by positivity)]
    exact le_mul_of_one_le_left ha.le hg'
  refine (neg_le_neg (Real.log_le_log ha hmul)).trans
    ((hc m n hm' hn' (Nat.coprime_div_gcd_div_gcd hg)).trans ?_)
  have h1 : (m : ℝ) ≤ h₁ := by exact_mod_cast (Nat.div_le_self h₁ g)
  have h2 : (n : ℝ) ≤ h₂ := by exact_mod_cast (Nat.div_le_self h₂ g)
  have ht := Real.log_le_log
    (show 0 < (m : ℝ)/x + (n : ℝ)/y by positivity)
    (add_le_add (div_le_div_of_nonneg_right h1 hx.le) (div_le_div_of_nonneg_right h2 hy.le))
  have hmax : max 4 (Real.log ((m : ℝ)/x + (n : ℝ)/y) / radius) ≤
      max 4 (Real.log ((h₁ : ℝ)/x + (h₂ : ℝ)/y) / radius) :=
    max_le_max_left _ (div_le_div_of_nonneg_right ht hr.le)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_trans (by norm_num) (le_max_left _ _)) hmax _) hC

/--
Multiplicatively independent positive rationals give a nonzero real log difference when its first natural coefficient is positive.
-/
theorem independentLogNe (q r : ℚ) (hq : 0 < q) (hr : 0 < r)
    (hind : ∀ a b : ℤ, q ^ a * r ^ b = 1 → a = 0 ∧ b = 0)
    (m n : ℕ) (hm : 0 < m) :
    (n : ℝ) * Real.log (r : ℝ) - (m : ℝ) * Real.log (q : ℝ) ≠ 0 := by
  intro h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpow : (r : ℝ)^n = (q : ℝ)^m := by
    simpa [Real.exp_nat_mul, Real.exp_log hq', Real.exp_log hr'] using
      congrArg Real.exp (sub_eq_zero.mp h)
  have hp : r^n = q^m := by exact_mod_cast hpow
  have he : q ^ (-(m : ℤ)) * r ^ (n : ℤ) = 1 := by
    rw [zpow_neg, zpow_natCast, zpow_natCast, hp, inv_mul_cancel₀ (by positivity)]
  have := (hind _ _ he).1
  omega

/--
The coprime variable-radius bound with constant 1157 extends to all positive coefficient pairs. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realVarRadiusLaurent1157OfCoprime
    (q r : ℚ) (hq : 0 < q) (hr : 0 < r)
    (hind : ∀ a b : ℤ, q ^ a * r ^ b = 1 → a = 0 ∧ b = 0)
    (radius η₁ η₂ : ℝ) (hrad : 0 < radius) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hc : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n →
      -Real.log |(n : ℝ)*Real.log (r : ℝ) - (m : ℝ)*Real.log (q : ℝ)| ≤
        1157 * η₁ * η₂ * (max 4 (Real.log ((m : ℝ)/η₂ + (n : ℝ)/η₁) / radius))^2 / radius)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    -Real.log |(n : ℝ)*Real.log (r : ℝ) - (m : ℝ)*Real.log (q : ℝ)| ≤
      1157 * η₁ * η₂ * (max 4 (Real.log ((m : ℝ)/η₂ + (n : ℝ)/η₁) / radius))^2 / radius := by
  have hC : 0 ≤ 1157 * η₁ * η₂ / radius := by positivity
  have h := _root_.AbcTwoNinths.ExteriorE1.logBoundOfCoprime hη₂ hη₁ hrad hC m n hm hn
    (fun m n hm _ => _root_.AbcTwoNinths.ExteriorE1.independentLogNe q r hq hr hind m n hm)
    (fun m n hm hn hcop => by
      convert hc m n hm hn hcop using 1
      ring)
  convert h using 1
  ring

end

end AbcTwoNinths.ExteriorE1
