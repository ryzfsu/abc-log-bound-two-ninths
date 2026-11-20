/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PowerLiftingValuation

/-!
# Unbounded Depth Height Comparison

Rescaling the normalized height parameters by `log p` gives the two-logarithm valuation estimate
with constant 147 for positive exponents at odd primes.

## Main results
* `AbcTwoNinths.Basic.TwoLogUnbounded`
* `AbcTwoNinths.Basic.twoLogUnboundedOfNormalized`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

open Real

section

/--
The two-logarithm valuation estimate with constant K for positive exponents of independent positive rational principal units.
-/
def TwoLogUnbounded (K : ℝ) : Prop :=
  ∀ (p : ℕ) (a b : ℚ) (m n : ℕ) (η₁ η₂ : ℝ),
    p.Prime → 2 < p → _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p a → _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p b → _root_.AbcTwoNinths.Basic.RatMulIndependent a b →
    0 < m → 0 < n →
    max (_root_.AbcTwoNinths.Basic.rationalHeight a) (log (p : ℝ)) ≤ η₁ →
    max (_root_.AbcTwoNinths.Basic.rationalHeight b) (log (p : ℝ)) ≤ η₂ →
    (padicValRat p (a^m - b^n) : ℝ) * (log (p : ℝ))^2 ≤
      K * η₁ * η₂ *
        (max 4 (log (exp 2 * log (p : ℝ) * ((m : ℝ)/η₂ + (n : ℝ)/η₁)) /
          log (p : ℝ)))^2

end

section



/--
Rescaling the height parameters by the logarithm of the prime gives the two-logarithm estimate with constant 147.
-/
theorem twoLogUnboundedOfNormalized
    (provider : ∀ (p m n : ℕ) (a b : ℚ) (A B : ℝ),
      p.Prime → 2 < p → _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a → _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b → _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b →
      0 < m → 0 < n → 1 ≤ A → 1 ≤ B →
      _root_.AbcTwoNinths.Basic.padicRationalHeight a ≤ A * log (p : ℝ) → _root_.AbcTwoNinths.Basic.padicRationalHeight b ≤ B * log (p : ℝ) →
      (padicValRat p (a^m-b^n) : ℝ) ≤ 147 * (_root_.AbcTwoNinths.Basic.unboundedD p m n A B ^ 2 * (A*B))) :
    _root_.AbcTwoNinths.Basic.TwoLogUnbounded 147 := by
  intro p a b m n η₁ η₂ hp ho ha hb hi hm hn h₁ h₂
  let ell := log (p : ℝ)
  let A := η₁ / ell
  let B := η₂ / ell
  have he : 0 < ell := log_pos (by exact_mod_cast hp.one_lt)
  have hη₁ := (le_max_right (_root_.AbcTwoNinths.Basic.padicRationalHeight a) ell).trans h₁
  have hη₂ := (le_max_right (_root_.AbcTwoNinths.Basic.padicRationalHeight b) ell).trans h₂
  have hA : 1 ≤ A := (le_div_iff₀ he).mpr (by simpa using hη₁)
  have hB : 1 ≤ B := (le_div_iff₀ he).mpr (by simpa using hη₂)
  have hAe : A * ell = η₁ := div_mul_cancel₀ _ he.ne'
  have hBe : B * ell = η₂ := div_mul_cancel₀ _ he.ne'
  have hU : (m : ℝ)/B + (n : ℝ)/A = ell * ((m : ℝ)/η₂ + (n : ℝ)/η₁) := by
    have hp₁ := (he.trans_le hη₁).ne'
    have hp₂ := (he.trans_le hη₂).ne'
    dsimp [A, B]
    field_simp
  have hD : _root_.AbcTwoNinths.Basic.unboundedD p m n A B =
      max 4 (log (exp 2 * ell * ((m : ℝ)/η₂ + (n : ℝ)/η₁)) / ell) := by
    have hUp : 0 < ell * ((m : ℝ)/η₂ + (n : ℝ)/η₁) := by
      have := he.trans_le hη₁
      have := he.trans_le hη₂
      positivity
    unfold _root_.AbcTwoNinths.Basic.unboundedD
    change max 4 ((2 + log ((m : ℝ)/B + (n : ℝ)/A)) / ell) = _
    rw [hU, mul_assoc, log_mul (exp_ne_zero _) hUp.ne', log_exp]
  have hv := provider p m n a b A B hp ho ha hb hi hm hn hA hB
    (by rw [show log (p : ℝ) = ell from rfl, hAe]; exact (le_max_left _ _).trans h₁)
    (by rw [show log (p : ℝ) = ell from rfl, hBe]; exact (le_max_left _ _).trans h₂)
  have hv' := mul_le_mul_of_nonneg_right hv (sq_nonneg ell)
  change _ * ell^2 ≤ _
  rw [← hD]
  convert hv' using 1
  rw [← hAe, ← hBe]
  ring

end

end AbcTwoNinths.Basic
