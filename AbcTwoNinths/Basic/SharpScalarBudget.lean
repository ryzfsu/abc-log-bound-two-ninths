/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Sharp Scalar Budget

The module bounds the logarithmic factorial and other overhead terms beyond the sharpened numerical onset.

## Main results
* `AbcTwoNinths.Basic.sharpOverhead`
* `AbcTwoNinths.Basic.sharpBudgetOnset`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

private theorem factorialLogLeSq (k : ℕ) :
    Real.log (k.factorial : ℝ) ≤ (k : ℝ)^2 := by
  cases k with
  | zero => simp
  | succ k =>
    have h : (((k+1).factorial : ℕ) : ℝ) ≤ ((k+1 : ℕ) : ℝ)^(k+1) := by
      exact_mod_cast Nat.factorial_le_pow (k+1)
    have hh := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at hh
    have hp : 0 < (((k+1 : ℕ) : ℝ)) := by positivity
    have hl : Real.log ((k+1 : ℕ) : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hp]
    exact hh.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hl hp.le)

/--
The factorial and binomial contributions together are bounded by the explicit inverse-logarithmic budget.
-/
theorem sharpOverhead {K : ℕ} {n ρ S t ℓ b θ : ℝ}
    (hn : 0 < n) (hρ : 0 < ρ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hθ : θ ≤ 1) (hscale : n * ℓ = 3 * (1+θ) * ρ)
    (hrows : (2*K : ℝ) ≤ 2*n) (hS : S ≤ 2*ρ) (hSpos : 0 ≤ S)
    (ht : b*ℓ ≤ t) :
    Real.log ((2*K).factorial : ℝ) + (2*K : ℝ)*((S/t+K)*Real.log 2) ≤
      (36 + 4/b)/ℓ * (n*ρ) := by
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have ht' : 0 < t := (mul_pos hb hℓ).trans_le ht
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hf := factorialLogLeSq (2*K)
  push_cast at hf
  have hsquare : (2*K : ℝ)^2 ≤ (2*n)^2 :=
    pow_le_pow_left₀ (by positivity) hrows 2
  have hscale' : n * ℓ ≤ 6*ρ := by nlinarith [mul_nonneg (sub_nonneg.mpr hθ) hρ.le]
  have hdiv : S/t ≤ 2*ρ/(b*ℓ) := div_le_div₀ (by positivity) hS (by positivity) ht
  have hprod : (2*K : ℝ) * ((S/t+K)*Real.log 2) ≤ 2*n*(2*ρ/(b*ℓ)+n) := by
    have hbest : (S/t+K)*Real.log 2 ≤ 2*ρ/(b*ℓ)+n := by
      have hh : (S/t+K)*Real.log 2 ≤ (S/t+K)*1 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith
    apply (mul_le_mul_of_nonneg_left hbest (by positivity)).trans
    exact mul_le_mul_of_nonneg_right hrows (by positivity)
  apply (add_le_add (hf.trans hsquare) hprod).trans
  have h6 : 6*n^2*ℓ ≤ 36*n*ρ := by
    nlinarith [mul_le_mul_of_nonneg_left hscale' hn.le]
  have hbound : 6*n^2 ≤ 36*n*ρ/ℓ := (le_div_iff₀ hℓ).2 h6
  calc
    (2*n)^2+2*n*(2*ρ/(b*ℓ)+n) = 6*n^2 + 4*n*ρ/(b*ℓ) := by ring
    _ ≤ 36*n*ρ/ℓ + 4*n*ρ/(b*ℓ) := by gcongr
    _ = (36+4/b)/ℓ*(n*ρ) := by field_simp

/--
A strict gap in the leading coefficient gives a common threshold for the rounded determinant budget.
-/
theorem sharpBudgetOnset {F f θ b : ℝ} (hf : 0 < f) (hf' : f ≤ 1)
    (hθ : 0 < θ) (hθ' : θ ≤ 1) (hb : 0 < b)
    (hgap : F < (2/3 : ℝ)*(1+θ)*f^2) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ {n ρ S t ℓ : ℝ} {K : ℕ},
      X ≤ n → X ≤ ℓ → 0 < ρ → n*ℓ = 3*(1+θ)*ρ →
      (2*K : ℝ) ≤ 2*n → n*f-1 ≤ (2*K : ℝ) →
      S ≤ 2*ρ → 0 ≤ S → b*ℓ ≤ t →
      F*(n*ρ) + Real.log ((2*K).factorial : ℝ) +
        (2*K : ℝ)*((S/t+K)*Real.log 2) < (2/9 : ℝ)*(2*K : ℝ)^2*ℓ := by
  let c := (2/3 : ℝ)*(1+θ)
  let A := 36+4/b
  let gap := c*f^2-F
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hg : 0 < gap := sub_pos.mpr hgap
  let X := max 1 (max (4*c/gap) (4*A/gap))
  refine ⟨X, le_max_left _ _, ?_⟩
  intro n ρ S t ℓ K hnX hℓX hρ hscale hrows hround hS hSp ht
  have hn1 := (le_max_left 1 (max (4*c/gap) (4*A/gap))).trans hnX
  have hℓ1 := (le_max_left 1 (max (4*c/gap) (4*A/gap))).trans hℓX
  have hn : 0 < n := by linarith
  have hℓ : 0 < ℓ := by linarith
  have hnLarge := (le_max_left (4*c/gap) (4*A/gap)).trans ((le_max_right _ _).trans hnX)
  have hℓLarge := (le_max_right (4*c/gap) (4*A/gap)).trans ((le_max_right _ _).trans hℓX)
  have hcn := (div_le_iff₀ hg).mp hnLarge
  have hal := (div_le_iff₀ hg).mp hℓLarge
  have hcost : A/ℓ ≤ gap/4 := (div_le_iff₀ hℓ).2 (by nlinarith)
  let k := (2*K : ℝ)
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk1 : n*f ≤ k+1 := by dsimp [k]; linarith
  have hksq : (n*f)^2 - 2*n*f ≤ k^2 := by
    by_cases h : n*f ≤ k
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ k+n*f by positivity),
        mul_pos hn hf]
    · have h' : 0 ≤ n*f-k := by linarith
      have hp := mul_le_mul_of_nonneg_right (show n*f-k ≤ 1 by linarith)
        (show 0 ≤ n*f+k by positivity)
      nlinarith
  have herr : 2*c*n*f ≤ (gap/2)*n^2 := by
    have hsmall : 2*c*f ≤ 2*c := by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hf')]
    nlinarith [mul_le_mul_of_nonneg_right (show 2*c*f ≤ gap*n/2 by linarith) hn.le]
  have hcore : (F+gap/4)*n^2 < c*k^2 := by
    have gain : 0 < gap*n^2 := mul_pos hg (sq_pos_of_pos hn)
    have hsq := mul_le_mul_of_nonneg_left hksq hc.le
    have hEq : F + gap = c*f^2 := by dsimp [gap]; ring
    nlinarith [congrArg (fun z : ℝ => z*n^2) hEq]
  have hmain := mul_lt_mul_of_pos_right hcore hρ
  have hid : c*k^2*ρ = ((2/9 : ℝ)*k^2*ℓ)*n := by
    dsimp [c]
    linear_combination -(2/9)*k^2*hscale
  have hmain' : (F+gap/4)*(n*ρ) < (2/9 : ℝ)*k^2*ℓ := by
    apply (mul_lt_mul_iff_left₀ hn).1
    calc
      (F+gap/4)*(n*ρ)*n = ((F+gap/4)*n^2)*ρ := by ring
      _ < _ := hmain
      _ = _ := hid
  have ho := _root_.AbcTwoNinths.Basic.sharpOverhead hn hρ hℓ hb hθ' hscale hrows hS hSp ht
  have ho' : Real.log ((2*K).factorial : ℝ) + (2*K : ℝ)*((S/t+K)*Real.log 2) ≤
      (gap/4)*(n*ρ) := ho.trans (mul_le_mul_of_nonneg_right hcost (by positivity))
  linarith

end

end AbcTwoNinths.Basic
