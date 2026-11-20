/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationMoments

/-!
# Exponential Sum Derivatives

The module computes repeated derivatives of the interpolation exponential sum, including at the origin. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.taylorExponentialSumIteratedDerivAtZero`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- Differentiating the exponential sum raises its order by one. -/
theorem taylorExponentialSumHasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ) (t : ℝ) :
    HasDerivAt (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d m) (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d (m+1) t) t := by
  let w (σ : Equiv.Perm ι) : ℝ := ∑ i ∈ s, (l i * γ) * u (σ.symm i)
  let c (σ : Equiv.Perm ι) : ℝ := Equiv.Perm.sign σ •
    ∏ j : ι, if σ j ∈ s then u j ^ d (σ j) else
      u j ^ d (σ j) * Real.exp (l (σ j) * γ * u j) *
        (Real.exp (l (σ j) * ε j) - 1)
  have h (σ : Equiv.Perm ι) :
      HasDerivAt (fun x => (c σ * w σ ^ m) * Real.exp (w σ * x))
        ((c σ * w σ ^ (m+1)) * Real.exp (w σ * t)) t := by
    have hlin : HasDerivAt (fun x : ℝ => w σ * x) (w σ) t := by
      have hi : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
      simpa only [mul_one] using hi.const_mul (w σ)
    convert (hlin.exp.const_mul
      (c σ * w σ ^ m)) using 1
    ring
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => h σ)).const_mul _

/--
The iterated derivative of the order-zero exponential sum is the exponential sum of the corresponding order.
-/
theorem taylorExponentialSumIteratedDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ) :
    iteratedDeriv m (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d 0) = _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumHasDerivAt s u l ε γ d m t).deriv

/--
Every derivative below the row-set vanishing order vanishes at zero. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem taylorExponentialSumIteratedDerivAtZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ)
    (hm : m < s.card * (s.card - 1) / 2 - ∑ i ∈ s, d i) :
    iteratedDeriv m (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d 0) 0 = 0 := by
  rw [_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumIteratedDeriv]
  exact _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumAtZero s u l ε γ d m hm

end

end AbcTwoNinths.ExteriorE1
