/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.OrientedBasis

/-!
# Signs of a Small Two-Logarithm Form

The slab and separation bounds force the coefficients of a sufficiently small positive
two-logarithm form to have opposite signs. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.oppositeContactSigns`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The product and separation bounds imply that the first length is at most the allotted fraction of the height.
-/
theorem sameSignLengthPaid {H θ u ell t L K ε S : ℝ}
    (hH : 0 < H) (hu : 48 ≤ u) (ht : 0 < t)
    (hL : 0 < L) (hK : 1 / 2 ≤ K)
    (hell : u / 2 ≤ ell) (he : 0 < ε) (hell_eq : ell = -Real.log ε)
    (hprod : L * K ≤ 5 * H * t)
    (hsep : Real.exp (-K) ≤ S) (hslab : S ≤ 7 * K * ε / t)
    (hlarge : 320000 * 2048 * t ≤ θ * u)
    (htiny : t < Real.exp (-ell / 2) → 10 * t ≤ θ) :
    L ≤ θ * H := by
  by_cases hcase : t < Real.exp (-ell / 2)
  · have h := mul_le_mul_of_nonneg_left (htiny hcase) hH.le
    nlinarith [mul_le_mul_of_nonneg_left hK hL.le]
  · have hlogt : -ell / 2 ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht).mpr (le_of_not_gt hcase)
    have h7 : Real.log 7 ≤ 2 := by
      apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 7)).mpr
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have hkpos : 0 < K := by linarith
    have hlog := Real.log_le_log (Real.exp_pos (-K)) (hsep.trans hslab)
    rw [Real.log_exp, Real.log_div (by positivity) ht.ne',
      Real.log_mul (by positivity) he.ne', Real.log_mul (by norm_num) hkpos.ne'] at hlog
    have hk : u / 16 ≤ K := by
      linarith [Real.log_le_sub_one_of_pos hkpos]
    have hprod' := (mul_le_mul_of_nonneg_left hk hL.le).trans hprod
    have hscale : 80 * t ≤ θ * u := by linarith
    have := mul_le_mul_of_nonneg_left hscale hH.le
    have h' : L * u ≤ (θ * H) * u := by nlinarith
    exact le_of_mul_le_mul_right h' (by linarith)

/--
A positive integer combination with nonnegative coefficients and positive summands is at least one of its summands.
-/
theorem nonnegativeCoeffContact {c d : ℤ} {s₁ s₂ Λ : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hΛ : 0 < Λ)
    (he : Λ = (c : ℝ) * s₁ + (d : ℝ) * s₂) :
    s₁ ≤ Λ ∨ s₂ ≤ Λ := by
  have hcR : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hp : 0 < c
  · have hpR : (1 : ℝ) ≤ c := by exact_mod_cast hp
    left
    nlinarith [mul_nonneg hdR hs₂.le, mul_le_mul_of_nonneg_right hpR hs₁.le]
  · have hcz : c = 0 := by omega
    have hdp : (1 : ℝ) ≤ d := by
      have h : 0 < d := by
        by_contra! hn
        have hdz : d = 0 := by omega
        simp [hcz, hdz] at he
        linarith
      exact_mod_cast h
    right
    simp [hcz] at he
    nlinarith [mul_le_mul_of_nonneg_right hdp hs₂.le]

/--
A sufficiently small positive linear form in two logarithms must have coefficients of
strictly opposite signs under the separation and slab bounds.
-/
theorem oppositeContactSigns {H θ u ell t L K ε S R Λ : ℝ} {c d : ℤ}
    (hH : 0 < H) (hu : 48 ≤ u) (ht : 0 < t)
    (hL : 1 / 2 ≤ L) (hK : 1 / 2 ≤ K)
    (hell : u / 2 ≤ ell) (he : 0 < ε) (hell_eq : ell = -Real.log ε)
    (hprod : L * K ≤ 5 * H * t)
    (hS : Real.exp (-L) ≤ S) (hR : Real.exp (-K) ≤ R)
    (hSs : S ≤ 7 * L * ε / t) (hRs : R ≤ 7 * K * ε / t)
    (hlarge : 320000 * 2048 * t ≤ θ * u)
    (htiny : t < Real.exp (-ell / 2) → 10 * t ≤ θ)
    (hΛ : 0 < Λ) (hΛsmall : Λ < Real.exp (-(θ * H)))
    (hform : Λ = (c : ℝ) * S + (d : ℝ) * R) :
    (c < 0 ∧ 0 < d) ∨ (d < 0 ∧ 0 < c) := by
  have hSp := (Real.exp_pos _).trans_le hS
  have hRp := (Real.exp_pos _).trans_le hR
  by_contra hn
  by_cases hnon : 0 ≤ c ∧ 0 ≤ d
  · rcases _root_.AbcTwoNinths.ExteriorE1.nonnegativeCoeffContact hnon.1 hnon.2 hSp hRp hΛ hform with h | h
    · have hpay := _root_.AbcTwoNinths.ExteriorE1.sameSignLengthPaid hH hu ht (by linarith : 0 < L) hK
        hell he hell_eq hprod hR hRs hlarge htiny
      exact (not_lt_of_ge ((Real.exp_le_exp.mpr (neg_le_neg hpay)).trans (hS.trans h))) hΛsmall
    · have hpay := _root_.AbcTwoNinths.ExteriorE1.sameSignLengthPaid hH hu ht (by linarith : 0 < K) hL
        hell he hell_eq (by rwa [mul_comm K L]) hS hSs hlarge htiny
      exact (not_lt_of_ge ((Real.exp_le_exp.mpr (neg_le_neg hpay)).trans (hR.trans h))) hΛsmall
  · have hc : c ≤ 0 := by omega
    have hd : d ≤ 0 := by omega
    have hcR : (c : ℝ) ≤ 0 := by exact_mod_cast hc
    have hdR : (d : ℝ) ≤ 0 := by exact_mod_cast hd
    rw [hform] at hΛ
    linarith [mul_nonpos_of_nonpos_of_nonneg hcR hSp.le,
      mul_nonpos_of_nonpos_of_nonneg hdR hRp.le]

end

end AbcTwoNinths.ExteriorE1
