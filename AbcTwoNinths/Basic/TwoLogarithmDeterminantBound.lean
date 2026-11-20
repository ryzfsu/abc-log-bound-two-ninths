/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Two Logarithm Determinant Bound

The module compares local depth with the height of a selected grid minor to exclude the high-depth case.

## Main results
* `AbcTwoNinths.Basic.depthBoundOfGridAndMinor`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

/--
The strict determinant inequality contradicts the prescribed ranges of the two rectangle parameters.
-/
theorem highBranchImpossible
    (D A ell U L J N M C : ℝ)
    (hD : 4 ≤ D) (hA : 1 ≤ A) (hell : 1 ≤ ell)
    (hU : 0 < U) (hM : 0 < M)
    (hlog : log (exp 2 * U) / ell ≤ D)
    (hLl : 4 * D ≤ L) (hLu : L ≤ (17 / 4 : ℝ) * D)
    (hJl : 32 * D * A ≤ J) (hJu : J ≤ 33 * D * A)
    (hN : N = (J + 1) * L)
    (hMu : M ≤ (1 + sqrt J) * sqrt (L * A) * U)
    (hCu : C ≤ (1 + sqrt J) * sqrt (L * A))
    (hdet : (J + 1) * (L - 1) <
      2 * log N / ell + J * (log (exp 2 * M / J) / ell) + L * C) :
    False := by
  have hDp : 0 < D := by linarith
  have hAp : 0 < A := by linarith
  have hLp : 0 < L := by linarith
  have hDA : 4 ≤ D * A := calc
    4 ≤ D := hD
    _ = D * 1 := (mul_one _).symm
    _ ≤ D * A := mul_le_mul_of_nonneg_left hA hDp.le
  have hJp : 0 < J := by linarith
  have hellp : 0 < ell := by linarith
  have hX : 16 ≤ D ^ 2 * A := by
    calc
      16 ≤ D * (D * A) := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hDA)]
      _ = _ := by ring
  have hNpos : 0 < N := by rw [hN]; positivity
  have hNbound : N ≤ 145 * (D ^ 2 * A) := by
    have hp : (J + 1) * L ≤ (34 * (D * A)) * ((17 / 4 : ℝ) * D) :=
      mul_le_mul (by linarith) hLu hLp.le (by positivity)
    rw [hN]
    nlinarith
  have h145 : log (145 : ℝ) ≤ 8 := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 145)
      (by norm_num : (145 : ℝ) ≤ 2 ^ (8 : ℕ))
    rw [log_pow] at hl
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl h2
    linarith
  have hfirst : 2 * log N / ell ≤ 4 * (D ^ 2 * A) := by
    have hn := log_le_log hNpos hNbound
    have hx := log_le_sub_one_of_pos (by positivity : 0 < D ^ 2 * A)
    rw [log_mul (by norm_num : (145 : ℝ) ≠ 0) (by positivity : D ^ 2 * A ≠ 0)] at hn
    apply (div_le_iff₀ hellp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hell) (show 0 ≤ D ^ 2 * A by positivity)]
  have hSJ := sq_sqrt hJp.le
  have hSL := sq_sqrt (show 0 ≤ L * A by positivity)
  have hSN : 0 ≤ sqrt J := sqrt_nonneg _
  have hLN : 0 ≤ sqrt (L * A) := sqrt_nonneg _
  have hsmallJ : 11 ≤ sqrt J := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 11 + sqrt J by positivity)]
  have hprod : J * (L * A) ≤ (33 * D * A) * ((17 / 4 : ℝ) * D * A) :=
    mul_le_mul hJu (mul_le_mul_of_nonneg_right hLu hAp.le) (by positivity) (by positivity)
  have hsq : (sqrt J * sqrt (L * A)) ^ 2 = J * (L * A) := by rw [mul_pow, hSJ, hSL]
  have hroot : sqrt J * sqrt (L * A) ≤ (237 / 20 : ℝ) * (D * A) := by
    by_contra! h
    have hpos : 0 < sqrt J * sqrt (L * A) + (237 / 20 : ℝ) * (D * A) := by positivity
    nlinarith [mul_pos (sub_pos.mpr h) hpos, sq_nonneg (D * A)]
  have hB : (1 + sqrt J) * sqrt (L * A) ≤ (1293 / 100 : ℝ) * (D * A) := by
    have hp := mul_le_mul_of_nonneg_right hsmallJ hLN
    linarith
  have hMJ : M / J ≤ U := by
    apply (div_le_iff₀ hJp).2
    refine hMu.trans ?_
    rw [mul_comm U J]
    have hb : (1 + sqrt J) * sqrt (L * A) ≤ J := by linarith
    exact mul_le_mul_of_nonneg_right hb hU.le
  have hsecond : J * (log (exp 2 * M / J) / ell) ≤ 33 * (D ^ 2 * A) := by
    have harg : exp 2 * M / J ≤ exp 2 * U := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hMJ (exp_pos _).le
    have hl := log_le_log (by positivity : 0 < exp 2 * M / J) harg
    have hv := (div_le_div_of_nonneg_right hl hellp.le).trans hlog
    calc
      _ ≤ J * D := mul_le_mul_of_nonneg_left hv hJp.le
      _ ≤ (33 * D * A) * D := mul_le_mul_of_nonneg_right hJu hDp.le
      _ = _ := by ring
  have hthird : L * C ≤ 55 * (D ^ 2 * A) := by
    calc
      _ ≤ L * ((1293 / 100 : ℝ) * (D * A)) :=
        mul_le_mul_of_nonneg_left (hCu.trans hB) hLp.le
      _ ≤ ((17 / 4 : ℝ) * D) * ((1293 / 100 : ℝ) * (D * A)) :=
        mul_le_mul_of_nonneg_right hLu (by positivity)
      _ ≤ _ := by nlinarith
  have hleft : 120 * (D ^ 2 * A) ≤ (J + 1) * (L - 1) := by
    have hb : (15 / 4 : ℝ) * D ≤ L - 1 := by linarith
    calc
      _ = (32 * D * A) * ((15 / 4 : ℝ) * D) := by ring
      _ ≤ _ := mul_le_mul (by linarith) hb (by positivity) (by linarith)
  nlinarith

/--
The grid alternatives and the valuation correction give the upper bound of 147 times the squared scale times the height parameter.
-/
theorem depthBoundOfGridAndMinor
    (D A ell U L J N m0 u : ℝ)
    (hD : 4 ≤ D) (hA : 1 ≤ A) (hell : 1 ≤ ell)
    (hU : 0 < U) (hlog : log (exp 2 * U) / ell ≤ D)
    (hLl : 4 * D ≤ L) (hLu : L ≤ (17 / 4 : ℝ) * D)
    (hJl : 32 * D * A ≤ J) (hJu : J ≤ 33 * D * A)
    (hN : N = (J + 1) * L)
    (hu : u ≤ 2 * (D ^ 2 * A))
    (hgrid : m0 < 1 + 2 * sqrt (J * L * A) ∨
      (N ≤ m0 → ∃ M C : ℝ, 0 < M ∧
        M ≤ (1 + sqrt J) * sqrt (L * A) * U ∧
        C ≤ (1 + sqrt J) * sqrt (L * A) ∧
        (J + 1) * (L - 1) <
          2 * log N / ell + J * (log (exp 2 * M / J) / ell) + L * C)) :
    m0 + u ≤ 147 * (D ^ 2 * A) := by
  have hDp : 0 < D := by linarith
  have hAp : 0 < A := by linarith
  have hDA : 4 ≤ D * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hDp.le]
  have hX : 16 ≤ D ^ 2 * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hDA)]
  have hLp : 0 < L := by linarith
  have hJp : 0 < J := by linarith
  have hNbound : N ≤ 145 * (D ^ 2 * A) := by
    have hp : (J + 1) * L ≤ (34 * (D * A)) * ((17 / 4 : ℝ) * D) :=
      mul_le_mul (by linarith) hLu hLp.le (by positivity)
    rw [hN]
    nlinarith
  rcases hgrid with hcoll | hminor
  · have hp : (J * L) * A ≤ ((33 * D * A) * ((17 / 4 : ℝ) * D)) * A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hJu hLu hLp.le (by positivity)) hAp.le
    have hsq := sq_sqrt (show 0 ≤ J * L * A by positivity)
    have hs : sqrt (J * L * A) ≤ 12 * (D * A) := by
      by_contra! h
      have hpos : 0 < sqrt (J * L * A) + 12 * (D * A) := by positivity
      nlinarith [mul_pos (sub_pos.mpr h) hpos, sq_nonneg (D * A)]
    have hDAle : D * A ≤ D ^ 2 * A := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ D by linarith))
        (show 0 ≤ D * A by positivity)]
    linarith
  · have hlt : m0 < N := by
      by_contra! h
      obtain ⟨M, C, hMp, hM, hC, hdet⟩ := hminor h
      exact _root_.AbcTwoNinths.Basic.highBranchImpossible D A ell U L J N M C hD hA hell hU hMp hlog
        hLl hLu hJl hJu hN hM hC hdet
    linarith

end

end AbcTwoNinths.Basic
