/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Determinant Log Bound

The module bounds the logarithmic contributions of factorials and interpolation rows.

## Main results
* `AbcTwoNinths.Basic.archBridge`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

open scoped BigOperators

section

open Real

/-- Bounds the factorial of a natural number by its own power. -/
theorem factorialUpper (N : ℕ) : N.factorial ≤ N^N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left _ (ih.trans (Nat.pow_le_pow_left (by omega) _))

/-- For (N>1), the factorial of (N) is strictly less than (N^N). -/
theorem factorialUpperStrict (N : ℕ) (hN : 1 < N) : N.factorial < N^N := by
  cases N with
  | zero => omega
  | succ n =>
    rw [Nat.factorial_succ, pow_succ']
    apply Nat.mul_lt_mul_of_pos_left _ (by omega)
    apply (_root_.AbcTwoNinths.Basic.factorialUpper n).trans_lt
    exact Nat.pow_lt_pow_left (by omega) (by omega)

/-- For positive real `J`, the logarithm of `k!` is at least `k * log J - J`. -/
theorem logFactorial (J : ℝ) (hJ : 0 < J) (k : ℕ) :
    (k : ℝ)*log J - J ≤ log (k.factorial : ℝ) := by
  have hp : 0 < J^k / (k.factorial : ℝ) := by positivity
  have h := log_le_log hp (pow_div_factorial_le_exp J hJ.le k)
  rw [log_div (pow_ne_zero _ hJ.ne') (by positivity), log_pow, log_exp] at h
  linarith

/-- Twice the sum of the real row indices from zero through `J` equals `(J + 1) * J`. -/
theorem determinantLogBoundRowSum (J : ℕ) :
    2 * (∑ i : Fin (J+1), (i.val : ℝ)) = ((J : ℝ)+1)*J := by
  have hn : (∑ i ∈ Finset.range (J+1), i) * 2 = (J+1)*J := by
    simpa using Finset.sum_range_id_mul_two (J+1)
  have hc := congrArg (fun a : ℕ => (a : ℝ)) hn
  push_cast at hc
  rw [Fin.sum_univ_eq_sum_range]
  linarith

/-- Sums the logarithmic factorial lower bounds over all rows from zero through `J`. -/
theorem factorialRowLower (J : ℕ) (hJ : 0 < J) :
    (∑ i : Fin (J+1), (i.val : ℝ)) * log J - ((J : ℝ)+1)*J ≤
      ∑ i : Fin (J+1), log (i.val.factorial : ℝ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (J+1))))
    (fun i _ => _root_.AbcTwoNinths.Basic.logFactorial (J : ℝ) (by exact_mod_cast hJ) i.val)
  simpa [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const] using h

/--
Converts the factorial height and divisibility estimates for a rectangular interpolation minor into a strict logarithmic inequality.
-/
theorem archBridge (J L E : ℕ) (p M W Z : ℝ) (hJ : 0 < J) (hL : 0 < L)
    (hp : 1 < p) (hM : 0 < M)
    (hE : 2*(E : ℝ) = (((J+1)*L : ℕ) : ℝ)*(J+1)*((L : ℝ)-1))
    (hZ : Z ≤ (((J+1)*L : ℕ) : ℝ)*L/2*W*log p)
    (hlog : (E : ℝ)*log p ≤ log ((((J+1)*L).factorial : ℕ) : ℝ) +
      (L : ℝ)*(∑ i : Fin (J+1), ((i.val : ℝ)*log M-log (i.val.factorial : ℝ))) + Z) :
    ((J : ℝ)+1)*((L : ℝ)-1) <
      2*log (((J+1)*L : ℕ) : ℝ)/log p +
      (J : ℝ)*(2+log (M/J))/log p + L*W := by
  let N := (J+1)*L
  let X := (∑ i : Fin (J+1), (i.val : ℝ))
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by dsimp [N]; positivity)
  have hlp := log_pos hp
  have hJ0 : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hF : 0 < (N.factorial : ℝ) := by positivity
  have hN1 : 1 < N := by
    dsimp [N]
    nlinarith [Nat.mul_le_mul_left (J+1) (show 1 ≤ L by omega)]
  have hf := log_lt_log hF (show (N.factorial : ℝ) < (N : ℝ)^N by
    exact_mod_cast _root_.AbcTwoNinths.Basic.factorialUpperStrict N hN1)
  rw [log_pow] at hf
  have hg := _root_.AbcTwoNinths.Basic.factorialRowLower J hJ
  change X * log J - _ ≤ _ at hg
  have hs := _root_.AbcTwoNinths.Basic.determinantLogBoundRowSum J
  change 2*X = _ at hs
  change 2*(E : ℝ) = (N : ℝ)*(J+1)*((L : ℝ)-1) at hE
  change Z ≤ (N : ℝ)*L/2*W*log p at hZ
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hlog
  change (E : ℝ)*log p ≤ log (N.factorial : ℝ) +
    (L : ℝ)*(X*log M - ∑ i : Fin (J+1), log (i.val.factorial : ℝ)) + Z at hlog
  have hLg := mul_le_mul_of_nonneg_left hg (show 0 ≤ (L : ℝ) by positivity)
  have hh : (E : ℝ)*log p < (N : ℝ)*log N +
      (L : ℝ)*(X*(log M-log J)+((J : ℝ)+1)*J) + Z := by linarith
  have hh' := congrArg (fun x : ℝ => x*log p) hE
  have hs' := congrArg (fun x : ℝ => x*(L : ℝ)*(log M-log J)) hs
  have hNe : (N : ℝ) = ((J : ℝ)+1)*L := by simp [N]
  rw [log_div hM.ne' hJ0.ne', ← add_div]
  have hk : ((J : ℝ)+1)*((L : ℝ)-1)*log p <
      2*log (N : ℝ)+(J : ℝ)*(2+(log M-log J))+(L : ℝ)*W*log p := by
    have hk' : 0 < (N : ℝ) *
        (2*log (N : ℝ)+(J : ℝ)*(2+(log M-log J))+(L : ℝ)*W*log p -
          ((J : ℝ)+1)*((L : ℝ)-1)*log p) := by
      rw [hNe] at hh hh' hZ ⊢
      nlinarith only [hh, hh', hZ, hs']
    linarith [pos_of_mul_pos_right hk' hN.le]
  change _ < (2*log (N : ℝ)+_)/log p + _
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ hlp]
  nlinarith

/--
Specializes the interpolation-minor logarithmic bound to height 36 and exponent `630 * (J + 1)^2`.
-/
theorem archBridge36 (J : ℕ) (p M W Z : ℝ) (hJ : 0 < J)
    (hp : 1 < p) (hM : 0 < M)
    (hZ : Z ≤ ((J : ℝ)+1)*324*(2*W*log p))
    (hlog : ((630*(J+1)^2 : ℕ) : ℝ)*log p ≤
      log ((((J+1)*36).factorial : ℕ) : ℝ) +
      36*(∑ i : Fin (J+1), ((i.val : ℝ)*log M-log (i.val.factorial : ℝ))) + Z) :
    ((J : ℝ)+1)*35 <
      2*log (((J+1)*36 : ℕ) : ℝ)/log p +
      (J : ℝ)*(2+log (M/J))/log p + 36*W := by
  have h := _root_.AbcTwoNinths.Basic.archBridge J 36 (630*(J+1)^2) p M W Z hJ (by decide) hp hM
  have he : 2*((630*(J+1)^2 : ℕ) : ℝ) =
      (((J+1)*36 : ℕ) : ℝ)*(J+1)*((36 : ℝ)-1) := by push_cast; ring
  have hz : Z ≤ (((J+1)*36 : ℕ) : ℝ)*36/2*W*log p := by
    convert hZ using 1
    push_cast
    ring
  have hc := h he hz hlog
  norm_num at hc ⊢
  exact hc

end

end AbcTwoNinths.Basic
