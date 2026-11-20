/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.FactorialRank

/-!
# Log Rank

The module bounds the number of distinct prime factors using the logarithm of their product. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.rankLeFourWeightDivLog`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- If `W` bounds the sum of the logarithms of a finite prime set and `m` is one more
than its cardinality, then `m * (Real.log m - 1) ≤ W`. -/
theorem factorialLogBound (S : Finset ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p) (W : ℝ)
    (hW : (∑ p ∈ S, Real.log (p : ℝ)) ≤ W) :
    let m : ℝ := S.card + 1
    m * (Real.log m - 1) ≤ W := by
  let n := S.card + 1
  let m : ℝ := (n : ℝ)
  have hn : 0 < n := by dsimp [n]; omega
  have hm : 0 < m := Nat.cast_pos.mpr hn
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfac := _root_.AbcTwoNinths.ExteriorE1.factorialLeProductOfPrimes S hp
  have hfacR : (n.factorial : ℝ) ≤ ∏ p ∈ S, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr hfac
  have hlog := Real.log_le_log hf hfacR
  rw [Real.log_prod (fun p hp' => by exact_mod_cast (hp p hp').ne_zero)] at hlog
  have hpow := Real.pow_div_factorial_le_exp m hm.le n
  have hlog' := Real.log_le_log (div_pos (pow_pos hm n) hf) hpow
  rw [Real.log_div (pow_pos hm n).ne' hf.ne', Real.log_pow, Real.log_exp] at hlog'
  have hcast : (n : ℝ) = m := rfl
  rw [hcast] at hlog'
  have hm' : m = (S.card : ℝ) + 1 := by simp [m, n]
  dsimp only
  rw [← hm']
  linarith

/--
A finite set of primes whose total logarithmic weight is at most `W` contains at most
`4 * W / Real.log W` primes when `W ≥ exp 4`.
-/
theorem rankLeFourWeightDivLog (S : Finset ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p) (W : ℝ) (hW : Real.exp 4 ≤ W)
    (hs : (∑ p ∈ S, Real.log (p : ℝ)) ≤ W) :
    (S.card : ℝ) ≤ 4 * W / Real.log W := by
  have hWp : 0 < W := (Real.exp_pos _).trans_le hW
  have hlW : 4 ≤ Real.log W := by
    simpa using Real.log_le_log (Real.exp_pos 4) hW
  let m : ℝ := S.card + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hfac : m * (Real.log m - 1) ≤ W := _root_.AbcTwoNinths.ExteriorE1.factorialLogBound S hp W hs
  by_contra! h
  have hL : 0 < Real.log W := by linarith
  have hlt : 4 * W / Real.log W < m := by dsimp [m]; linarith
  have hlog := Real.log_lt_log (show 0 < 4 * W / Real.log W by positivity) hlt
  rw [Real.log_div (by positivity) hL.ne', Real.log_mul (by norm_num) hWp.ne'] at hlog
  have h4 : 1 < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  have hd := Real.log_le_sub_one_of_pos (show 0 < Real.log W / 2 by positivity)
  rw [Real.log_div hL.ne' (by norm_num)] at hd
  have h2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hlarge : Real.log W / 2 < Real.log m - 1 := by linarith
  have htwice := (div_lt_iff₀ hL).mp hlt
  nlinarith [mul_lt_mul_of_pos_left hlarge hm]

end

end AbcTwoNinths.ExteriorE1
