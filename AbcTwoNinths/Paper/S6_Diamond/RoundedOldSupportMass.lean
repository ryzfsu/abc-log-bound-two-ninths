/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import AbcTwoNinths.Paper.S6_Diamond.MassThreshold

/-!
# Counting and volume for the original prime support

Bounds the number of primes in the original support and obtains a lower bound on the volume of
the weighted ball. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.cardLeSixHalfMulDivLog`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

section

open Real

/--
The mass floor absorbs the rounded box denominator raised to any dimension at most (13/2)x/log x.
-/
theorem roundedMass {x : ℝ} {d : ℕ} (hx : 15 ≤ log x)
    (hd : (d : ℝ) ≤ (13/2)*x/log x) (hxp : 0 < x) :
    _root_.AbcTwoNinths.Diamond.massFloor x * ((⌊3*log x⌋₊ + 1 : ℕ) : ℝ)^d ≤ 1 := by
  let K : ℝ := ((⌊3*log x⌋₊ + 1 : ℕ) : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hT : 0 < 3*log x := by linarith
  have hKle : K ≤ 3*log x+1 := by
    dsimp [K]
    push_cast
    linarith [Nat.floor_le hT.le]
  have hlog : log K ≤ log (3*log x) + 1/(3*log x) := by
    have h := log_le_sub_one_of_pos (div_pos hK hT)
    rw [log_div hK.ne' hT.ne'] at h
    have ht := (div_le_div_iff_of_pos_right hT).mpr hKle
    rw [add_div, div_self hT.ne'] at ht
    linarith
  have hlarge : 1 ≤ log (3*log x) := by
    rw [← log_exp 1]
    apply log_le_log (exp_pos _)
    linarith [exp_one_lt_d9]
  have hc : (13/2 : ℝ)*(log (3*log x) + 1/(3*log x)) ≤ 7*log (3*log x) := by
    have hfrac : 1/(3*log x) ≤ 1/45 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  change exp (-(7*x/log x)*log (3*log x)) * K^d ≤ 1
  rw [← exp_log (pow_pos hK d), log_pow, ← exp_add, ← exp_zero]
  apply exp_le_exp.mpr
  have hb : 0 ≤ log (3*log x) + 1/(3*log x) := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have h₂ := mul_le_mul_of_nonneg_right hd hb
  have h₃ := mul_le_mul_of_nonneg_left hc (div_nonneg hxp.le (by linarith : 0 ≤ log x))
  calc
    _ ≤ -(7*x/log x)*log (3*log x) +
        ((13/2)*x/log x)*(log (3*log x) + 1/(3*log x)) := by linarith
    _ = (x/log x)*((13/2)*(log (3*log x) + 1/(3*log x)) - 7*log (3*log x)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hc)

/--
A set of positive integers with log sum at most 3x has size at most (13/2)x/log x when log x is at least 15. This is used in Section 6 of the paper.
-/
theorem cardLeSixHalfMulDivLog (F : Finset ℕ) (hF : ∀ q ∈ F, 0 < q)
    {x : ℝ} (hx : 1 < x) (h15 : 15 ≤ Real.log x) (hbudget : ∑ q ∈ F, Real.log (q : ℝ) ≤ 3*x) :
    (F.card : ℝ) ≤ (13/2)*x/Real.log x := by
  classical
  let lo := F.filter (fun q : ℕ => (q : ℝ) ≤ Real.sqrt x)
  let hi := F.filter (fun q : ℕ => ¬ (q : ℝ) ≤ Real.sqrt x)
  have hpartition : lo.card + hi.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) _
  have hlo : (lo.card : ℝ) ≤ Real.sqrt x := by
    have hcount : lo.card ≤ ⌊Real.sqrt x⌋₊ := by
      calc
        lo.card ≤ (Finset.Icc 1 ⌊Real.sqrt x⌋₊).card := Finset.card_le_card (by
          intro q hq
          obtain ⟨hqF, hq⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_Icc.mpr ⟨hF q hqF, Nat.le_floor hq⟩)
        _ = _ := by simp
    exact (show (lo.card : ℝ) ≤ ⌊Real.sqrt x⌋₊ by exact_mod_cast hcount).trans
      (Nat.floor_le (Real.sqrt_nonneg x))
  have hx0 : 0 < x := by linarith
  have hxs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hhi : (hi.card : ℝ) ≤ 6*x/Real.log x := by
    have hsumb : (∑ q ∈ hi, Real.log (q : ℝ)) ≤ ∑ q ∈ F, Real.log (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q hq _ =>
        Real.log_nonneg (by exact_mod_cast (hF q hq))
    have hh : (hi.card : ℝ) * (Real.log x / 2) ≤ ∑ q ∈ hi, Real.log (q : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro q hq
      rw [← Real.log_sqrt hx0.le]
      exact Real.log_le_log hxs (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hq).2))
    apply (le_div_iff₀ hlx).2
    linarith [hh.trans (hsumb.trans hbudget)]
  have hlog : Real.log x ≤ Real.sqrt x / 2 := by
    have h4 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 4 by positivity)
    have h8 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 8 by positivity)
    have hlog2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_div hxs.ne' (by norm_num), Real.log_sqrt hx0.le, hl4] at h4
    rw [Real.log_div hxs.ne' (by norm_num), Real.log_sqrt hx0.le, hl8] at h8
    linarith
  have hlo' : (lo.card : ℝ) ≤ (1/2)*x/Real.log x := by
    apply hlo.trans
    apply (le_div_iff₀ hlx).2
    nlinarith [mul_le_mul_of_nonneg_left hlog hxs.le, Real.sq_sqrt hx0.le]
  have hpart : (F.card : ℝ) = (lo.card : ℝ) + (hi.card : ℝ) := by exact_mod_cast hpartition.symm
  rw [hpart]
  calc
    _ ≤ (1/2)*x/Real.log x + 6*x/Real.log x := add_le_add hlo' hhi
    _ = _ := by ring


/--
The product bound on the prime support controls the rounded box denominator in the dimension obtained by erasing the roof prime.
-/
theorem roundedMassOldSupport (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) {R : ℕ} (hprod : ∏ q ∈ S, q ≤ R)
    {x : ℝ} (hx : exp 15 ≤ x) (hR : log (R : ℝ) = 3*x) :
    _root_.AbcTwoNinths.Diamond.massFloor x *
      ((⌊3*log x⌋₊ + 1 : ℕ) : ℝ)^Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex S roof) ≤ 1 := by
  have h15 : 15 ≤ log x := by simpa using log_le_log (exp_pos 15) hx
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num)).trans_le hx
  apply _root_.AbcTwoNinths.Diamond.roundedMass h15 _ (by positivity)
  simp only [_root_.AbcTwoNinths.ExteriorE2.OldIndex, Fintype.card_coe]
  apply _root_.AbcTwoNinths.Diamond.cardLeSixHalfMulDivLog _ (fun q hq => (hS q (Finset.mem_erase.mp hq).2).pos) hx1 h15
  rw [← Finset.sum_coe_sort (s := S.erase roof) (f := fun q : ℕ => log (q : ℝ))]
  exact _root_.AbcTwoNinths.ExteriorE2.oldLogBudget S roof hS hprod hR

end

end AbcTwoNinths.Diamond
