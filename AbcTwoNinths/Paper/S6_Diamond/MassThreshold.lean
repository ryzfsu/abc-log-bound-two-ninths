/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeSupply
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Overlap count threshold

The module proves that the eventual overlap mass exceeds the budget for bad pairs. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.eventualBudget`
* `AbcTwoNinths.Diamond.strictBulk`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

noncomputable section

open Filter Real
open scoped Topology

section



/--
The numerical upper bound from the oriented short-plane count. This is used in Section 6 of the paper.
-/
def badBudget (x L : ℝ) : ℝ :=
  (2 * (⌊x^2 / log 2⌋₊ : ℝ) + 1) * exp (4 * ((1/log x)*x)) *
    (∑ k ∈ Finset.Icc 1 ⌊2 * x^2 / L⌋₊, (2 * k^2 : ℕ) : ℕ)

/--
The guaranteed centered ball volume from the support dimension estimate. This is used in Section 6 of the paper.
-/
def massFloor (x : ℝ) : ℝ := exp (-(7*x/log x) * log (3*log x))

private theorem polyLtExp {b : ℝ} (hb : 0 < b) (C : ℝ) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, C * x^n < exp (b*x) := by
  have h : Tendsto (fun x : ℝ => C * (x^n * exp (-b*x))) atTop (𝓝 0) := by
    have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb).const_mul C
    simpa only [rpow_natCast, mul_zero] using h₀
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
  rw [neg_mul, exp_neg, ← mul_assoc, ← div_eq_mul_inv] at hx
  simpa only [one_mul] using (div_lt_iff₀ (exp_pos (b*x))).mp hx

private theorem lossRatioZero :
    Tendsto (fun x : ℝ => (7 : ℝ) * log (3*log x)/log x) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    ((tendsto_log_atTop).const_mul_atTop (show (0 : ℝ) < 3 by norm_num))
  have h' := h.const_mul (21 : ℝ)
  have h'' : Tendsto (fun x : ℝ => 21 * (log (3 * log x) / (3 * log x))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using h'
  apply h''.congr
  intro x
  by_cases hx : log x = 0
  · simp [hx]
  · field_simp
    ring

private theorem badBudgetLe {e x L : ℝ} (he : 0 < e) (hx : 1 ≤ x)
    (hL : e*x ≤ L) (hlog : 0 < log x) (helog : 8/e ≤ log x) :
    _root_.AbcTwoNinths.Diamond.badBudget x L ≤ (80/e^3)*x^5*exp ((e/2)*x) := by
  have hxp : 0 < x := by linarith
  have hLp : 0 < L := (mul_pos he hxp).trans_le hL
  let B := ⌊2*x^2/L⌋₊
  have hB : (B : ℝ) ≤ 2*x/e := by
    apply (Nat.floor_le (show 0 ≤ 2*x^2/L by positivity)).trans
    apply (div_le_div_iff₀ hLp he).mpr
    have h := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2*x by positivity)
    nlinarith
  have hsumNat : (∑ k ∈ Finset.Icc 1 B, (2*k^2 : ℕ)) ≤ 2*B^3 := by
    calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 B, (2*B^2 : ℕ) := by
        exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Finset.mem_Icc.mp hi).2 _)
      _ = 2*B^3 := by simp [Nat.card_Icc]; ring
  have hsum : ((∑ k ∈ Finset.Icc 1 B, (2*k^2 : ℕ) : ℕ) : ℝ) ≤ 2*(2*x/e)^3 := by
    have hh : ((∑ k ∈ Finset.Icc 1 B, (2*k^2 : ℕ) : ℕ) : ℝ) ≤ 2*(B : ℝ)^3 := by exact_mod_cast hsumNat
    exact hh.trans (by gcongr)
  have hlog2 : (1/2 : ℝ) < log 2 := by linarith [log_two_gt_d9]
  have hroof : (⌊x^2 / log 2⌋₊ : ℝ) ≤ 2*x^2 := by
    apply (Nat.floor_le (show 0 ≤ x^2/log 2 by positivity)).trans
    apply (div_le_iff₀ (by linarith : 0 < log (2 : ℝ))).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 2 * log 2 - 1 by linarith)]
  have htop : 2 * (⌊x^2 / log 2⌋₊ : ℝ) + 1 ≤ 5*x^2 := by nlinarith
  have hexp : exp (4*((1/log x)*x)) ≤ exp ((e/2)*x) := by
    apply exp_le_exp.mpr
    have h := (div_le_iff₀ he).mp helog
    have hh : 4 / log x ≤ e/2 := (div_le_iff₀ hlog).mpr (by nlinarith)
    convert mul_le_mul_of_nonneg_right hh hxp.le using 1
    ring
  change (2 * (⌊x^2 / log 2⌋₊ : ℝ) + 1) * exp (4 * ((1/log x)*x)) *
    ((∑ k ∈ Finset.Icc 1 B, (2*k^2 : ℕ) : ℕ) : ℝ) ≤ _
  calc
    _ ≤ 5*x^2 * exp ((e/2)*x) * (2*(2*x/e)^3) := by gcongr
    _ = _ := by ring

/--
Every positive shell margin eventually bounds the patch loss and the bad-pair budget uniformly for log shell sizes above the margin times x. This is used in Section 6 of the paper.
-/
theorem eventualBudget {e : ℝ} (he : 0 < e) :
    ∃ X : ℝ, ∀ x ≥ X, exp 1 ≤ x ∧
      exp (-(e/2)*x) ≤ _root_.AbcTwoNinths.Diamond.massFloor x ∧
      12*x^2 < exp ((e/2)*x) ∧
      ∀ L, e*x ≤ L → _root_.AbcTwoNinths.Diamond.badBudget x L < exp (e*x)/(8*x) := by
  have hL : ∀ᶠ x : ℝ in atTop, 8/e ≤ log x :=
    tendsto_atTop.mp tendsto_log_atTop _
  have hratio := lossRatioZero.eventually (gt_mem_nhds (show (0 : ℝ) < e/2 by positivity))
  have hp := polyLtExp (b := e/2) (by positivity) (640/e^3) 6
  have h := polyLtExp (b := e/2) (by positivity) 12 2
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (exp 1), hL, hratio, hp, h] with x hx hlog hratio hp hx₂
  have hE : 1 < exp (1 : ℝ) := one_lt_exp_iff.mpr zero_lt_one
  have h₁ : 1 < x := hE.trans_le hx
  have hlogx : 0 < log x := log_pos h₁
  refine ⟨hx, ?_, hx₂, ?_⟩
  · apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hratio.le (show 0 ≤ x by linarith)
    change -(e/2)*x ≤ -(7*x/log x) * log (3*log x)
    linarith [show 7 * log (3 * log x) / log x * x = (7*x/log x) * log (3*log x) by ring]
  · intro L hLm
    apply (badBudgetLe he h₁.le hLm hlogx hlog).trans_lt
    apply (lt_div_iff₀ (show 0 < 8*x by linarith)).mpr
    have hh := mul_lt_mul_of_pos_right hp (exp_pos ((e/2)*x))
    rw [← exp_add, show (e/2)*x+(e/2)*x = e*x by ring] at hh
    convert hh using 1
    ring

/--
The manuscript's strict threshold, with no bulk or comparison premise. This is used in Section 6 of the paper.
-/
theorem strictBulk {η : ℝ} (hη : η < 1/9) :
    ∃ X : ℝ, ∀ {R p : ℕ} {H x m W : ℝ}, X ≤ x →
      0 < R → Real.log (R : ℝ) = 3*x →
      _root_.AbcTwoNinths.ExteriorE2.Admissible (p : ℝ) H η x → 1 < p → H ≤ 3*x*m →
      _root_.AbcTwoNinths.Diamond.massFloor x ≤ W →
      let M₀ := _root_.AbcTwoNinths.ExteriorE2.m (p : ℝ) H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
      let n := ((_root_.AbcTwoNinths.ExteriorE2.fresh R M₀).card : ℝ)
      let μ := ((p : ℝ)-1)/(2*m)
      _root_.AbcTwoNinths.Diamond.badBudget x (log M₀) < (n/2)*(n*W/μ-1) := by
  let e := _root_.AbcTwoNinths.ExteriorE2.margin η
  have he : 0 < e := _root_.AbcTwoNinths.ExteriorE2.marginPos hη
  obtain ⟨X, hX⟩ := _root_.AbcTwoNinths.Diamond.eventualBudget he
  refine ⟨max X (max 128 (16*(1+6/e))/e), ?_⟩
  intro R p H x m W hx hR hxR a hp hm hW
  dsimp only
  let M₀ := _root_.AbcTwoNinths.ExteriorE2.m (p : ℝ) H e x
  let L := log M₀
  let n := ((_root_.AbcTwoNinths.ExteriorE2.fresh R M₀).card : ℝ)
  let μ := ((p : ℝ)-1)/(2*m)
  change _root_.AbcTwoNinths.Diamond.badBudget x L < (n/2)*(n*W/μ-1)
  obtain ⟨_, hmass, h₂, hbad⟩ := hX x ((le_max_left _ _).trans hx)
  have hxp := a.hx
  have hHp := a.hH
  have h4x : 0 < 4*x := by positivity
  have hL : e*x ≤ L := (_root_.AbcTwoNinths.ExteriorE2.shellSlack a).1
  have hLp : 0 < L := (mul_pos he a.hx).trans_le hL
  have hLx : L ≤ x := by
    linarith [(_root_.AbcTwoNinths.ExteriorE2.shellSlack a).2, a.log_hi, mul_pos he a.hx]
  have hn : M₀/(4*x) ≤ n := by
    have hcut := (le_max_right X (max 128 (16*(1+6/e))/e)).trans hx
    exact (div_le_div_of_nonneg_left (_root_.AbcTwoNinths.ExteriorE2.MPos _ _ _ _).le (by positivity)
      (mul_le_mul_of_nonneg_left hLx (by norm_num))).trans (_root_.AbcTwoNinths.ExteriorE2.adaptiveFreshSupply hR hxR a hcut)
  have hn₀ : 0 < n := (div_pos (_root_.AbcTwoNinths.ExteriorE2.MPos _ _ _ _) h4x).trans_le hn
  have hm₀ : 0 < m := by
    by_contra! hn
    exact a.hH.not_ge (hm.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn))
  have hμ : 0 < μ := by
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp
    exact div_pos (sub_pos.mpr hp') (by positivity)
  have hμb : μ ≤ 3*(p : ℝ)*x/(2*H) := by
    change ((p : ℝ)-1)/(2*m) ≤ 3*(p : ℝ)*x/(2*H)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*(p : ℝ) by positivity), a.hH]
  have hMw : (p : ℝ)/H * exp (e*x) ≤ M₀ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
  have hMone : exp (e*x) ≤ M₀ := by
    simpa only [M₀, _root_.AbcTwoNinths.ExteriorE2.m, one_mul] using mul_le_mul_of_nonneg_right
      (le_max_left 1 ((p : ℝ)/H)) (exp_pos (e*x)).le
  have hW₁ : exp (-(e/2)*x) ≤ W := hmass.trans hW
  have hW₀ : 0 < W := (exp_pos _).trans_le hW₁
  have hprod : ((p : ℝ)/H) * exp ((e/2)*x)/(4*x) ≤ n*W := by
    calc
      _ = ((p : ℝ)/H * exp (e*x)/(4*x)) * exp (-(e/2)*x) := by
        have heq : exp (e*x) * exp (-(e/2)*x) = exp ((e/2)*x) := by
          rw [← exp_add, show e*x+ -(e/2)*x = (e/2)*x by ring]
        calc
          _ = ((p : ℝ)/H) * (exp (e*x) * exp (-(e/2)*x))/(4*x) := by rw [heq]
          _ = _ := by ring
      _ ≤ n*W := by
        exact mul_le_mul ((div_le_div_of_nonneg_right hMw (by positivity)).trans hn)
          hW₁ (exp_pos _).le hn₀.le
  have htwo : 2 < n*W/μ := by
    apply (lt_div_iff₀ hμ).mpr
    apply (mul_le_mul_of_nonneg_left hμb (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
    apply lt_of_lt_of_le _ hprod
    apply (lt_div_iff₀ (show 0 < 4*x by positivity)).mpr
    have h := mul_lt_mul_of_pos_left h₂ (div_pos a.hp a.hH)
    convert h using 1
    ring
  calc
    _root_.AbcTwoNinths.Diamond.badBudget x L < exp (e*x)/(8*x) := hbad L hL
    _ ≤ n/2 := by
      have hh := (div_le_div_of_nonneg_right hMone (show 0 ≤ 4*x by positivity)).trans hn
      calc
        _ = (exp (e*x)/(4*x))/2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hh (by norm_num)
    _ ≤ _ := by
      conv_lhs => rw [← mul_one (n/2)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end

end
end AbcTwoNinths.Diamond
