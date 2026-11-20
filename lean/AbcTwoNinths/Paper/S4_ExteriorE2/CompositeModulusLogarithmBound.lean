/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeModulusMinorBound
public import AbcTwoNinths.Basic.LocalDepthHeightComparison
public import AbcTwoNinths.Basic.InterpolationDeterminantDepth

/-!
# Composite Modulus Logarithm Bound

The module combines the composite-modulus minor depth and logarithmic height estimates. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeLog36`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators
open Real

/--
A nonzero interpolation minor of width 36 bounds the logarithmic depth of the composite congruence by factorial and rational-height terms. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeLog36 {B J c d R S : ℕ} (hB : 1 < B) (hc : c.Coprime d)
    (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (ha : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) a.val = 1)
    (hb : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) b.val = 1)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((J+1)*36)) (a.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((J+1)*36)) (b.val ^ d))
    (r s : _root_.AbcTwoNinths.Basic.Rows J 36 → ℕ) (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (hM : 0 < R*d+S*c)
    (hD : (_root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val
      (fun i => i.1.val) (fun i => i.2.val) r s c d).det ≠ 0) :
    ((630*(J+1)^2 : ℕ) : ℝ) * log B ≤ log ((((J+1)*36).factorial : ℕ) : ℝ) +
      36 * ∑ i : Fin (J+1), ((i.val : ℝ) * log ((R*d+S*c : ℕ) : ℝ) -
        log (i.val.factorial : ℝ)) +
      (((J+1 : ℕ) : ℝ) * 324) *
        ((R : ℝ) * log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ)) +
         (S : ℝ) * log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ))) := by
  classical
  have hn : Fintype.card (_root_.AbcTwoNinths.Basic.Rows J 36) = (J+1)*36 := by simp [_root_.AbcTwoNinths.Basic.Rows]
  obtain ⟨la, ua, hea, hwa⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * r j) _ (_root_.AbcTwoNinths.Basic.exactWidth36 (J+1) R r hr)
  obtain ⟨lb, ub, heb, hwb⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * s j) _ (_root_.AbcTwoNinths.Basic.exactWidth36 (J+1) S s hs)
  have hE : 630*(J+1)^2 + (∑ i : _root_.AbcTwoNinths.Basic.Rows J 36, i.1.val) ≤
      Fintype.card (_root_.AbcTwoNinths.Basic.Rows J 36) * (Fintype.card (_root_.AbcTwoNinths.Basic.Rows J 36) - 1) / 2 := by
    rw [hn, _root_.AbcTwoNinths.Basic.rowSum]
    have hf := _root_.AbcTwoNinths.Basic.depthFormula36 J
    have ht : 0 < 630 * (J+1)^2 := by positivity
    omega
  obtain ⟨Z, hZl, hZu⟩ := _root_.AbcTwoNinths.ExteriorE2.compositeActualBound (Nat.zero_lt_of_lt hB)
    (by rw [hn]; positivity) hc a b ha hb (by rw [hn]; exact hab)
    _ _ r s hE hr hs hea heb hD
  have hp : (1 : ℝ) < B := by exact_mod_cast hB
  have hz : Z ≠ 0 := by
    intro hz
    simp [hz] at hZl
    exact (not_le_of_gt (mul_pos (by positivity) (Real.log_pos hp))) hZl
  let M : ℝ := ((R*d+S*c : ℕ) : ℝ)
  let A := log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ))
  let C := log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ))
  let F (j : _root_.AbcTwoNinths.Basic.Rows J 36) := M^(j.1.val) / (j.1.val.factorial : ℝ)
  have hMp : 0 < M := by dsimp [M]; exact_mod_cast hM
  have hFp (j : _root_.AbcTwoNinths.Basic.Rows J 36) : 0 < F j :=
    div_pos (pow_pos hMp _) (by positivity)
  have hprod : 0 < ∏ j, F j := Finset.prod_pos (fun j _ => hFp j)
  have hfac : 0 < (((J+1)*36).factorial : ℝ) := by positivity
  have hZa : (0 : ℝ) < Z.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hz
  change (Z.natAbs : ℝ) ≤ ((Fintype.card (_root_.AbcTwoNinths.Basic.Rows J 36)).factorial : ℝ) *
    (∏ j, F j) * exp ((ua-la : ℕ) * A + (ub-lb : ℕ) * C) at hZu
  rw [hn] at hZu
  have hlog := log_le_log hZa hZu
  rw [log_mul (mul_ne_zero hfac.ne' hprod.ne') (exp_ne_zero _), log_mul hfac.ne' hprod.ne',
    log_exp, log_prod (fun j _ => (hFp j).ne')] at hlog
  have hgroup : (∑ j, log (F j)) =
      36 * ∑ i : Fin (J+1), ((i.val : ℝ) * log M - log (i.val.factorial : ℝ)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [F, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [log_div (pow_ne_zero _ hMp.ne') (by positivity), log_pow]
    norm_num
  rw [hgroup] at hlog
  have hA : 0 ≤ A := log_nonneg ((by exact_mod_cast a.val.val.den_pos :
    (1 : ℝ) ≤ a.val.val.den).trans (le_max_right _ _))
  have hC : 0 ≤ C := log_nonneg ((by exact_mod_cast b.val.val.den_pos :
    (1 : ℝ) ≤ b.val.val.den).trans (le_max_right _ _))
  have hwa' : ((ua-la : ℕ) : ℝ) ≤ ((J+1 : ℕ) : ℝ)*324*(R : ℝ) := by exact_mod_cast hwa
  have hwb' : ((ub-lb : ℕ) : ℝ) ≤ ((J+1 : ℕ) : ℝ)*324*(S : ℝ) := by exact_mod_cast hwb
  refine hZl.trans (hlog.trans ?_)
  nlinarith [mul_le_mul_of_nonneg_right hwa' hA, mul_le_mul_of_nonneg_right hwb' hC]

end

end AbcTwoNinths.ExteriorE2
