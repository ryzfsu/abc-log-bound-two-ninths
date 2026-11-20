/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeInterpolationEdges
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeCollisionHeight

/-!
# Composite Contact Bound

The module bounds the depth of composite-modulus contact from the logarithmic height budget. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeContactBoundOfLogBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open Real

/--
Under the stated height and logarithmic budgets, coprime positive powers of multiplicatively
independent principal units cannot agree modulo `B ^ (rows (order (a * b)))` .
-/
theorem compositeContactBoundOfLogBudget {B c d : ℕ} (hB : 3 ≤ B)
    (u v : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (hu : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) u.val = 1)
    (hv : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) v.val = 1)
    (hi : ∀ m n : ℤ, u.val.val ^ m * v.val.val ^ n = 1 → m = 0 ∧ n = 0)
    (hc : c.Coprime d) (hc0 : 0 < c) (hd0 : 0 < d)
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hlog : log ((d : ℝ)/b+(c : ℝ)/a)+1 ≤ 15*log B)
    (hU : log (max (u.val.val.num.natAbs : ℝ) (u.val.val.den : ℝ)) ≤ b * log B)
    (hV : log (max (v.val.val.num.natAbs : ℝ) (v.val.val.den : ℝ)) ≤ a * log B)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order (a*b)))) (u.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order (a*b)))) (v.val ^ d)) :
    False := by
  have hB' : (3 : ℝ) ≤ B := by exact_mod_cast hB
  have hell : 1 < log (B : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).2 (Real.exp_one_lt_three.trans_le hB')
  have hA : 1 ≤ a*b := by
    have hh := mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ b-1 by linarith)
    nlinarith
  let J := _root_.AbcTwoNinths.Basic.order (a*b)
  let R := _root_.AbcTwoNinths.Basic.edge 36 a b
  let S := _root_.AbcTwoNinths.Basic.edge 36 b a
  let T := _root_.AbcTwoNinths.Basic.edge (J*36) a b
  let Q := _root_.AbcTwoNinths.Basic.edge (J*36) b a
  have ⟨h₁, h₂, hm, hw⟩ := _root_.AbcTwoNinths.ExteriorE2.compositeEdgeBudgets a b ha hb c d
  have hB1 : 1 < B := by omega
  have hl : 0 < log (B : ℝ) := by linarith
  by_cases hwidth : T < c ∨ Q < d
  · have hM : 0 < (R+T)*d+(S+Q)*c := by
      by_contra h
      have hzero : (R+T)*d+(S+Q)*c = 0 := by omega
      have he : R+T = 0 ∧ S+Q = 0 := by
        simpa [Nat.add_eq_zero_iff, Nat.mul_eq_zero, hc0.ne', hd0.ne'] using hzero
      have ht : T = 0 := by omega
      have hq : Q = 0 := by omega
      change 36 * J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle T Q) at h₂
      have hj : (0 : ℝ) < J := (show 0 < 400*(a*b) by nlinarith).trans_le
        (_root_.AbcTwoNinths.Basic.orderBounds (a*b) hA).1
      have hj' : 0 < J := by exact_mod_cast hj
      simp [ht, hq, _root_.AbcTwoNinths.Basic.Rectangle] at h₂
      omega
    refine _root_.AbcTwoNinths.ExteriorE2.compositeBudgetBound hB1 u v hu hv hi hc hwidth (a*b) _ (127*(a*b))
      hA hell (by positivity) hlog hM hm le_rfl h₁ h₂ ?_ hab
    calc
      _ ≤ ((R+T : ℕ) : ℝ) * (b * log B) + ((S+Q : ℕ) : ℝ) * (a * log B) :=
        add_le_add (mul_le_mul_of_nonneg_left hU (by positivity))
          (mul_le_mul_of_nonneg_left hV (by positivity))
      _ = (((R+T : ℕ) : ℝ)*b + ((S+Q : ℕ) : ℝ)*a) * log B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hl.le
  · push Not at hwidth
    have hne : u.val.val^c ≠ v.val.val^d := by
      intro h
      have hv0 : v.val.val ≠ 0 :=
        (Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom v).ne_zero
      have ht : u.val.val ^ (c : ℤ) * v.val.val ^ (-(d : ℤ)) = 1 := by
        rw [zpow_natCast, zpow_neg, zpow_natCast, h, mul_inv_cancel₀ (pow_ne_zero _ hv0)]
      exact hc0.ne' (by exact_mod_cast (hi _ _ ht).1)
    have hcross := _root_.AbcTwoNinths.ExteriorE2.compositePowerCrossBound (by omega : 0 < B) u.val v.val hab hne
    have hcv : (c : ℝ) ≤ ((R+T : ℕ) : ℝ) := by
      exact_mod_cast hwidth.1.trans (Nat.le_add_left T R)
    have hdv : (d : ℝ) ≤ ((S+Q : ℕ) : ℝ) := by
      exact_mod_cast hwidth.2.trans (Nat.le_add_left Q S)
    have hh : (c : ℝ)*b+(d : ℝ)*a ≤ 2*(127*(a*b)) :=
      (add_le_add (mul_le_mul_of_nonneg_right hcv (by linarith))
        (mul_le_mul_of_nonneg_right hdv (by linarith))).trans hw
    have hup := add_le_add (mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ (c : ℝ)))
      (mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ (d : ℝ)))
    have hh' := mul_le_mul_of_nonneg_right hh hl.le
    have hj := (_root_.AbcTwoNinths.Basic.orderBounds (a*b) hA).1
    have hrows : 400*(a*b) ≤ (_root_.AbcTwoNinths.Basic.rows J : ℝ) := by
      change 400*(a*b) ≤ (J : ℝ) at hj
      simp [_root_.AbcTwoNinths.Basic.rows, _root_.AbcTwoNinths.Basic.levels]
      linarith
    have hrows' := mul_le_mul_of_nonneg_right hrows hl.le
    have hpos : (a*b) * log B ≥ 1 := by
      have hp := mul_nonneg (show 0 ≤ a*b-1 by linarith) (show 0 ≤ log (B : ℝ)-1 by linarith)
      nlinarith
    change (_root_.AbcTwoNinths.Basic.rows J : ℝ) * log B ≤ _ at hcross
    nlinarith [Real.log_two_lt_d9]

end

end AbcTwoNinths.ExteriorE2
