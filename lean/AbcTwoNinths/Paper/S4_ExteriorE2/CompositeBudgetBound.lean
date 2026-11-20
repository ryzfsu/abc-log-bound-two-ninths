/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeContactInjectivity
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeInterpolationNodes
public import AbcTwoNinths.Basic.TwoLogarithmConstants

/-!
# Composite Budget Bound

The module bounds composite-modulus contact depth in terms of the interpolation budget. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeBudgetBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open Real

/--
The rectangle size, width, degree, and height budgets rule out equality of the indicated
coprime powers modulo `B ^ (36 * (order A + 1))` for multiplicatively independent principal
units.
-/
theorem compositeBudgetBound {B c d R S R' S' : ℕ} (hB : 1 < B)
    (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (ha : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) a.val = 1)
    (hb : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) b.val = 1)
    (hi : ∀ m n : ℤ, a.val.val ^ m * b.val.val ^ n = 1 → m = 0 ∧ n = 0)
    (hc : c.Coprime d) (hwidth : R' < c ∨ S' < d)
    (A U W : ℝ) (hA : 1 ≤ A) (hell : 1 < log B) (hU : 0 < U)
    (hlog : log U + 1 ≤ 15*log B)
    (hM : 0 < (R+R')*d+(S+S')*c)
    (hm : ((((R+R')*d+(S+S')*c : ℕ) : ℝ)) ≤ (127*A)*U)
    (hw : W ≤ 127*A)
    (h₁ : 36 ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S))
    (h₂ : 36 * _root_.AbcTwoNinths.Basic.order A < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S'))
    (hW : ((R+R' : ℕ) : ℝ) * log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ)) +
      ((S+S' : ℕ) : ℝ) * log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ)) ≤
      2*W*log B)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((_root_.AbcTwoNinths.Basic.order A+1)*36)) (a.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((_root_.AbcTwoNinths.Basic.order A+1)*36)) (b.val ^ d)) :
    False := by
  have hj : 0 < _root_.AbcTwoNinths.Basic.order A := by
    obtain ⟨hj, _, _⟩ := _root_.AbcTwoNinths.Basic.orderBounds A hA
    exact_mod_cast (show (0 : ℝ) < (_root_.AbcTwoNinths.Basic.order A : ℝ) by linarith)
  have hdet := _root_.AbcTwoNinths.ExteriorE2.compositeInjective hB a b ha hb hab hi hc hj h₁ h₂
    (hwidth.elim (_root_.AbcTwoNinths.ExteriorE2.nodeZInjectiveOfWidth hc) (_root_.AbcTwoNinths.ExteriorE2.nodeZInjectiveOfSecondWidth hc)) W hM hW
  exact _root_.AbcTwoNinths.Basic.contradiction A (log B) U _ W hA hell hU (by exact_mod_cast hM)
    hlog hm hw (by simpa [_root_.AbcTwoNinths.Basic.rows, _root_.AbcTwoNinths.Basic.levels] using hdet)

end

end AbcTwoNinths.ExteriorE2
