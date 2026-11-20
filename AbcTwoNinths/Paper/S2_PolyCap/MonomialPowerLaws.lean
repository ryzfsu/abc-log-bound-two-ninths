/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.ValuationResidueKernel

/-!
# Monomial Power Laws

The module shows that addition and scalar multiplication of exponents become multiplication and powers of monomials. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.prodMonomialSmul`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- Adding two exponent vectors multiplies their rational prime monomials. -/
theorem prodMonomialAdd {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (e v : ι → ℤ) :
    _root_.AbcTwoNinths.PolyCap.prodMonomial q (e + v) = _root_.AbcTwoNinths.PolyCap.prodMonomial q e * _root_.AbcTwoNinths.PolyCap.prodMonomial q v := by
  simp only [_root_.AbcTwoNinths.PolyCap.prodMonomial, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact zpow_add₀ (by exact_mod_cast (hq j).ne_zero) _ _

/-- Scaling an exponent vector by an integer `a` raises its rational monomial to the power `a`. -/
theorem prodMonomialSmul {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e : ι → ℤ) (a : ℤ) :
    _root_.AbcTwoNinths.PolyCap.prodMonomial q (a • e) = _root_.AbcTwoNinths.PolyCap.prodMonomial q e ^ a := by
  simp only [_root_.AbcTwoNinths.PolyCap.prodMonomial, ← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro j _
  change (q j : ℚ) ^ (a * e j) = ((q j : ℚ) ^ e j) ^ a
  rw [mul_comm, zpow_mul]

end

end AbcTwoNinths.PolyCap
