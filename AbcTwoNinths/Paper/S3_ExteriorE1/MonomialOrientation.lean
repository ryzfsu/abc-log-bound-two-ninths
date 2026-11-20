/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.MonomialLog

/-!
# Monomial Orientation

The module changes the signs of monomial exponents while controlling their heights. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.orientMonomial`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
The logarithmic height of a monomial in distinct primes equals the signed height of its exponent vector with prime logarithm weights.
-/
theorem monomialHeight {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (e : ι → ℤ) :
    _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial p e) =
      _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i => Real.log (p i : ℝ)) e := by
  change _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial p e) = _
  rw [(_root_.AbcTwoNinths.PolyCap.ratHeightProdMonomial p hp hinj e).1]
  unfold _root_.AbcTwoNinths.ExteriorE1.signedHeight
  have h (i : ι) (x : ℝ) :
      max (x * Real.log (p i : ℝ)) 0 = Real.log (p i : ℝ) * max x 0 := by
    rw [mul_max_of_nonneg _ _ (Real.log_nonneg (by exact_mod_cast (hp i).one_le)),
      mul_zero, mul_comm]
  simp only [← neg_mul, h]

/--
A nonzero exponent vector on distinct primes admits a sign for which its monomial is greater than one. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem orientMonomial {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (e : ι → ℤ) (he : e ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ 1 < _root_.AbcTwoNinths.PolyCap.prodMonomial p (s • e) := by
  have hne : _root_.AbcTwoNinths.PolyCap.prodMonomial p e ≠ 1 := by
    intro h
    exact he (funext ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff p hp hinj e).mp h))
  have hpos := _root_.AbcTwoNinths.ExteriorE1.monomialPos p hp e
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h : _root_.AbcTwoNinths.PolyCap.prodMonomial p ((-1 : ℤ) • e) = (_root_.AbcTwoNinths.PolyCap.prodMonomial p e)⁻¹ := by
      simp [_root_.AbcTwoNinths.PolyCap.prodMonomial, zpow_neg, Finset.prod_inv_distrib]
    rw [h]
    exact (one_lt_inv₀ hpos).mpr hlt
  · exact ⟨1, Or.inl rfl, by simpa using hgt⟩

end

end AbcTwoNinths.ExteriorE1
