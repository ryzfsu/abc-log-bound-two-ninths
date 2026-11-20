/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SignedBasisIndependence

/-!
# Monomial Quotient Valuation

The module relates the depth of a difference to the valuation of a signed monomial quotient. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.signedMonomialQuotient`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section


/--
If the quotient of two rational powers is x distinct from one and the denominator is a p-adic unit, the valuation of their difference equals that of x minus one.
-/
theorem differenceDepthOfQuotient {p n m : ℕ} {a b x : ℚ}
    (hp : p.Prime) (hb : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p b) (hx : x ≠ 1) (he : a ^ n / b ^ m = x) :
    padicValRat p (a ^ n - b ^ m) = padicValRat p (x - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hb0 : b ^ m ≠ 0 := pow_ne_zero _ hb.2.1
  have hdiff : a ^ n - b ^ m = b ^ m * (x - 1) := by
    have hmul := (div_eq_iff hb0).mp he
    rw [hmul]
    ring
  rw [hdiff, padicValRat.mul hb0 (sub_ne_zero.mpr hx), padicValRat.pow, hb.2.2.1]
  simp

/--
Signed powers of two plane monomials reconstruct the source monomial when their combined coordinates are (1, 0). This is used in the proof of Proposition 2.1 of the paper.
-/
theorem signedMonomialQuotient {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (e v : ι → ℤ) (w m : ℤ × ℤ)
    {a b s t : ℤ} {n k : ℕ} (hs : (n : ℤ) * s = a) (ht : (k : ℤ) * t = -b)
    (h1 : a * w.1 + b * m.1 = 1) (h2 : a * w.2 + b * m.2 = 0) :
    _root_.AbcTwoNinths.PolyCap.prodMonomial q (s • _root_.AbcTwoNinths.PolyCap.planeMap e v w) ^ n /
      _root_.AbcTwoNinths.PolyCap.prodMonomial q (t • _root_.AbcTwoNinths.PolyCap.planeMap e v m) ^ k = _root_.AbcTwoNinths.PolyCap.prodMonomial q e := by
  rw [← zpow_natCast, ← zpow_natCast, ← _root_.AbcTwoNinths.PolyCap.prodMonomialSmul, ← _root_.AbcTwoNinths.PolyCap.prodMonomialSmul,
    smul_smul, smul_smul, hs, ht, div_eq_mul_inv, ← zpow_neg_one,
    ← _root_.AbcTwoNinths.PolyCap.prodMonomialSmul, smul_smul]
  have h : (-1 : ℤ) * -b = b := by ring
  rw [h, ← _root_.AbcTwoNinths.PolyCap.prodMonomialAdd q hq, ← _root_.AbcTwoNinths.PolyCap.planeMapSmulAdd]
  congr 1
  have hp : a • w + b • m = ((1, 0) : ℤ × ℤ) := Prod.ext h1 h2
  rw [hp]
  funext j
  simp [_root_.AbcTwoNinths.PolyCap.planeMap]

end

end AbcTwoNinths.PolyCap
