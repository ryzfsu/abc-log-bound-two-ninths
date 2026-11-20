/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket

/-!
# Principal Unit Bracket

The module derives a principal-unit valuation bracket and its consequence under the polynomial height cap. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.b1Bracket`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

section



/--
Bounds the valuation of a signed lift minus one using the heights of two independent kernel generators and their nonzero coefficients. This is used in Section 6 of the paper.
-/
theorem b1Bracket {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {ι : Type*} [Fintype ι] (q : ι → ℕ) (hq : ∀ i, (q i).Prime)
    (avoid : ∀ i, p ≠ q i) (hp : 5 ≤ p) (hqinj : Function.Injective q)
    (w₁ w₂ v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid))
    (hcoords : Function.Injective
      (fun a : ℤ × ℤ => fun i => a.1 * w₁.val.toAdd i + a.2 * w₂.val.toAdd i))
    {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (hv : v = w₁ ^ c * w₂ ^ d)
    {B₁ B₂ : ℝ}
    (h₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)
      (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) w₁ : ℚ)) (Real.log (p : ℝ)) ≤ B₁)
    (h₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)
      (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) w₂ : ℚ)) (Real.log (p : ℝ)) ≤ B₂) :
    let ell := Real.log (p : ℝ)
    let b := (c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁
    (padicValRat p ((_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)
      (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) v : ℚ) - 1) : ℝ) * ell ^ 2 ≤
      588 * B₁ * B₂ * (max 4 (Real.log (Real.exp 2 * ell * (b / 2)) / ell)) ^ 2 :=
  _root_.AbcTwoNinths.Diamond.liftedBound q hq avoid hp hqinj w₁ w₂ v hcoords hc hd hv h₁ h₂

end

end AbcTwoNinths.Diamond
