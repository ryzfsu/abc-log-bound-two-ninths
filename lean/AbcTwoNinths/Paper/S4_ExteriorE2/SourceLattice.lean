/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import AbcTwoNinths.Basic.ShapeCount

/-!
# Source Lattice

Expresses the heights of prime monomials in terms of their integer exponent vectors. It supports
Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.exponentHeightSiteExponent`
-/

@[expose] public section
namespace AbcTwoNinths.ExteriorE2

noncomputable section





section

/--
The integer exponent vector of a lattice site in the chosen two directions. This is used in the proof of Proposition 4.1 of the paper.
-/
def siteExponent {n : ℕ} (s : _root_.AbcTwoNinths.Basic.Shape n) (i : _root_.AbcTwoNinths.Basic.Sites) (j : Fin n) : ℤ :=
  i.1 * s.v j + i.2 * s.u j

/-- Casting a site exponent to the reals gives the exponent at the lifted site. -/
theorem castSiteExponent {n : ℕ} (s : _root_.AbcTwoNinths.Basic.Shape n) (i : _root_.AbcTwoNinths.Basic.Sites) (j : Fin n) :
    (_root_.AbcTwoNinths.ExteriorE2.siteExponent s i j : ℝ) = _root_.AbcTwoNinths.Basic.exponent s (_root_.AbcTwoNinths.Basic.lift i) j := by
  simp [_root_.AbcTwoNinths.ExteriorE2.siteExponent, _root_.AbcTwoNinths.Basic.exponent, _root_.AbcTwoNinths.Basic.lift]

/--
The weighted height of an integer exponent vector is the maximum of its positive and negative logarithmic sums. This is used in the proof of Proposition 4.1 of the paper.
-/
def exponentHeight {n : ℕ} (s : _root_.AbcTwoNinths.Basic.Shape n) (w : Fin n → ℤ) : ℝ :=
  max (∑ j, max ((w j : ℝ) * Real.log (s.primeAt j : ℝ)) 0)
    (∑ j, max (-((w j : ℝ) * Real.log (s.primeAt j : ℝ))) 0)

/--
The exponent height of a site equals the real height of its lift. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem exponentHeightSiteExponent {n : ℕ} (s : _root_.AbcTwoNinths.Basic.Shape n) (i : _root_.AbcTwoNinths.Basic.Sites) :
    _root_.AbcTwoNinths.ExteriorE2.exponentHeight s (_root_.AbcTwoNinths.ExteriorE2.siteExponent s i) = _root_.AbcTwoNinths.Basic.height s (_root_.AbcTwoNinths.Basic.lift i) := by
  simp only [_root_.AbcTwoNinths.ExteriorE2.exponentHeight, _root_.AbcTwoNinths.Basic.height, _root_.AbcTwoNinths.Basic.logCoord, _root_.AbcTwoNinths.ExteriorE2.castSiteExponent]

end

end
end AbcTwoNinths.ExteriorE2
