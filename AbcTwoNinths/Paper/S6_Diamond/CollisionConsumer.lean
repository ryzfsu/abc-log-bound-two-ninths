/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Label correction after an overlap

Shows that the correction from two labels in the same residue coset cancels the residue of their
ratio. It also gives evaluation formulas for exponent vectors with two added coordinates.
It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.correctedLabel`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

section

/--
The fresh labels share one coset representative. The old correction then cancels
the quotient residue of the oriented fresh ratio. This is used in Section 6 of the paper.
-/
theorem correctedLabel {W G : Type*} [CommGroup W] [CommGroup G]
    (r : W →* G) (w a a' : W) (q q' t : G) (hw : r w = 1)
    (hq : q = t * r a) (hq' : q' = t * r a') :
    r (w * a⁻¹ * a') * (q / q') = 1 := by
  rw [map_mul, map_mul, map_inv, hw, hq, hq']
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
Adjoin the two fresh coordinates, with `false` denoting the numerator prime. This is used in Section 6 of the paper.
-/
def extendExponents {ι : Type*} (w : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) (e₀ e₁ : ℤ) : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool) :=
  Multiplicative.ofAdd (Sum.elim w.toAdd (fun b => if b then e₁ else e₀))

/-- Evaluation of the extended exponent vector multiplies the original monomial
by the powers of the two added bases. -/
theorem extendEval {ι G : Type*} [Fintype ι] [CommGroup G]
    (base : ι ⊕ Bool → G) (w : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) (e₀ e₁ : ℤ) :
    _root_.AbcTwoNinths.ExteriorE2.eval base (_root_.AbcTwoNinths.Diamond.extendExponents w e₀ e₁) =
      _root_.AbcTwoNinths.ExteriorE2.eval (fun i => base (.inl i)) w * (base (.inr false) ^ e₀ * base (.inr true) ^ e₁) := by
  classical
  simp [_root_.AbcTwoNinths.ExteriorE2.eval, _root_.AbcTwoNinths.Diamond.extendExponents, Fintype.prod_sum_type, mul_comm]

/-- Reducing a monomial modulo the sign subgroup equals evaluating it on the
individual residue classes modulo signs. -/
theorem reductionEval {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (base : ι → (ZMod p)ˣ) (w : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) :
    _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.eval base) w =
      _root_.AbcTwoNinths.ExteriorE2.eval (fun i => QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (base i)) w := by
  change QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (∏ i, base i ^ w.toAdd i) =
    ∏ i, QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (base i) ^ w.toAdd i
  simp only [map_prod, map_zpow]

end

end AbcTwoNinths.Diamond
