/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice
public import AbcTwoNinths.Basic.RoofCovolume
public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Residue Reuse

The module bounds the image of monomial reduction and uses the bound to obtain a short projection. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.rangeBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

open MeasureTheory Set
open scoped ENNReal

section




variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Map an integral exponent vector to the product of its base units raised to those exponents modulo M. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def monomialReduction (M : ℕ) (q : Unit ⊕ ι → ℕ)
    (hc : ∀ i, (q i).Coprime M) : _root_.AbcTwoNinths.ExteriorE2.Old ι →+ Additive (ZMod M)ˣ where
  toFun a := Additive.ofMul (∏ i, (ZMod.unitOfCoprime (q i) (hc i)) ^ a i)
  map_zero' := by change Additive.ofMul (∏ i, _ ^ (0 : ℤ)) = _; simp
  map_add' a b := by
    simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    rfl

omit [DecidableEq ι] in
/--
The image of monomial reduction modulo a nonzero natural number M has cardinality at most M. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem rangeBound (M : ℕ) [NeZero M] (q : Unit ⊕ ι → ℕ)
    (hc : ∀ i, (q i).Coprime M) :
    Nat.card (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).range ≤ M := by
  calc
    _ ≤ Nat.card (Additive (ZMod M)ˣ) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = M.totient := by
      change Nat.card (ZMod M)ˣ = _
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    _ ≤ M := M.totient_le

end

end AbcTwoNinths.ExteriorE2
