/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Exponent Residue

The residue homomorphism maps an integer exponent vector to a product of units modulo `p`. At a
prime modulus, bases indivisible by `p` are coprime to it.

## Main results
* `AbcTwoNinths.Basic.residue`
* `AbcTwoNinths.Basic.awayCoprime`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

variable {I : Type*} [Fintype I] {p : ℕ}

/--
Map an integer exponent vector to the product of its coprime base residues raised to those exponents.
-/
noncomputable def residue (q : I → ℕ) (hq : ∀ i, Nat.Coprime (q i) p) :
    (I → ℤ) →+ Additive (ZMod p)ˣ where
  toFun x := Additive.ofMul (∏ i, (ZMod.unitOfCoprime (q i) (hq i)) ^ x i)
  map_zero' := by simp
  map_add' x y := by
    change (∏ i, (ZMod.unitOfCoprime (q i) (hq i)) ^ (x i + y i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]
    rfl

omit [Fintype I] in
/-- Each base indivisible by the prime modulus is coprime to it. -/
theorem awayCoprime (hp : p.Prime) (q : I → ℕ)
    (haway : ∀ i, ¬ p ∣ q i) : ∀ i, Nat.Coprime (q i) p :=
  fun i => (hp.coprime_iff_not_dvd.mpr (haway i)).symm

end

end AbcTwoNinths.Basic
