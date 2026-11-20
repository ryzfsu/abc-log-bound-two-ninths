/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueReuse

/-!
# Residue Parts

The module characterizes the residue kernel by congruence between the positive and negative monomial parts. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.kernelIffDiffDvd`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
An exponent vector lies in the reduction kernel exactly when its positive and negative products agree modulo the modulus.
-/
theorem kernelIffParts {I : Type*} [Fintype I] (M : ℕ) (q : Unit ⊕ I → ℕ)
    (hc : ∀ j, (q j).Coprime M) (a : (Unit ⊕ I) → ℤ) :
    a ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker ↔
      (∏ j, (q j : ZMod M) ^ (a j).toNat) = ∏ j, (q j : ZMod M) ^ (-a j).toNat := by
  classical
  let u (j : Unit ⊕ I) := ZMod.unitOfCoprime (q j) (hc j)
  let up (b : (Unit ⊕ I) → ℤ) := ∏ j, u j ^ (b j).toNat
  have hu : (∏ j, u j ^ a j) = up a / up (-a) := by
    simp only [up, ← Finset.prod_div_distrib, Pi.neg_apply]
    apply Finset.prod_congr rfl
    intro j _
    have hj : a j = ((a j).toNat : ℤ) - ((-a j).toNat : ℤ) := by omega
    conv_lhs => rw [hj, zpow_sub]
    simp only [zpow_natCast, div_eq_mul_inv]
  change (∏ j, u j ^ a j) = 1 ↔ _
  rw [hu, div_eq_one]
  have parts (b : (Unit ⊕ I) → ℤ) :
      (up b : ZMod M) = ∏ j, (q j : ZMod M) ^ (b j).toNat := by
    simp [up, u, ZMod.coe_unitOfCoprime]
  constructor
  · intro h
    simpa only [parts, Pi.neg_apply] using congrArg (fun v : (ZMod M)ˣ => (v : ZMod M)) h
  · intro h
    apply Units.ext
    simpa only [parts, Pi.neg_apply] using h

/--
For ordered integral products, kernel membership is equivalent to divisibility of their natural difference by the modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem kernelIffDiffDvd {I : Type*} [Fintype I] (M : ℕ) (q : Unit ⊕ I → ℕ)
    (hc : ∀ j, (q j).Coprime M) (a : (Unit ⊕ I) → ℤ)
    {A D : ℕ} (ha : ∏ j, q j ^ (a j).toNat = A)
    (hd : ∏ j, q j ^ (-a j).toNat = D) (hle : D ≤ A) :
    a ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker ↔ M ∣ A - D := by
  rw [_root_.AbcTwoNinths.ExteriorE2.kernelIffParts]
  have hA : (∏ j, (q j : ZMod M) ^ (a j).toNat) = (A : ZMod M) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod M)) ha
  have hD : (∏ j, (q j : ZMod M) ^ (-a j).toNat) = (D : ZMod M) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod M)) hd
  rw [hA, hD, ← sub_eq_zero, ← Nat.cast_sub hle]
  exact ZMod.natCast_eq_zero_iff _ _

end

end AbcTwoNinths.ExteriorE2
