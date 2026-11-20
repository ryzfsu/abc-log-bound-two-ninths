/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueQuotientRing
public import AbcTwoNinths.Basic.PadicContact

/-!
# Composite Rational Newton

The module transfers a composite-modulus Newton depth bound to a rational determinant. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeRationalNewtonDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators

/--
Entrywise agreement with the Newton matrix to the required depth yields divisibility of the determinant numerator by the specified modulus power. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeRationalNewtonDepth {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (g : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) (hg : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ∣ g - 1)
    (E c : ℕ) (k t z : I → ℕ) (A : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B))
    (hA : ∀ i j, (B : ℤ) ^ Fintype.card I ∣
      ((A i j - (Nat.choose (c * z j) (k i) : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) *
        g ^ (t i * z j)).val).num)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    (B : ℤ) ^ E ∣ ((_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.mapMatrix A).det.num := by
  let F : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) := fun i j =>
    (Nat.choose (c * z j) (k i) : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) * g ^ (t i * z j)
  have h := _root_.AbcTwoNinths.Basic.newtonMatrixDvd (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    g hg E c k t z (A - F) (fun i j => _root_.AbcTwoNinths.ExteriorE2.compositeDvdOfNum _ (hA i j)) hE
  have heq : (fun i j => F i j + (A - F) i j : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)) = A := by
    ext i j
    simp [Matrix.sub_apply]
  change _ ∣ Matrix.det (fun i j => F i j + (A - F) i j : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)) at h
  rw [heq] at h
  rw [← RingHom.map_det]
  exact _root_.AbcTwoNinths.ExteriorE2.compositeNumOfDvd _ h

end

end AbcTwoNinths.ExteriorE2
