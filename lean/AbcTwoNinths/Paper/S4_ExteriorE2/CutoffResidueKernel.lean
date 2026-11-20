/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PivotedExponentCoordinates
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueParts

/-!
# Cutoff Residue Kernel

The module transfers the source vector into the modular kernel after reindexing the prime support. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.reindexedSourceKernel`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
Divisibility of the ordered monomial-part difference puts the reindexed exponent vector in the reduction kernel. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem reindexedSourceKernel {I J : Type*} [Fintype I] [Fintype J]
    (f : (Unit ⊕ J) ≃ I) (q : I → ℕ) (e : I → ℤ) (M : ℕ)
    (hc : ∀ i, (q i).Coprime M) {A D : ℕ}
    (hA : _root_.AbcTwoNinths.PolyCap.posPartNat q e = A) (hD : _root_.AbcTwoNinths.PolyCap.negPartNat q e = D)
    (hord : D ≤ A) (hd : M ∣ A - D) :
    e ∘ f ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M (q ∘ f) (fun j => hc (f j))).ker := by
  have h := _root_.AbcTwoNinths.ExteriorE2.partsReindex f q e
  apply (_root_.AbcTwoNinths.ExteriorE2.kernelIffDiffDvd M (q ∘ f) (fun j => hc (f j)) (e ∘ f)
    (h.1.trans hA) (h.2.trans hD) hord).mpr
  exact hd

end

end AbcTwoNinths.ExteriorE2
