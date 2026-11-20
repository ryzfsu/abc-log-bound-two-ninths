/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.SquaredChart
public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffResidueKernel

/-!
# Triple Kernel

The module places a triple's signed source exponent vector in the cutoff residue kernel. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.tripleSourceKernel`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section





/--
The ordered squared source pair has signed exponents in the reduction kernel for every choice of pivot. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem tripleSourceKernel (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) {M : ℕ}
    (hm : M ∣ _root_.AbcTwoNinths.Statement.sideValue t s) (ho : (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ≤ (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1) :
    let A := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2
    let D := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2
    let S := (A * D).primeFactors
    ∃ e : S → ℤ, _root_.AbcTwoNinths.PolyCap.posPartNat Subtype.val e = A ∧ _root_.AbcTwoNinths.PolyCap.negPartNat Subtype.val e = D ∧
      ∃ hc : ∀ i : S, (i : ℕ).Coprime M,
        ∀ p : S, e ∘ _root_.AbcTwoNinths.ExteriorE2.pivotEquiv p ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M
          (Subtype.val ∘ _root_.AbcTwoNinths.ExteriorE2.pivotEquiv p) (fun j => hc (_root_.AbcTwoNinths.ExteriorE2.pivotEquiv p j))).ker := by
  classical
  obtain ⟨e, he, hd, hc⟩ := _root_.AbcTwoNinths.ExteriorE2.squaredSourceChart t s M hm
  refine ⟨e, he, hd, hc, fun p => ?_⟩
  apply _root_.AbcTwoNinths.ExteriorE2.reindexedSourceKernel (_root_.AbcTwoNinths.ExteriorE2.pivotEquiv p) Subtype.val e M hc he hd
    (Nat.pow_le_pow_left ho 2)
  simpa using _root_.AbcTwoNinths.ExteriorE2.sourceSqDepth t s (M := M) (L := 1) (by simpa using hm)

end

end AbcTwoNinths.ExteriorE2
