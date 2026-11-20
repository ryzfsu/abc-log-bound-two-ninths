/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Pivoted Exponent Coordinates

The module reindexes the selected pivot and proves that the positive and negative monomial parts are preserved. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.partsReindex`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
Reindexing the bases and exponents by the same equivalence preserves both the positive and
negative part products.
-/
theorem partsReindex {I J : Type*} [Fintype I] [Fintype J] (f : J ≃ I)
    (q : I → ℕ) (e : I → ℤ) :
    _root_.AbcTwoNinths.PolyCap.posPartNat (q ∘ f) (e ∘ f) = _root_.AbcTwoNinths.PolyCap.posPartNat q e ∧
    _root_.AbcTwoNinths.PolyCap.negPartNat (q ∘ f) (e ∘ f) = _root_.AbcTwoNinths.PolyCap.negPartNat q e := by
  constructor
  · exact Fintype.prod_equiv f _ _ (fun _ => rfl)
  · exact Fintype.prod_equiv f _ _ (fun _ => rfl)

/-- The pivot equiv. This is used in the proof of Proposition 4.1 of the paper. -/
noncomputable def pivotEquiv {I : Type*} (p : I) :
    (Unit ⊕ {i : I // i ≠ p}) ≃ I := by
  classical
  refine
    { toFun := Sum.elim (fun _ => p) Subtype.val
      invFun := fun i => if h : i = p then .inl () else .inr ⟨i, h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro j
    cases j with
    | inl u => cases u; simp
    | inr i => simp [i.property]
  · intro i
    by_cases h : i = p <;> simp [h]

end

end AbcTwoNinths.ExteriorE2
