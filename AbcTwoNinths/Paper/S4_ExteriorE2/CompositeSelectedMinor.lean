/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeClearing
public import AbcTwoNinths.Basic.RationalBinomialMinor

/-!
# Composite Selected Minor

The module bounds the selected interpolation minor used in the composite contact estimate. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeSelectedMinorBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open scoped BigOperators


/--
A nonzero minor of the prescribed numerator depth yields one cleared integer satisfying both the logarithmic lower bound and the height upper bound. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeSelectedMinorBound {I : Type*} [Fintype I] [DecidableEq I]
    {B E : ℕ} (hB : 0 < B) (a b : Units (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B))
    (k t r s : I → ℕ) (c d R S la ua lb ub : ℕ)
    (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (he : ∀ σ : Equiv.Perm I, la ≤ ∑ j, t (σ j)*r j ∧ (∑ j, t (σ j)*r j) ≤ ua)
    (hf : ∀ σ : Equiv.Perm I, lb ≤ ∑ j, t (σ j)*s j ∧ (∑ j, t (σ j)*s j) ≤ ub)
    (D : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (hD : D.val = (_root_.AbcTwoNinths.Basic.actualEntry (a.val.val) (b.val.val) k t r s c d).det)
    (hD0 : D.val ≠ 0)
    (hdepth : (B : ℤ) ^ E ∣ D.val.num) :
    ∃ Z : ℤ, (E : ℝ) * Real.log B ≤ Real.log (Z.natAbs : ℝ) ∧
      (Z.natAbs : ℝ) ≤ (Fintype.card I).factorial *
        (∏ j, ((R*d+S*c : ℕ) : ℝ)^(k j) / ((k j).factorial : ℝ)) *
        Real.exp ((ua-la : ℕ) * Real.log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ)) +
          (ub-lb : ℕ) * Real.log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ))) := by
  have ha : a.val.val ≠ 0 := by
    exact (Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom a).ne_zero
  have hb : b.val.val ≠ 0 := by
    exact (Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom b).ne_zero
  obtain ⟨Z, hZ, hZb⟩ := _root_.AbcTwoNinths.Basic.selectedMinorBound a.val.val b.val.val ha hb k t r s
    c d R S la ua lb ub hr hs he hf
  let u : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B :=
    ((a⁻¹).val ^ la * (a.val.val.den : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ (ua-la)) *
    ((b⁻¹).val ^ lb * (b.val.val.den : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ (ub-lb))
  have hu : u.val = ((a.val.val ^ la)⁻¹ * (a.val.val.den : ℚ) ^ (ua-la)) *
      ((b.val.val ^ lb)⁻¹ * (b.val.val.den : ℚ) ^ (ub-lb)) := by
    change (((Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom a)⁻¹).val ^ la * _) *
      (((Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom b)⁻¹).val ^ lb * _) = _
    simp [Units.val_inv_eq_inv_val, inv_pow]
  have hclear : (Z : ℚ) = u.val * D.val := by rw [hu, hD]; exact hZ
  have hu0 : u.val ≠ 0 := by
    rw [hu]
    positivity
  have hZ0 : Z ≠ 0 := by
    exact_mod_cast (hclear.symm ▸ mul_ne_zero hu0 hD0)
  exact ⟨Z, _root_.AbcTwoNinths.ExteriorE2.compositeClearedLogBound hB D u hZ0 hclear hdepth, hZb⟩

end

end AbcTwoNinths.ExteriorE2
