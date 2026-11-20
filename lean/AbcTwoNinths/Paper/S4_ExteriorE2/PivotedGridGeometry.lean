/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffImagePlane
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeModulusTail
public import AbcTwoNinths.Paper.S3_ExteriorE1.MaximalLogarithmicPivot
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueReuse

/-!
# Pivoted Grid Geometry

The module checks the residue-grid geometry and obtains uniform modulus conditions for the small-prime tail. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.uniformConditions`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real


/-- The maximal positive exponent and the total weight bound give the upper bound on the height. -/
theorem roofMass {J : Type*} [Fintype J] (w : J → ℝ) (E : J → ℤ)
    (p : J) (hw : ∀ i, 0 ≤ w i) (hp : 0 < E p)
    (hm : ∀ i, (E i).natAbs ≤ (E p).natAbs) {H x : ℝ}
    (hH : H ≤ _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (E j : ℝ)))
    (hs : (∑ i, w i) ≤ 3 * x) :
    H ≤ (E p : ℝ) * (3 * x) := by
  have h := _root_.AbcTwoNinths.ExteriorE1.signedHeightLeWeightedAbs w E hw
  change _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (E j : ℝ)) ≤ _ at h
  have hb (j : J) : |(E j : ℝ)| ≤ (E p : ℝ) := by
    have hz : |E j| ≤ E p := by
      rw [Int.abs_eq_natAbs, ← abs_of_pos hp, Int.abs_eq_natAbs]
      exact_mod_cast hm j
    exact_mod_cast hz
  calc
    H ≤ ∑ j, w j * |(E j : ℝ)| := hH.trans h
    _ ≤ ∑ j, w j * (E p : ℝ) := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hb j) (hw j)
    _ = (E p : ℝ) * ∑ j, w j := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by exact_mod_cast hp.le)

/--
The grid width lies below the logarithmic scale, and its weighted product bound implies the stated height bound.
-/
theorem gridGeometry {J : Type*} [Fintype J] (w : Unit ⊕ J → ℝ)
    (hw : ∀ j, 0 ≤ w j) {H x ell hv U Z : ℝ} {Q : ℕ} (hq : 48 ≤ (Q : ℝ))
    (hell : 0 ≤ ell) (hx : x ≤ 4 * ell) (hh : 0 ≤ hv) (hhH : hv ≤ 2 * H)
    (hs : (∑ i, w i) ≤ 3 * x) :
    4 * ((∑ i, w (.inr i)) / Q) ≤ ell ∧
      (U * Z ≤ 4 * hv * ((∑ i, w (.inr i)) / Q) → U * Z ≤ 24 * H * x / Q) := by
  have hq0 : 0 < (Q : ℝ) := by linarith
  have hs' : (∑ i, w (.inr i)) ≤ 3 * x := by
    rw [Fintype.sum_sum_type] at hs
    exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hw (.inl j))).trans hs
  have hx0 : 0 ≤ x := by linarith [Finset.sum_nonneg (s := Finset.univ) (fun j _ => hw j)]
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ hq0]
    nlinarith only [hs', hx, mul_le_mul_of_nonneg_left hq hell]
  · intro h
    rw [← mul_div_assoc, le_div_iff₀ hq0] at h
    apply (le_div_iff₀ hq0).2
    have h1 := mul_le_mul_of_nonneg_left hs' hh
    have h2 := mul_le_mul_of_nonneg_right hhH hx0
    linarith only [h, h1, h2]

/-- The modulus conditions. This is used in the proof of Proposition 4.1 of the paper. -/
structure ModulusConditions (η : ℚ) (σ κ : ℝ) (Q : ℕ) (t : _root_.AbcTwoNinths.Basic.Triple)
    (M L : ℕ) : Prop where
  high : _root_.AbcTwoNinths.Statement.High η 0 t
  x_pos : 0 < t.thirdLogRadical
  modulus : 3 ≤ M
  log_floor : t.thirdLogRadical ≤ 4 * log (M : ℝ)
  depth : 146 + 2 * (64 / κ) ≤ (L : ℝ)
  root_onset : 4 / (κ / 16) * log (8 / ((κ / 16) * log 2)) ≤ t.logHeight
  grid_cost : ∀ S : Finset ℕ, S ⊆ (t.a * t.b * t.c).primeFactors →
    log (4 / (κ / 16)) + log (3 * t.thirdLogRadical) + (S.card : ℝ) * log (Q : ℝ) < σ * t.thirdLogRadical

/--
One height threshold supplies the modulus conditions for every admissible modulus and depth. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem uniformConditions {η : ℚ} {σ κ : ℝ} (Q : ℕ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : 0 < κ) :
    ∃ X : ℝ, ∀ t : _root_.AbcTwoNinths.Basic.Triple, _root_.AbcTwoNinths.Statement.High η X t →
      ∀ M L : ℕ, 2 ≤ M → (M : ℝ) ≤ t.logHeight * exp (-σ * t.thirdLogRadical) →
        (log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ log (M : ℝ) →
        κ * t.logHeight / 16 ≤ (L : ℝ) * log (M : ℝ) →
        _root_.AbcTwoNinths.ExteriorE2.ModulusConditions η σ κ Q t M L := by
  obtain ⟨A, hA⟩ := _root_.AbcTwoNinths.ExteriorE2.eventualConstantGridCost Q (θ := κ / 16) hσ.1
  obtain ⟨B, _, hBA, hB⟩ := _root_.AbcTwoNinths.ExteriorE2.enlargeHighForHeight hη (max 1 A)
    (4 / (κ / 16) * log (8 / ((κ / 16) * log 2)))
  obtain ⟨X, hXB, hX⟩ := _root_.AbcTwoNinths.ExteriorE2.e2ModulusNumericOnset (X := B) hη hσ hκ
    (show 0 ≤ 146 + 2 * (64 / κ) by positivity)
  refine ⟨X, fun t ht M L hM hc hlo hmass => ?_⟩
  obtain ⟨ht', hHt⟩ := hB t ⟨hXB.trans ht.1, ht.2⟩
  obtain ⟨h3, hx, hlarge⟩ := hX t ht M L hM hc hlo hmass
  have hxpos : 0 < t.thirdLogRadical := zero_lt_one.trans_le ((le_max_left _ _).trans ht'.1)
  refine ⟨⟨hxpos.le, ht'.2⟩, hxpos, h3, hx, hlarge, hHt, fun S hs => ?_⟩
  exact hA t ((le_max_right _ _).trans ht'.1) S hs (3 * t.thirdLogRadical) (by positivity) le_rfl

end

end AbcTwoNinths.ExteriorE2
