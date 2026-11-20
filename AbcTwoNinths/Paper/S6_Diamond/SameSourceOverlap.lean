/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.CollisionConsumer
public import AbcTwoNinths.Paper.S4_ExteriorE2.VolumeSecondMoment
public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeSupply
public import AbcTwoNinths.Paper.S4_ExteriorE2.ProjectedMass

/-!
# Same Source Overlap

Chooses centers by residue class and uses overlap in the quotient to find witnesses in the
projected lattice. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.chooseCenters`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

open MeasureTheory Set
open scoped Pointwise ENNReal

section





variable {W E G : Type*} [AddCommGroup W] [NormedAddCommGroup E] [CommGroup G]

/--
The additive kernel of reduction on old exponent vectors. This is used in Section 6 of the paper.
-/
def oldKernel (red : Multiplicative W →* G) : AddSubgroup W :=
  red.toAdditive.ker

/--
An old exponent vector belongs to the reduction kernel exactly when its multiplicative reduction is one.
-/
theorem memOldKernel (red : Multiplicative W →* G) (w : W) :
    w ∈ _root_.AbcTwoNinths.Diamond.oldKernel red ↔ red (Multiplicative.ofAdd w) = 1 := Iff.rfl

/--
The quotient of the residue group by the image of the old exponents. This is used in Section 6 of the paper.
-/
abbrev Tag (red : Multiplicative W →* G) := G ⧸ red.range

/--
The quotient homomorphism assigning a label its class modulo the old image. This is used in Section 6 of the paper.
-/
def tag (red : Multiplicative W →* G) : G →* _root_.AbcTwoNinths.Diamond.Tag red := QuotientGroup.mk' red.range

/--
Choose a representative for each residue class and lift each label relative to its representative to an old exponent vector. This is used in Section 6 of the paper.
-/
theorem chooseCenters (red : Multiplicative W →* G) (label : ℕ → G) :
    ∃ (rep : _root_.AbcTwoNinths.Diamond.Tag red → G) (center : ℕ → W),
      ∀ q, label q = rep (_root_.AbcTwoNinths.Diamond.tag red (label q)) * red (Multiplicative.ofAdd (center q)) := by
  classical
  choose rep hrep using QuotientGroup.mk'_surjective red.range
  have h (q : ℕ) : ∃ w : W, label q = rep (_root_.AbcTwoNinths.Diamond.tag red (label q)) * red (Multiplicative.ofAdd w) := by
    have ht : _root_.AbcTwoNinths.Diamond.tag red (label q / rep (_root_.AbcTwoNinths.Diamond.tag red (label q))) = 1 := by
      rw [map_div, show _root_.AbcTwoNinths.Diamond.tag red (rep (_root_.AbcTwoNinths.Diamond.tag red (label q))) = _root_.AbcTwoNinths.Diamond.tag red (label q) from hrep _, div_self']
    obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff (N := red.range) _).mp ht
    refine ⟨w.toAdd, ?_⟩
    change label q = rep (_root_.AbcTwoNinths.Diamond.tag red (label q)) * red w
    rw [hw, div_eq_mul_inv]
    simp [mul_left_comm]
  choose center hc using h
  exact ⟨rep, center, hc⟩

variable (red : Multiplicative W →* G) (pi : W →+ E)

/--
The image of the old reduction kernel under the additive projection. This is used in Section 6 of the paper.
-/
abbrev Lattice := (_root_.AbcTwoNinths.Diamond.oldKernel red).map pi

/-- A lattice translate joining two patches gives a point in both quotient images. -/
theorem quotientOverlapOfOrbit (U V : Set E)
    (h : ∃ a ∈ U, ∃ b ∈ V, ∃ l : _root_.AbcTwoNinths.Diamond.Lattice red pi, l +ᵥ a = b) :
    ∃ z : E ⧸ _root_.AbcTwoNinths.Diamond.Lattice red pi,
      z ∈ (QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)) '' U ∧
      z ∈ (QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)) '' V := by
  obtain ⟨a, ha, b, hb, l, hl⟩ := h
  let Q := QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)
  have hl' : (l : E) + a = b := hl
  have hQl : Q (l : E) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr l.property
  have heq : Q b = Q a := by rw [← hl', map_add, hQl, zero_add]
  exact ⟨Q a, ⟨a, ha, rfl⟩, ⟨b, hb, heq⟩⟩

section FiniteFamily

/-- The increasing pairs of indices whose two sets meet. This is used in Section 6 of the paper. -/
noncomputable def overlapPairs (Q : Finset ℕ) {X : Type*} (A : ℕ → Set X) : Finset (ℕ × ℕ) := by
  classical
  exact (Q ×ˢ Q).filter (fun p => p.1 < p.2 ∧ (A p.1 ∩ A p.2).Nonempty)

/-- The cardinality of the increasing overlap pairs equals the overlap count. -/
theorem cardOverlapPairs (Q : Finset ℕ) {X : Type*} (A : ℕ → Set X) :
    (_root_.AbcTwoNinths.Diamond.overlapPairs Q A).card = _root_.AbcTwoNinths.ExteriorE2.overlaps Q A := by
  classical
  rw [_root_.AbcTwoNinths.Diamond.overlapPairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  rfl

/--
Two labels admit lifts relative to one representative whose patches meet in the projected quotient. This is used in Section 6 of the paper.
-/
def PatchInput (label : ℕ → G) (B : W → Set E) (i j : ℕ) : Prop :=
  ∃ (a b : W) (t : G) (z : E ⧸ _root_.AbcTwoNinths.Diamond.Lattice red pi),
    label i = t * red (Multiplicative.ofAdd a) ∧
    label j = t * red (Multiplicative.ofAdd b) ∧
    z ∈ (QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)) '' B a ∧
    z ∈ (QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)) '' B b

variable [Countable (_root_.AbcTwoNinths.Diamond.Lattice red pi)] [MeasurableSpace E]
  [MeasurableConstVAdd (_root_.AbcTwoNinths.Diamond.Lattice red pi) E]
  [Fintype (_root_.AbcTwoNinths.Diamond.Tag red)] [MeasurableSpace (_root_.AbcTwoNinths.Diamond.Tag red)] [MeasurableSingletonClass (_root_.AbcTwoNinths.Diamond.Tag red)]
  {ν : Measure E} [VAddInvariantMeasure (_root_.AbcTwoNinths.Diamond.Lattice red pi) E ν]

/-- Equal-mass patches that inject into the lattice quotient yield an ordered family of
labelled overlaps whose size is bounded below by the second-moment estimate. -/
theorem sameSourcePatchFamily {D : Set E} (hD : IsAddFundamentalDomain (_root_.AbcTwoNinths.Diamond.Lattice red pi) D ν)
    (hDm : MeasurableSet D) (hDf : ν D < ⊤)
    (label : ℕ → G) (Q : Finset ℕ) (hQ : Q.Nonempty) (B : W → Set E)
    (hB : ∀ c, MeasurableSet (B c))
    (hinj : ∀ c, ∀ a ∈ B c, ∀ b ∈ B c, ∀ l : _root_.AbcTwoNinths.Diamond.Lattice red pi, l +ᵥ a = b → l = 0)
    {W₀ : ℝ} (hW : 0 < W₀) (hMass : ∀ a : W, ν.real (B a) = W₀) :
    ∃ P : Finset (ℕ × ℕ),
      ((Q.card : ℝ) / 2) * (((Q.card : ℝ) * W₀) /
        ((Fintype.card (_root_.AbcTwoNinths.Diamond.Tag red) : ℝ) * ν.real D) - 1) ≤ P.card ∧
      ∀ p ∈ P, p.1 ∈ Q ∧ p.2 ∈ Q ∧ p.1 < p.2 ∧ _root_.AbcTwoNinths.Diamond.PatchInput red pi label B p.1 p.2 := by
  classical
  obtain ⟨rep, center, hcenter⟩ := _root_.AbcTwoNinths.Diamond.chooseCenters red label
  let A (q : ℕ) : Set (_root_.AbcTwoNinths.Diamond.Tag red × E) :=
    {_root_.AbcTwoNinths.Diamond.tag red (label q)} ×ˢ _root_.AbcTwoNinths.ExteriorE2.wrapped (L := _root_.AbcTwoNinths.Diamond.Lattice red pi) D (B (center q))
  let μ : Measure (_root_.AbcTwoNinths.Diamond.Tag red × E) := _root_.AbcTwoNinths.ExteriorE2.taggedMeasure D ν
  have hu : μ Set.univ = (Fintype.card (_root_.AbcTwoNinths.Diamond.Tag red) : ℝ≥0∞) * ν D := _root_.AbcTwoNinths.ExteriorE2.taggedMeasureUniv hDf
  have : IsFiniteMeasure μ := ⟨by
    rw [hu]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hDf⟩
  have hr : μ.real Set.univ = (Fintype.card (_root_.AbcTwoNinths.Diamond.Tag red) : ℝ) * ν.real D := by
    rw [measureReal_def, hu, ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def]
  refine ⟨_root_.AbcTwoNinths.Diamond.overlapPairs Q A, ?_, ?_⟩
  · rw [_root_.AbcTwoNinths.Diamond.cardOverlapPairs, ← hr]
    refine _root_.AbcTwoNinths.ExteriorE2.overlapLower μ Q hQ A ?_ W₀ hW ?_
    · intro i _
      exact (measurableSet_singleton (_root_.AbcTwoNinths.Diamond.tag red (label i))).prod
        (_root_.AbcTwoNinths.ExteriorE2.measurableWrapped (L := _root_.AbcTwoNinths.Diamond.Lattice red pi) hDm (hB (center i)))
    · intro i _
      change (_root_.AbcTwoNinths.ExteriorE2.taggedMeasure D ν).real ({_root_.AbcTwoNinths.Diamond.tag red (label i)} ×ˢ
        _root_.AbcTwoNinths.ExteriorE2.wrapped (L := _root_.AbcTwoNinths.Diamond.Lattice red pi) D (B (center i))) = W₀
      rw [measureReal_def, _root_.AbcTwoNinths.ExteriorE2.componentMass hD hDm hDf (hB (center i)) (hinj (center i))]
      exact hMass _
  · intro p hp
    obtain ⟨hmem, hlt, z, hz₁, hz₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    have hz₁' : z.1 = _root_.AbcTwoNinths.Diamond.tag red (label p.1) ∧ z.2 ∈ _root_.AbcTwoNinths.ExteriorE2.wrapped _ _ := hz₁
    have hz₂' : z.1 = _root_.AbcTwoNinths.Diamond.tag red (label p.2) ∧ z.2 ∈ _root_.AbcTwoNinths.ExteriorE2.wrapped _ _ := hz₂
    have ht := hz₁'.1.symm.trans hz₂'.1
    obtain ⟨w, hw₁, hw₂⟩ := _root_.AbcTwoNinths.Diamond.quotientOverlapOfOrbit red pi (B (center p.1)) (B (center p.2))
      (_root_.AbcTwoNinths.ExteriorE2.orbitOfWrappedOverlap ⟨hz₁'.2, hz₂'.2⟩)
    exact ⟨hi, hj, hlt, center p.1, center p.2, rep (_root_.AbcTwoNinths.Diamond.tag red (label p.1)), w,
      hcenter _, ht.symm ▸ hcenter _, hw₁, hw₂⟩

end FiniteFamily

end

end AbcTwoNinths.Diamond
