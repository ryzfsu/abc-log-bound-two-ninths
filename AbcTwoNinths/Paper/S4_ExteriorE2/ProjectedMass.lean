/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Projected Mass

The module relates the measure of wrapped sets to that of their projected translates. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.measureWrapped`
* `AbcTwoNinths.ExteriorE2.restrictMeasureWrapped`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE2

open MeasureTheory Set Function
open scoped Pointwise ENNReal

section

variable {L E : Type*} [AddGroup L] [Countable L]
  [MeasurableSpace E] [AddAction L E] [MeasurableConstVAdd L E]
  {ν : Measure E} [VAddInvariantMeasure L E ν]

/--
The part of the domain covered by translates of a patch. This is used in the proof of Proposition 4.1 of the paper.
-/
def wrapped (D B : Set E) : Set E := ⋃ l : L, (l +ᵥ B) ∩ D

/-- Wrapping a measurable patch into a measurable domain gives a measurable set. -/
theorem measurableWrapped {D B : Set E} (hD : MeasurableSet D) (hB : MeasurableSet B) :
    MeasurableSet (_root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B) :=
  MeasurableSet.iUnion (fun l : L => ((measurableEmbedding_const_vadd l).measurableSet_image' hB).inter hD)

/--
Wrapping an orbit-injective measurable patch into a fundamental domain preserves its measure. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem measureWrapped {D B : Set E} (hD : IsAddFundamentalDomain L D ν)
    (hB : MeasurableSet B) (hinj : ∀ x ∈ B, ∀ y ∈ B, ∀ l : L, l +ᵥ x = y → l = 0) :
    ν (_root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B) = ν B := by
  have hpair : Pairwise (AEDisjoint ν on fun l : L => (l +ᵥ B) ∩ D) := by
    apply Pairwise.aedisjoint
    intro g h hne
    change Disjoint ((g +ᵥ B) ∩ D) ((h +ᵥ B) ∩ D)
    rw [disjoint_left]
    rintro z ⟨⟨x,hx,rfl⟩,_⟩ ⟨⟨y,hy,hyx⟩,_⟩
    change h +ᵥ y = g +ᵥ x at hyx
    have heq : (-h+g) +ᵥ x = y := by
      rw [add_vadd, ← hyx, ← add_vadd, neg_add_cancel, zero_vadd]
    have hh := hinj x hx y hy (-h+g) heq
    exact hne (add_left_cancel (hh.trans (neg_add_cancel h).symm))
  calc
    ν (_root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B) = ∑' l : L, ν ((l +ᵥ B) ∩ D) :=
      measure_iUnion₀ hpair (fun l => (hB.nullMeasurableSet.vadd l).inter hD.nullMeasurableSet)
    _ = ν B := (hD.measure_eq_tsum B).symm

/--
The restricted fundamental-domain measure of an orbit-injective wrapped patch equals its original measure. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem restrictMeasureWrapped {D B : Set E} (hD : IsAddFundamentalDomain L D ν)
    (hDm : MeasurableSet D) (hB : MeasurableSet B)
    (hinj : ∀ x ∈ B, ∀ y ∈ B, ∀ l : L, l +ᵥ x = y → l = 0) :
    ν.restrict D (_root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B) = ν B := by
  rw [Measure.restrict_apply (_root_.AbcTwoNinths.ExteriorE2.measurableWrapped hDm hB)]
  have hd : _root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B ⊆ D := iUnion_subset fun _ => inter_subset_right
  rw [inter_eq_left.mpr hd]
  exact _root_.AbcTwoNinths.ExteriorE2.measureWrapped hD hB hinj

omit [Countable L] [MeasurableSpace E] [MeasurableConstVAdd L E] in
/-- Intersecting wrapped patches contain original points related by a group translation. -/
theorem orbitOfWrappedOverlap {D B B' : Set E} {z : E}
    (hz : z ∈ _root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B ∩ _root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B') :
    ∃ x ∈ B, ∃ y ∈ B', ∃ l : L, l +ᵥ x = y := by
  obtain ⟨l, hl⟩ := mem_iUnion.mp hz.1
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz.2
  obtain ⟨⟨x, hx, hxz⟩, _⟩ := hl
  obtain ⟨⟨y, hy, hyz⟩, _⟩ := hk
  change l +ᵥ x = z at hxz
  change k +ᵥ y = z at hyz
  refine ⟨x, hx, y, hy, -k+l, ?_⟩
  rw [add_vadd, hxz, ← hyz, ← add_vadd, neg_add_cancel, zero_vadd]

section tagged

variable {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/--
Counting measure on the tag space times the restricted measure on the domain. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def taggedMeasure (D : Set E) (ν : Measure E) : Measure (C × E) :=
  Measure.count.prod (ν.restrict D)

omit [MeasurableSingletonClass C] in
/--
For a domain of finite measure, the total mass is the number of tags times the measure of the domain.
-/
theorem taggedMeasureUniv {D : Set E} (hfin : ν D < ⊤) :
    _root_.AbcTwoNinths.ExteriorE2.taggedMeasure (C := C) D ν Set.univ = (Fintype.card C : ℝ≥0∞) * ν D := by
  have : IsFiniteMeasure (ν.restrict D) := ⟨by simpa using hfin⟩
  rw [_root_.AbcTwoNinths.ExteriorE2.taggedMeasure, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.count_apply MeasurableSet.univ, encard_univ, ENat.card_eq_coe_fintype_card]
  simp

omit [Fintype C] in
/-- A single tagged copy of an orbit-injective measurable patch has the original patch measure. -/
theorem componentMass {D B : Set E} (hD : IsAddFundamentalDomain L D ν)
    (hDm : MeasurableSet D) (hfin : ν D < ⊤) (hB : MeasurableSet B)
    (hinj : ∀ x ∈ B, ∀ y ∈ B, ∀ l : L, l +ᵥ x = y → l = 0) (c : C) :
    _root_.AbcTwoNinths.ExteriorE2.taggedMeasure D ν ({c} ×ˢ _root_.AbcTwoNinths.ExteriorE2.wrapped (L := L) D B) = ν B := by
  have : IsFiniteMeasure (ν.restrict D) := ⟨by simpa using hfin⟩
  rw [_root_.AbcTwoNinths.ExteriorE2.taggedMeasure, Measure.prod_prod, Measure.count_apply (measurableSet_singleton c),
    encard_singleton, _root_.AbcTwoNinths.ExteriorE2.restrictMeasureWrapped hD hDm hB hinj]
  simp

end tagged


end

end AbcTwoNinths.ExteriorE2
