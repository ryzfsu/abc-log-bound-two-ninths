/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.PlaneCoordinateBox

/-!
# Height Minimum Selection

A nonzero minor gives attainment of the height minimum on any nonempty set of integer plane
coordinates. Injectivity of the exponent map makes the height positive away from zero. This
supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.selectHeightMinimum`
* `AbcTwoNinths.PolyCap.heightPosOfInjective`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
For prime weights and a nonzero coordinate minor, plane height attains a minimum on every inhabited set of integer pairs.
-/
theorem selectHeightMinimum {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) {e v : ι → ℤ} {i j : ι}
    (hd : e i * v j - e j * v i ≠ 0)
    (P : ℤ × ℤ → Prop) {w : ℤ × ℤ} (hw : P w) :
    ∃ z, P z ∧ ∀ x, P x → _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair z) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) := by
  classical
  let h (x : ℤ × ℤ) := _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x)
  obtain ⟨M, hM⟩ := _root_.AbcTwoNinths.PolyCap.planeHeightBoxBound q hq hd (B := h w)
    (_root_.AbcTwoNinths.PolyCap.coordHeightNonneg _)
  let S := ((Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M)).filter (fun x => P x ∧ h x ≤ h w)
  have hws : w ∈ S := Finset.mem_filter.mpr ⟨hM w le_rfl, hw, le_rfl⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S h ⟨w, hws⟩
  have hzp := (Finset.mem_filter.mp hz).2
  refine ⟨z, hzp.1, fun x hx => ?_⟩
  by_cases hxb : h x ≤ h w
  · exact hmin x (Finset.mem_filter.mpr ⟨hM x hxb, hx, hxb⟩)
  · exact hzp.2.trans (le_of_not_ge hxb)

/--
An injective integral plane map with prime weights gives positive height to every nonzero integer pair. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem heightPosOfInjective {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) {e v : ι → ℤ} (hinj : Function.Injective (_root_.AbcTwoNinths.PolyCap.planeMap e v))
    {x : ℤ × ℤ} (hx : x ≠ 0) : 0 < _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) := by
  have hex : ∃ j, _root_.AbcTwoNinths.PolyCap.planeMap e v x j ≠ 0 := by
    by_contra! h
    apply hx
    apply hinj
    funext j
    simpa [_root_.AbcTwoNinths.PolyCap.planeMap] using h j
  obtain ⟨j, hj⟩ := hex
  have hc : (_root_.AbcTwoNinths.PolyCap.planeMap e v x j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hl : 0 < Real.log (q j : ℝ) := Real.log_pos (by exact_mod_cast (hq j).one_lt)
  have hz : _root_.AbcTwoNinths.PolyCap.planeCoord q e v j (_root_.AbcTwoNinths.PolyCap.realPair x) ≠ 0 := by
    have hd := mul_ne_zero hc hl.ne'
    simpa only [_root_.AbcTwoNinths.PolyCap.planeMap, _root_.AbcTwoNinths.PolyCap.planeCoord, _root_.AbcTwoNinths.PolyCap.realPair, Int.cast_add, Int.cast_mul] using hd
  have hb := _root_.AbcTwoNinths.PolyCap.planeCoordLeTwiceHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) j
  linarith [abs_pos.mpr hz]

end

end AbcTwoNinths.PolyCap
