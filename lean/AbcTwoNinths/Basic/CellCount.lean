/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module
public import Mathlib

/-!
# Cell Count

The module compares a lattice-point count with the volumes of the cells centered at the points.

## Main results
* `AbcTwoNinths.Basic.countBounds`
-/

@[expose] public section
namespace AbcTwoNinths.Basic

noncomputable section Geometry
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise
section

/-- The real coordinate plane used to measure lattice cells. -/
abbrev Plane := ℝ × ℝ
/-- An integer coordinate pair indexing a lattice cell. -/
abbrev Sites := ℤ × ℤ
/-- Embed an integer lattice site in the real coordinate plane. -/
def lift (i : _root_.AbcTwoNinths.Basic.Sites) : _root_.AbcTwoNinths.Basic.Plane := (i.1, i.2)
/-- The center. -/
def center (x : _root_.AbcTwoNinths.Basic.Plane) : _root_.AbcTwoNinths.Basic.Sites := (⌊x.1 + 1/2⌋, ⌊x.2 + 1/2⌋)
/-- The half-open unit square centered at an integer lattice site. -/
def cell (i : _root_.AbcTwoNinths.Basic.Sites) : Set _root_.AbcTwoNinths.Basic.Plane :=
  Ico ((i.1 : ℝ) - 1/2) (i.1 + 1/2) ×ˢ Ico ((i.2 : ℝ) - 1/2) (i.2 + 1/2)

/-- A point belongs to a lattice cell exactly when its rounded center is the indexing site. -/
theorem memCellIff (x : _root_.AbcTwoNinths.Basic.Plane) (i : _root_.AbcTwoNinths.Basic.Sites) : x ∈ _root_.AbcTwoNinths.Basic.cell i ↔ _root_.AbcTwoNinths.Basic.center x = i := by
  change (_ ∧ _) ↔ (_, _) = _
  rw [Prod.ext_iff]
  simp only [Int.floor_eq_iff, mem_Ico]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Each lattice cell has volume one. -/
theorem volumeCell (i : _root_.AbcTwoNinths.Basic.Sites) : volume (_root_.AbcTwoNinths.Basic.cell i) = 1 := by
  rw [_root_.AbcTwoNinths.Basic.cell, volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  ring_nf
  simp

/-- The volume of a finite union of lattice cells equals the number of indexing sites. -/
theorem volumeCells (s : Finset _root_.AbcTwoNinths.Basic.Sites) : volume (⋃ i ∈ s, _root_.AbcTwoNinths.Basic.cell i) = s.card := by
  rw [measure_biUnion_finset]
  · simp [_root_.AbcTwoNinths.Basic.volumeCell]
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (((_root_.AbcTwoNinths.Basic.memCellIff x i).mp hxi).symm.trans ((_root_.AbcTwoNinths.Basic.memCellIff x j).mp hxj))
  · intro i _
    exact measurableSet_Ico.prod measurableSet_Ico

/-- The horizontal coordinate unit vector. -/
def e₁ : _root_.AbcTwoNinths.Basic.Plane := (1, 0)
/-- The vertical coordinate unit vector. -/
def e₂ : _root_.AbcTwoNinths.Basic.Plane := (0, 1)

/--
The seminorm distance from a cell point to its site is at most any bound on half the sum of the coordinate unit seminorms.
-/
theorem centeredBound (p : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane) {R : ℝ}
    (hR : (p _root_.AbcTwoNinths.Basic.e₁ + p _root_.AbcTwoNinths.Basic.e₂)/2 ≤ R) {x : _root_.AbcTwoNinths.Basic.Plane} {i : _root_.AbcTwoNinths.Basic.Sites} (hx : x ∈ _root_.AbcTwoNinths.Basic.cell i) :
    p (x - _root_.AbcTwoNinths.Basic.lift i) ≤ R := by
  rcases hx with ⟨⟨hx₁,hx₂⟩,⟨hy₁,hy₂⟩⟩
  have he : x - _root_.AbcTwoNinths.Basic.lift i = (x.1 - i.1) • _root_.AbcTwoNinths.Basic.e₁ + (x.2 - i.2) • _root_.AbcTwoNinths.Basic.e₂ := by
    ext <;> simp [_root_.AbcTwoNinths.Basic.lift,_root_.AbcTwoNinths.Basic.e₁,_root_.AbcTwoNinths.Basic.e₂]
  rw [he]
  apply (map_add_le_add p _ _).trans
  simp only [map_smul_eq_mul, Real.norm_eq_abs]
  have ha : |x.1 - i.1| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |x.2 - i.2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [mul_le_mul_of_nonneg_right ha (apply_nonneg p _root_.AbcTwoNinths.Basic.e₁),
    mul_le_mul_of_nonneg_right hb (apply_nonneg p _root_.AbcTwoNinths.Basic.e₂)]

/--
The union of cells indexed by sites in a seminorm ball lies between the closed balls with radii decreased and increased by the cell error.
-/
theorem cellSandwich (p : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane) (d R : ℝ) (s : Finset _root_.AbcTwoNinths.Basic.Sites)
    (hs : ∀ i, i ∈ s ↔ p (_root_.AbcTwoNinths.Basic.lift i) ≤ d) (hR : (p _root_.AbcTwoNinths.Basic.e₁ + p _root_.AbcTwoNinths.Basic.e₂)/2 ≤ R) :
    p.closedBall 0 (d-R) ⊆ ⋃ i ∈ s, _root_.AbcTwoNinths.Basic.cell i ∧
      (⋃ i ∈ s, _root_.AbcTwoNinths.Basic.cell i) ⊆ p.closedBall 0 (d+R) := by
  constructor
  · intro x hx
    have hh := p.mem_closedBall_zero.mp hx
    let i := _root_.AbcTwoNinths.Basic.center x
    have hi : x ∈ _root_.AbcTwoNinths.Basic.cell i := (_root_.AbcTwoNinths.Basic.memCellIff _ _).mpr rfl
    have hb := _root_.AbcTwoNinths.Basic.centeredBound p hR hi
    have ha := map_add_le_add p x (-(x - _root_.AbcTwoNinths.Basic.lift i))
    rw [show x + -(x - _root_.AbcTwoNinths.Basic.lift i) = _root_.AbcTwoNinths.Basic.lift i by abel, map_neg_eq_map] at ha
    exact mem_iUnion₂.mpr ⟨i, (hs i).mpr (by linarith), hi⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hb := _root_.AbcTwoNinths.Basic.centeredBound p hR hxi
    have ha := map_add_le_add p (x - _root_.AbcTwoNinths.Basic.lift i) (_root_.AbcTwoNinths.Basic.lift i)
    rw [sub_add_cancel] at ha
    exact p.mem_closedBall_zero.mpr (by linarith [(hs i).mp hi])

/--
The volume of a centered planar seminorm ball of positive radius scales as the square of the radius.
-/
theorem ballArea (p : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane) {r : ℝ} (hr : 0 < r) :
    volume (p.closedBall 0 r) = ENNReal.ofReal (r^2) * volume (p.closedBall 0 1) := by
  have he := p.smul_closedBall_zero (r := 1) (k := r) (by simpa using hr.ne')
  rw [Real.norm_eq_abs, abs_of_pos hr, mul_one] at he
  rw [← he, addHaar_smul_of_nonneg volume hr.le]
  simp [Module.finrank_prod]

/--
The volumes at the two adjusted radii bound the number of lattice sites in a closed seminorm ball, with the lower radius truncated at zero.
-/
theorem countBounds (p : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane) {d R : ℝ} (hd : 0 ≤ d) (hpos : 0 < R)
    (s : Finset _root_.AbcTwoNinths.Basic.Sites) (hs : ∀ i, i ∈ s ↔ p (_root_.AbcTwoNinths.Basic.lift i) ≤ d)
    (hR : (p _root_.AbcTwoNinths.Basic.e₁ + p _root_.AbcTwoNinths.Basic.e₂)/2 ≤ R) :
    ENNReal.ofReal ((max (d-R) 0)^2) * volume (p.closedBall 0 1) ≤ s.card ∧
    (s.card : ENNReal) ≤ ENNReal.ofReal ((d+R)^2) * volume (p.closedBall 0 1) := by
  obtain ⟨hl, hu⟩ := _root_.AbcTwoNinths.Basic.cellSandwich p d R s hs hR
  rw [← _root_.AbcTwoNinths.Basic.volumeCells]
  constructor
  · by_cases h : 0 < d-R
    · rw [max_eq_left h.le, ← _root_.AbcTwoNinths.Basic.ballArea p h]
      exact measure_mono hl
    · simp [max_eq_right (le_of_not_gt h)]
  · rw [← _root_.AbcTwoNinths.Basic.ballArea p (by linarith : 0 < d+R)]
    exact measure_mono hu

end
end Geometry

end AbcTwoNinths.Basic
