/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.IndependentPlaneMinor

/-!
# Plane Coordinate Box

The module bounds real plane coordinates by the height and encloses its height ball in a box. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.planeHeightBoxBound`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

/--
Cast both coordinates of an integer lattice point to the reals. This is used in the proof of Proposition 2.1 of the paper.
-/
def realPair (x : ℤ × ℤ) : ℝ × ℝ := (x.1, x.2)

/--
The absolute value of each logarithmically weighted coordinate is at most twice the plane height.
-/
theorem planeCoordLeTwiceHeight {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e v : ι → ℤ) (z : ℝ × ℝ) (j : ι) :
    |_root_.AbcTwoNinths.PolyCap.planeCoord q e v j z| ≤ 2 * _root_.AbcTwoNinths.PolyCap.planeHeight q e v z := by
  calc
    _ ≤ ∑ k, |_root_.AbcTwoNinths.PolyCap.planeCoord q e v k z| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (_root_.AbcTwoNinths.PolyCap.planeCoord q e v k z)) (Finset.mem_univ j)
    _ ≤ _ := by
      have h := (_root_.AbcTwoNinths.PolyCap.coordHeightBounds (fun k => _root_.AbcTwoNinths.PolyCap.planeCoord q e v k z)).1
      change _ ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v z at h
      linarith

/--
A nonzero coordinate minor puts the integer points of bounded plane height in a finite square. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem planeHeightBoxBound {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) {e v : ι → ℤ} {i j : ι}
    (hd : e i * v j - e j * v i ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℤ, ∀ x : ℤ × ℤ, _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) ≤ B →
      x ∈ (Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M) := by
  let D : ℝ := (e i : ℝ) * v j - (e j : ℝ) * v i
  have hD : D ≠ 0 := by dsimp [D]; exact_mod_cast hd
  let C : ℝ := 4 * B * (|(v j : ℝ)| + |(v i : ℝ)| + |(e i : ℝ)| + |(e j : ℝ)|) / |D|
  refine ⟨⌈C⌉, fun x hx => ?_⟩
  let u (k : ι) : ℝ := (x.1 : ℝ) * e k + (x.2 : ℝ) * v k
  have hu (k : ι) : |u k| ≤ 4 * B := by
    have hl : (1 / 2 : ℝ) ≤ log (q k : ℝ) := by
      have hk : (2 : ℝ) ≤ q k := by exact_mod_cast (hq k).two_le
      linarith [Real.log_two_gt_d9, log_le_log (by norm_num : (0 : ℝ) < 2) hk]
    have hb := (_root_.AbcTwoNinths.PolyCap.planeCoordLeTwiceHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) k).trans
      (mul_le_mul_of_nonneg_left hx (by norm_num))
    change |u k * log (q k : ℝ)| ≤ 2 * B at hb
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ log (q k : ℝ))] at hb
    linarith [mul_le_mul_of_nonneg_left hl (abs_nonneg (u k))]
  have hx1 : D * (x.1 : ℝ) = u i * v j - u j * v i := by dsimp [D,u]; ring
  have hx2 : D * (x.2 : ℝ) = u j * e i - u i * e j := by dsimp [D,u]; ring
  have aux (a b : ι) (c d : ℝ) {y : ℝ} (hy : D * y = u a * c - u b * d)
      (hs : |c| + |d| ≤ |(v j : ℝ)| + |(v i : ℝ)| + |(e i : ℝ)| + |(e j : ℝ)|) :
      |y| ≤ C := by
    apply (le_div_iff₀ (abs_pos.mpr hD)).2
    rw [mul_comm, ← abs_mul, hy]
    calc
      _ ≤ |u a * c| + |u b * d| := abs_sub _ _
      _ ≤ 4 * B * (|c| + |d|) := by
        rw [abs_mul, abs_mul, mul_add]
        gcongr
        · exact hu a
        · exact hu b
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have h1 := (aux i j (v j) (v i) hx1 (by have := abs_nonneg (e i : ℝ); have := abs_nonneg (e j : ℝ); linarith)).trans (Int.le_ceil C)
  have h2 := (aux j i (e i) (e j) hx2 (by have := abs_nonneg (v i : ℝ); have := abs_nonneg (v j : ℝ); linarith)).trans (Int.le_ceil C)
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨by exact_mod_cast abs_le.mp h1, by exact_mod_cast abs_le.mp h2⟩

end

end AbcTwoNinths.PolyCap
