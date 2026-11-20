/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationParameterInequalities

/-!
# Interpolation Grid Dimensions

The module checks the sharp and weighted grid dimensions used in the real interpolation estimate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.certParamBounds`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

private theorem largeGridSide {r a b D L j : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : r ≤ b) (hD : 4 ≤ D)
    (hL : 13 ≤ L) (hj : 640 ≤ j)
    (hX : 160 * a * b * D / r ^ 2 ≤ (641 / 640 : ℝ) * j) :
    91 ≤ ⌊Real.sqrt (L * j * b / a)⌋₊ := by
  have hb0 := hr.trans_le hb
  have hsq : r ^ 2 ≤ b ^ 2 := by nlinarith
  have hX' := (div_le_iff₀ (sq_pos_of_pos hr)).mp hX
  have h := mul_le_mul_of_nonneg_right hX' hb0.le
  have h₁ := mul_le_mul_of_nonneg_right hD (show 0 ≤ 160 * a * b ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 640 * a by positivity)
  have h₃ : r ^ 2 * (640 * a) ≤ r ^ 2 * ((641 / 640 : ℝ) * (j * b)) := by
    nlinarith only [h, h₁, h₂]
  have h₄ := le_of_mul_le_mul_left h₃ (sq_pos_of_pos hr)
  have h₅ := mul_le_mul_of_nonneg_right hL (show 0 ≤ j * b by positivity)
  have hs : (91 : ℝ) ^ 2 ≤ L * j * b / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [h₄, h₅, ha]
  exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by exact_mod_cast Real.le_sqrt_of_sq_le hs)

private theorem weightedGridSide {a b L j : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 ≤ L) (hj : 640 ≤ j) :
    ((⌊Real.sqrt (L * b / a)⌋₊ : ℝ) +
      (⌊Real.sqrt (L * j * b / a)⌋₊ : ℝ)) * a ≤
      (26 / 25 : ℝ) * Real.sqrt (L * j * a * b) := by
  have hj0 : 0 ≤ j := by linarith
  have heq (t : ℝ) (ht : 0 ≤ t) :
      Real.sqrt (t * b / a) * a = Real.sqrt (t * a * b) := by
    calc
      _ = Real.sqrt (t * b / a) * Real.sqrt (a ^ 2) := by rw [Real.sqrt_sq ha.le]
      _ = _ := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp
  have hf := mul_le_mul_of_nonneg_right
    (Nat.floor_le (Real.sqrt_nonneg (L * b / a))) ha.le
  have hg := mul_le_mul_of_nonneg_right
    (Nat.floor_le (Real.sqrt_nonneg (L * j * b / a))) ha.le
  rw [heq _ hL] at hf
  rw [heq _ (mul_nonneg hL hj0)] at hg
  have hj25 : (25 : ℝ) ≤ Real.sqrt j := Real.le_sqrt_of_sq_le (by linarith)
  have he : Real.sqrt j * Real.sqrt (L * a * b) = Real.sqrt (L * j * a * b) := by
    rw [← Real.sqrt_mul hj0]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hj25 (Real.sqrt_nonneg (L * a * b))
  rw [he] at hm
  linarith only [hf, hg, hm]

/--
Bound the square-root grid scale by the product of the two weights and the dimension parameter divided by the radius.
-/
theorem certSharpGrid {r a b D L j : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) (hD : 4 ≤ D)
    (hL : L ≤ (13 / 4 : ℝ) * D) (hj : 640 ≤ j)
    (hjU : j ≤ 160 * a * b * D / r ^ 2) :
    Real.sqrt (L * j * a * b) ≤ Real.sqrt 520 * (a * b * D / r) := by
  have hj0 : 0 ≤ j := by linarith
  have hD0 : 0 ≤ D := by linarith
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul hL hjU hj0 (by positivity)) (show 0 ≤ a * b by positivity)
  have h' : L * j * a * b ≤ 520 * (a * b * D / r) ^ 2 := by
    convert h using 1 <;> ring
  simpa only [Real.sqrt_mul (show (0 : ℝ) ≤ 520 by norm_num),
    Real.sqrt_sq (show 0 ≤ a * b * D / r by positivity)] using Real.sqrt_le_sqrt h'

/--
The two rounded rectangles satisfy the dimension, cardinality and weighted side bounds for real interpolation. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem certParamBounds {r a b D : ℝ}
    (hr : 1 ≤ r) (ha : r ≤ a) (hb : r ≤ b) (hD : 4 ≤ D) :
    let X := 160 * a * b * D / r ^ 2
    let L := ⌊3 * D⌋₊ + 1
    let J := ⌊X⌋₊
    let K := J + 1
    let N := K * L
    let R₁ := ⌊Real.sqrt ((L : ℝ) * b / a)⌋₊
    let S₁ := ⌊Real.sqrt ((L : ℝ) * a / b)⌋₊
    let R₂ := ⌊Real.sqrt ((L : ℝ) * J * b / a)⌋₊
    let S₂ := ⌊Real.sqrt ((L : ℝ) * J * a / b)⌋₊
    let R := R₁ + R₂
    let S := S₁ + S₂
    13 ≤ L ∧ (11 / 4 : ℝ) * D ≤ (L : ℝ) - 1 ∧ 3 * D < L ∧
    (L : ℝ) ≤ (13 / 4 : ℝ) * D ∧ (L : ℝ) ≤ (13 / 12 : ℝ) * ((L : ℝ) - 1) ∧
    640 ≤ J ∧ 641 ≤ K ∧ X ≤ (641 / 640 : ℝ) * J ∧
    8333 ≤ N ∧ (N : ℝ) ≤ (8333 / 16 : ℝ) * a * b * D ^ 2 / r ^ 2 ∧
    L ≤ (R₁ + 1) * (S₁ + 1) ∧ L * J < (R₂ + 1) * (S₂ + 1) ∧
    91 ≤ R₂ ∧ 91 ≤ S₂ ∧ 1 ≤ R + S ∧
    (R : ℝ) * a + (S : ℝ) * b ≤ (5929 / 20000 : ℝ) * r * K ∧
    (R₂ : ℝ) * a + (S₂ : ℝ) * b ≤ 12 * a * b * D ^ 2 / r ∧
    (S : ℝ) ≤ (3 / 20 : ℝ) * K ∧ 2 * (L - 1) * S ≤ N := by
  intro X L J K N R₁ S₁ R₂ S₂ R S
  have hr0 : 0 < r := by linarith
  have ha0 := hr0.trans_le ha
  have hb0 := hr0.trans_le hb
  have hD0 : 0 ≤ D := by linarith
  have hab : r ^ 2 ≤ a * b := by rw [sq]; exact mul_le_mul ha hb hr0.le ha0.le
  have hX : 640 ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ (sq_pos_of_pos hr0)).mpr
    nlinarith only [mul_le_mul hD hab (sq_nonneg r) hD0]
  obtain ⟨hL, hJ, hN, hDL, hL₁, hLD, hXJ, hNU⟩ := _root_.AbcTwoNinths.ExteriorE1.certFloorDimensions hD hX
  have hJr : (640 : ℝ) ≤ J := by exact_mod_cast hJ
  have hLr : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hJK : X < K := by simpa [K, J] using Nat.lt_floor_add_one X
  have hX' : 160 * b * a * D / r ^ 2 ≤ (641 / 640 : ℝ) * J := by
    convert hXJ using 1
    simp only [X]
    ring
  have hR₂ : 91 ≤ R₂ := largeGridSide hr0 ha0 hb hD hLr hJr hXJ
  have hS₂ : 91 ≤ S₂ := largeGridSide hr0 hb0 ha hD hLr hJr hX'
  have hr1 : L < (R₁ + 1) * (S₁ + 1) := by
    exact_mod_cast _root_.AbcTwoNinths.ExteriorE1.certRectangleCard hL0 ha0 hb0
  have hr2 : L * J < (R₂ + 1) * (S₂ + 1) := by
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one, R₂, S₂] using
      _root_.AbcTwoNinths.ExteriorE1.certRectangleCard (show 0 ≤ (L : ℝ) * J by positivity) ha0 hb0
  have hJU : (J : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hR : (R : ℝ) * a ≤ (26 / 25 : ℝ) * Real.sqrt ((L : ℝ) * J * a * b) := by
    simpa [R, R₁, R₂, Nat.cast_add] using weightedGridSide ha0 hb0 hL0 hJr
  have hS : (S : ℝ) * b ≤ (26 / 25 : ℝ) * Real.sqrt ((L : ℝ) * J * a * b) := by
    simpa [S, S₁, S₂, Nat.cast_add, mul_assoc, mul_comm b a] using
      weightedGridSide hb0 ha0 hL0 hJr
  have hroot : Real.sqrt ((L : ℝ) * J * a * b) ≤ Real.sqrt 520 * (a * b * D / r) :=
    _root_.AbcTwoNinths.ExteriorE1.certSharpGrid hr0 ha0 hb0 hD hLD hJr hJU
  have h520 : Real.sqrt 520 ≤ (5929 / 260 : ℝ) :=
    (Real.sqrt_le_iff).mpr (by norm_num)
  have hhK : a * b * D / r ≤ r * K / 160 := by
    have h := mul_le_mul_of_nonneg_right hJK.le (show 0 ≤ r / 160 by positivity)
    calc
      _ = X * (r / 160) := by dsimp [X]; field_simp
      _ ≤ _ := h
      _ = _ := by ring
  have hsharp : Real.sqrt ((L : ℝ) * J * a * b) ≤ (5929 / 260 : ℝ) * (r * K / 160) :=
    hroot.trans (mul_le_mul h520 hhK (by positivity) (by norm_num))
  have hSK : (S : ℝ) ≤ (3 / 20 : ℝ) * K := by
    apply le_of_mul_le_mul_right _ hr0
    have h := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ S by positivity)
    nlinarith only [h, hS, hsharp, show 0 ≤ r * K by positivity]
  have hpert : 2 * (L - 1) * S ≤ N := by
    have hS' : 2 * (S : ℝ) ≤ K := by linarith [show (0 : ℝ) ≤ K by positivity]
    have h := mul_le_mul hS' (show ((L - 1 : ℕ) : ℝ) ≤ L by exact_mod_cast Nat.sub_le L 1)
      (show 0 ≤ ((L - 1 : ℕ) : ℝ) by positivity) (show 0 ≤ (K : ℝ) by positivity)
    exact_mod_cast (show (2 : ℝ) * ((L - 1 : ℕ) : ℝ) * S ≤ (K : ℝ) * L by linarith only [h])
  refine ⟨hL, ?_, ?_, hLD, ?_, hJ, ?_, hXJ, hN, ?_, hr1.le, hr2, hR₂, hS₂, ?_, ?_, ?_, hSK, hpert⟩
  · simpa [L] using hDL
  · simpa [L] using Nat.lt_floor_add_one (3 * D)
  · simpa [L] using hL₁
  · change 641 ≤ J + 1
    change 640 ≤ J at hJ
    omega
  · apply hNU.trans
    dsimp [X]
    apply le_of_eq
    ring
  · dsimp [R, S]
    omega
  · nlinarith only [hR, hS, hsharp]
  · have hi := mul_le_mul_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg ((L : ℝ) * J * b / a))) ha0.le
    have hj := mul_le_mul_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg ((L : ℝ) * J * a / b))) hb0.le
    have he (u v t : ℝ) (hu : 0 < u) (hv : 0 < v) (ht : 0 ≤ t) :
        Real.sqrt (t * v / u) * u = Real.sqrt (t * u * v) := by
      calc
        _ = Real.sqrt (t * v / u) * Real.sqrt (u ^ 2) := by rw [Real.sqrt_sq hu.le]
        _ = _ := by rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [he a b _ ha0 hb0 (by positivity)] at hi
    rw [he b a _ hb0 ha0 (by positivity), show (L : ℝ) * J * b * a = L * J * a * b by ring] at hj
    have hs24 : Real.sqrt 520 ≤ (24 : ℝ) := (Real.sqrt_le_iff).mpr (by norm_num)
    have hp := mul_le_mul_of_nonneg_right hs24 (show 0 ≤ a * b * D / r by positivity)
    have heq : D * (a * b * D / r) = a * b * D ^ 2 / r := by ring
    have hlast := mul_le_mul_of_nonneg_right hD (show 0 ≤ a * b * D / r by positivity)
    rw [heq] at hlast
    rw [show 12 * a * b * D ^ 2 / r = 12 * (a * b * D ^ 2 / r) by ring]
    change (↑⌊Real.sqrt ((L : ℝ) * J * b / a)⌋₊ : ℝ) * a +
      (↑⌊Real.sqrt ((L : ℝ) * J * a / b)⌋₊ : ℝ) * b ≤ _
    nlinarith only [hi, hj, hroot, hp, hlast]

end

end AbcTwoNinths.ExteriorE1
