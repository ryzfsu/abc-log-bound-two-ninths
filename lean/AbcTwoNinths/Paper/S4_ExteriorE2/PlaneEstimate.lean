/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Plane Estimate

The module bounds transverse coordinates and finds a shortest integer vector with a unimodular companion. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.transverseCoeffBound`
* `AbcTwoNinths.ExteriorE2.determinantHeightBound`
* `AbcTwoNinths.ExteriorE2.roundedHeightBound`
* `AbcTwoNinths.ExteriorE2.existsShortestIntegerVector`
* `AbcTwoNinths.ExteriorE2.gcdEqOneOfShortest`
* `AbcTwoNinths.ExteriorE2.existsUnimodularCompanion`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/--
The absolute transverse coefficient times a lower bound on line distance is at most the seminorm. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem transverseCoeffBound (f : Seminorm ℝ E) {u w : E}
    {d : ℝ} (hmin : ∀ s : ℝ, d ≤ f (w - s • u)) (a b : ℝ) :
    |b| * d ≤ f (a • u + b • w) := by
  by_cases hb : b = 0
  · simp [hb, apply_nonneg]
  have h := mul_le_mul_of_nonneg_left (hmin (-a / b)) (abs_nonneg b)
  rw [← Real.norm_eq_abs, ← map_smul_eq_mul] at h
  convert h using 1
  congr 1
  rw [smul_sub, smul_smul]
  have he : b * (-a / b) = -a := by field_simp
  rw [he, neg_smul, sub_neg_eq_add, add_comm]

/--
The absolute coordinate determinant times the first height and transverse distance is at most twice the product of the two heights. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem determinantHeightBound (f : Seminorm ℝ E) {u w : E}
    {d : ℝ} (hd : 0 ≤ d) (hmin : ∀ s : ℝ, d ≤ f (w - s • u))
    (a b c e : ℝ) :
    |a * e - b * c| * f u * d ≤
      2 * f (a • u + b • w) * f (c • u + e • w) := by
  let x := a • u + b • w
  let y := c • u + e • w
  have hdet : e • x + (-b) • y = (a * e - b * c) • u := by
    dsimp [x, y]
    module
  have h := map_add_le_add f (e • x) ((-b) • y)
  rw [hdet, map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg] at h
  have ht₁ := _root_.AbcTwoNinths.ExteriorE2.transverseCoeffBound f hmin a b
  have ht₂ := _root_.AbcTwoNinths.ExteriorE2.transverseCoeffBound f hmin c e
  change |b| * d ≤ f x at ht₁
  change |e| * d ≤ f y at ht₂
  change _ ≤ 2 * f x * f y
  calc
    |a * e - b * c| * f u * d ≤ (|e| * f x + |b| * f y) * d :=
      mul_le_mul_of_nonneg_right h hd
    _ = (|e| * d) * f x + (|b| * d) * f y := by ring
    _ ≤ f y * f x + f x * f y :=
      add_le_add (mul_le_mul_of_nonneg_right ht₂ (apply_nonneg f x))
        (mul_le_mul_of_nonneg_right ht₁ (apply_nonneg f y))
    _ = 2 * f x * f y := by ring

/--
Rounding a minimizing line coefficient gives height at most twice the attained distance under the shortest-vector inequality. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem roundedHeightBound (f : Seminorm ℝ E) (u w : E) (q d : ℝ)
    (hq : f (w - q • u) = d)
    (hshort : f u ≤ f (w - (round q : ℝ) • u)) :
    f (w - (round q : ℝ) • u) ≤ 2 * d := by
  let m : ℝ := (round q : ℤ)
  have h := map_add_le_add f (w - q • u) ((q - m) • u)
  rw [show w - q • u + (q - m) • u = w - m • u by module,
    hq, map_smul_eq_mul, Real.norm_eq_abs] at h
  have hh := mul_le_mul_of_nonneg_right (abs_sub_round q) (apply_nonneg f u)
  change |q - m| * f u ≤ _ at hh
  change f u ≤ f (w - m • u) at hshort
  change f (w - m • u) ≤ _
  linarith

/--
A subgroup containing a nonzero vector has a shortest nonzero vector when positive coordinate weights are bounded by height. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsShortestIntegerVector {I : Type*} [Fintype I]
    (K : AddSubgroup (I → ℤ)) (F : (I → ℤ) → ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ z i, w i * |(z i : ℝ)| ≤ F z)
    {v : I → ℤ} (hv : v ∈ K) (hv0 : v ≠ 0) :
    ∃ u ∈ K, u ≠ 0 ∧ ∀ z ∈ K, z ≠ 0 → F u ≤ F z := by
  classical
  let S : Set (I → ℤ) := {z | z ∈ K ∧ z ≠ 0 ∧ F z ≤ F v}
  let N (i : I) : ℤ := ⌈F v / w i⌉
  let inj (z : S) (i : I) : Set.Icc (-N i) (N i) := ⟨z.val i, by
    have hb : |(z.val i : ℝ)| ≤ F v / w i := (le_div_iff₀ (hw i)).2 (by
      rw [mul_comm]
      exact (hcoord z.val i).trans z.property.2.2)
    have hN := hb.trans (Int.le_ceil (F v / w i))
    change -(N i) ≤ z.val i ∧ z.val i ≤ N i
    exact_mod_cast abs_le.mp hN⟩
  have hfin : Set.Finite S := by
    have hinj : Function.Injective inj := fun x y h =>
      Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
    let _ : Finite S := Finite.of_injective inj hinj
    exact Set.toFinite S
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image S F hfin ⟨v, hv, hv0, le_rfl⟩
  refine ⟨u, hu.1, hu.2.1, fun z hz hz0 => ?_⟩
  by_cases h : F z ≤ F v
  · exact hmin z ⟨hz, hz0, h⟩
  · exact hu.2.2.trans (le_of_not_ge h)

/--
A shortest nonzero vector for a positive homogeneous height has coprime coefficients in any representation by two subgroup vectors. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem gcdEqOneOfShortest {A : Type*} [AddCommGroup A]
    (K : AddSubgroup A) (F : A → ℝ)
    (hscale : ∀ (n : ℤ) (z : A), F (n • z) = |(n : ℝ)| * F z)
    {v b u : A} (hv : v ∈ K) (hb : b ∈ K) (hu : u ≠ 0)
    (hpos : ∀ z, z ≠ 0 → 0 < F z)
    (hmin : ∀ z ∈ K, z ≠ 0 → F u ≤ F z)
    (a c : ℤ) (h : u = a • v + c • b) : a.gcd c = 1 := by
  have ha : a ≠ 0 ∨ c ≠ 0 := by
    by_contra! hn
    exact hu (by rw [h, hn.1, hn.2]; simp)
  let g : ℕ := a.gcd c
  have hg : 0 < g := by
    rcases ha with ha | hc
    · exact Int.gcd_pos_of_ne_zero_left c ha
    · exact Int.gcd_pos_of_ne_zero_right a hc
  obtain ⟨p, hp⟩ := Int.gcd_dvd_left a c
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right a c
  let z := p • v + q • b
  have hgz : u = (g : ℤ) • z := calc
    u = a • v + c • b := h
    _ = ((g : ℤ) * p) • v + ((g : ℤ) * q) • b :=
      congrArg₂ (· + ·) (congrArg (· • v) hp) (congrArg (· • b) hq)
    _ = (g : ℤ) • z := by simp [z, smul_add, smul_smul]
  have hz : z ∈ K := K.add_mem (K.zsmul_mem hv p) (K.zsmul_mem hb q)
  have hz0 : z ≠ 0 := fun h0 => hu (by rw [hgz, h0, smul_zero])
  have hh : F u = (g : ℝ) * F z := by rw [hgz, hscale, Int.cast_natCast, abs_of_nonneg (by positivity)]
  have hg1 : (g : ℝ) ≤ 1 :=
    le_of_mul_le_mul_right (by simpa [hh] using hmin z hz hz0) (hpos z hz0)
  change g = 1
  exact le_antisymm (by exact_mod_cast hg1) (by omega)

/--
A pair of coprime integer coordinates extends to a determinant-one matrix. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsUnimodularCompanion (a c : ℤ) (h : a.gcd c = 1) :
    ∃ b d : ℤ, a * d - c * b = 1 := by
  have hb := Int.gcd_eq_gcd_ab a c
  rw [h] at hb
  exact ⟨-a.gcdB c, a.gcdA c, by simpa only [mul_neg, sub_neg_eq_add, Int.natCast_one] using hb.symm⟩

end

end AbcTwoNinths.ExteriorE2
