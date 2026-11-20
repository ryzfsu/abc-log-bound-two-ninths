/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PrimitiveResidueVector

/-!
# Maximal Logarithmic Pivot

The module selects a pivot of maximal logarithmic weight and excludes a sufficiently short source line. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.existsPivot`
* `AbcTwoNinths.ExteriorE1.strictLineExclusion`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open scoped BigOperators

section

variable {ι : Type*} [Fintype ι]

/--
The signed exponent height is the larger of the weighted sums of the positive and negative parts. This is used in the proof of Proposition 3.1 of the paper.
-/
def signedHeight (a : ι → ℝ) (v : ι → ℤ) : ℝ :=
  max (∑ i, a i * max (v i : ℝ) 0) (∑ i, a i * max (-(v i : ℝ)) 0)

/--
The weighted sum of absolute exponents bounds the signed exponent height for nonnegative weights.
-/
theorem signedHeightLeWeightedAbs (a : ι → ℝ) (v : ι → ℤ)
    (ha : ∀ i, 0 ≤ a i) :
    _root_.AbcTwoNinths.ExteriorE1.signedHeight a v ≤ ∑ i, a i * |(v i : ℝ)| := by
  apply max_le <;> apply Finset.sum_le_sum <;> intro i _
  · exact mul_le_mul_of_nonneg_left
      (max_le (le_abs_self _) (abs_nonneg _)) (ha i)
  · exact mul_le_mul_of_nonneg_left
      (max_le (neg_le_abs _) (abs_nonneg _)) (ha i)

/--
A coordinate maximizing absolute exponent before and after scaling gives the pivot lower bound in terms of total weight and absolute scale. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem existsPivot [Nonempty ι] (a : ι → ℝ) (v w : ι → ℤ) (g : ℤ)
    (hg : g ≠ 0) (ha : ∀ i, 0 < a i) (hv : ∀ i, v i = g * w i)
    (H : ℝ) (hH : H ≤ ∑ i, a i * |(v i : ℝ)|) :
    ∃ r, (∀ i, |w i| ≤ |w r|) ∧ (∀ i, |v i| ≤ |v r|) ∧
      H / (|(g : ℝ)| * ∑ i, a i) ≤ |(w r : ℝ)| := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun i => |w i|)
    Finset.univ_nonempty
  have hw (i : ι) : |w i| ≤ |w r| := hr i (Finset.mem_univ i)
  have hW : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have hvabs (i : ι) : |(v i : ℝ)| = |(g : ℝ)| * |(w i : ℝ)| := by
    rw [hv i, Int.cast_mul, abs_mul]
  have hwr (i : ι) : |(w i : ℝ)| ≤ |(w r : ℝ)| := by exact_mod_cast hw i
  have hvr (i : ι) : |(v i : ℝ)| ≤ |(v r : ℝ)| := by
    rw [hvabs, hvabs]
    exact mul_le_mul_of_nonneg_left (hwr i) (abs_nonneg _)
  refine ⟨r, hw, fun i => ?_, (div_le_iff₀ (mul_pos (abs_pos.mpr hgr) hW)).2 ?_⟩
  · exact_mod_cast hvr i
  calc
    H ≤ ∑ i, a i * |(v i : ℝ)| := hH
    _ ≤ ∑ i, a i * |(v r : ℝ)| :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvr i) (ha i).le
    _ = |(w r : ℝ)| * (|(g : ℝ)| * ∑ i, a i) := by
      rw [← Finset.sum_mul, hvabs]
      ring

omit [Fintype ι] in
/--
A nonzero integer point in the strict pivot strip of a primitive vector lies outside the real line through any integer multiple of that vector. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem strictLineExclusion (v w u : ι → ℤ) (g : ℤ)
    (hv : ∀ i, v i = g * w i)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w)
    (r : ι) (hu : u ≠ 0) (hstrip : |u r| < |w r|) :
    ¬ ∃ t : ℝ, ∀ i, (u i : ℝ) = t * (v i : ℝ) := by
  rintro ⟨t, ht⟩
  have hwr : w r ≠ 0 := by
    intro hz
    exact (not_lt_of_ge (abs_nonneg (u r))) (by simpa [hz] using hstrip)
  have hwrR : (w r : ℝ) ≠ 0 := by exact_mod_cast hwr
  have hreal (i : ι) : (u i : ℝ) = (t * (g : ℝ)) * (w i : ℝ) := by
    rw [ht i, hv i, Int.cast_mul, mul_assoc]
  let q : ℚ := (u r : ℚ) / (w r : ℚ)
  have hq : (q : ℝ) = t * (g : ℝ) := by
    simp only [q, Rat.cast_div, Rat.cast_intCast]
    exact (div_eq_iff hwrR).2 (hreal r)
  have hprop (i : ι) : (u i : ℚ) = q * (w i : ℚ) := by
    have hi : (u i : ℝ) = (q : ℝ) * (w i : ℝ) := by rw [hq, ← hreal i]
    exact_mod_cast hi
  have hn := _root_.AbcTwoNinths.Basic.integralOfPrimitiveProportional
    (show w ∈ (⊤ : AddSubgroup (ι → ℤ)) from trivial)
    (show u ∈ (⊤ : AddSubgroup (ι → ℤ)) from trivial) hprim q hprop
  have huEq (i : ι) : u i = q.num * w i := by
    have hi := hprop i
    rw [hn] at hi
    exact_mod_cast hi
  have hnz : q.num ≠ 0 := by
    intro hz
    apply hu
    funext i
    simp [huEq i, hz]
  have hnum : 1 ≤ |q.num| := by have := abs_pos.mpr hnz; omega
  have hge := mul_le_mul_of_nonneg_right hnum (abs_nonneg (w r))
  rw [one_mul, ← abs_mul, ← huEq r] at hge
  exact (not_lt_of_ge hge) hstrip

end

end AbcTwoNinths.ExteriorE1
