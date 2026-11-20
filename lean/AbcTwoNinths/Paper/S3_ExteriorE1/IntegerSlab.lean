/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SlabEuclidean
public import AbcTwoNinths.Paper.S3_ExteriorE1.MaximalLogarithmicPivot

/-!
# Integer Slab

The integer slab lemma produces a nonzero exponent vector outside the original line, with bounded
projected coordinates and a small weighted sum of those coordinates. This supports Proposition 3.1
of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.integerSlab`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- With fewer cells than positive pivot residues, a primitive integer vector admits
an integer vector outside its real span whose weighted coordinate errors and summed
error satisfy the prescribed slab bounds. -/
theorem integerSlab {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (w : ι → ℤ)
    (hm : 0 < w r) (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w)
    [Nonempty {i : ι // i ≠ r}]
    (N : {i : ι // i ≠ r} → ℕ) (hN : ∀ i, 0 < N i) {M : ℕ} (hM : 0 < M)
    (a : {i : ι // i ≠ r} → ℝ) (ha : ∀ i, 0 < a i) (T : ℝ) (hT : 0 < T)
    (hbudget : (∑ i, a i / N i) ≤ T)
    (hcard : M * (∏ i, N i) < (w r).toNat) :
    ∃ u : ι → ℤ, u ≠ 0 ∧ |u r| < w r ∧
      (∀ i : {i : ι // i ≠ r},
        |a i * ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))| < a i / N i) ∧
      |∑ i : {i : ι // i ≠ r},
        a i * ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))| < T / M ∧
      ¬ ∃ s : ℝ, ∀ i, (u i : ℝ) = s * (w i : ℝ) := by
  classical
  let m := (w r).toNat
  let z (k : Fin m) (i : {i : ι // i ≠ r}) : ℝ :=
    (((k.val : ℤ) * w i.val % w r : ℤ) : ℝ) / (w r : ℝ)
  have hz (k : Fin m) (i : {i : ι // i ≠ r}) := _root_.AbcTwoNinths.ExteriorE1.normalizedEmod (w r) (k.val * w i.val) hm
  obtain ⟨k, l, hkl, hco, hslab⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.slabCollision N hN hM z (fun k i => (hz k i).1) (fun k i => (hz k i).2)
      a ha T hT hbudget hcard
  let u (i : ι) : ℤ := if i = r then (l.val : ℤ) - k.val
    else (l.val : ℤ) * w i / w r - (k.val : ℤ) * w i / w r
  have hur : u r = (l.val : ℤ) - k.val := by simp [u]
  have hcast : (m : ℤ) = w r := Int.toNat_of_nonneg hm.le
  have hk : (k.val : ℤ) < w r := by
    rw [← hcast]; exact_mod_cast k.isLt
  have hl : (l.val : ℤ) < w r := by
    rw [← hcast]; exact_mod_cast l.isLt
  have hrs : |u r| < w r := by
    rw [hur]
    exact abs_lt.mpr ⟨by omega, by omega⟩
  have hne : u ≠ 0 := by
    intro hu
    have h := congrFun hu r
    change u r = 0 at h
    rw [hur] at h
    apply hkl
    apply Fin.ext
    omega
  have hres (i : {i : ι // i ≠ r}) :
      (u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ) = z k i - z l i := by
    have h1 := _root_.AbcTwoNinths.ExteriorE1.residualEdiv (w r) ((l.val : ℤ) * w i.val) hm
    have h2 := _root_.AbcTwoNinths.ExteriorE1.residualEdiv (w r) ((k.val : ℤ) * w i.val) hm
    simp only [Int.cast_mul] at h1 h2
    have hu : u i.val =
        (l.val : ℤ) * w i.val / w r - (k.val : ℤ) * w i.val / w r := ite_eq_right i.property
    rw [hu, hur, Int.cast_sub, Int.cast_sub]
    dsimp [z]
    linear_combination h1 - h2
  refine ⟨u, hne, hrs, fun i => by rw [hres]; exact hco i, by simpa only [hres] using hslab, ?_⟩
  exact _root_.AbcTwoNinths.ExteriorE1.strictLineExclusion w w u 1 (by simp) hprim r hne
    (by rwa [abs_of_pos hm])

end

end AbcTwoNinths.ExteriorE1
