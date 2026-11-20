/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SlabProduct

/-!
# Strict Capacity

Ceiling bounds on the coordinate and logarithmic subdivisions give strictly fewer slab cells than
sample points. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.strictCapacity`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
When the prescribed thickness is less than the scale, the rounded slab capacity is strictly smaller than the mass. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem strictCapacity {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (T W m : ℝ)
    (hT : 0 < T) (hW : 0 ≤ W) (hm : 0 < m) (hs : ∑ i, a i ≤ W) :
    let d := Fintype.card ι
    let B := 1 + W / T
    let ε := (3 * T / m) * B ^ d
    ε < T → (⌈T / ε⌉₊ : ℝ) *
      (∏ i, (⌈(d : ℝ) * a i / T⌉₊ : ℝ)) < m := by
  classical
  let d := Fintype.card ι
  let B : ℝ := 1 + W / T
  let N : ι → ℕ := fun i => ⌈(d : ℝ) * a i / T⌉₊
  let ε := (3 * T / m) * B ^ d
  change ε < T → (⌈T / ε⌉₊ : ℝ) * (∏ i, (N i : ℝ)) < m
  intro heT
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < ε := by dsimp [ε]; positivity
  have hN (i : ι) : 0 < (N i : ℝ) := by
    exact_mod_cast (_root_.AbcTwoNinths.ExteriorE1.ceilCapacity a ha T hT).1 i
  have hprod : (∏ i, (N i : ℝ)) ≤ B ^ d := by
    apply _root_.AbcTwoNinths.ExteriorE1.prodLePowOfSumLe _ hN B hB
    calc
      (∑ i, (N i : ℝ)) ≤ ∑ i, ((d : ℝ) * a i / T + 1) :=
        Finset.sum_le_sum fun i _ => (Nat.ceil_lt_add_one
          (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (ha i).le) hT.le)).le
      _ = (d : ℝ) * ((∑ i, a i) / T + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
        simp [d, mul_add, mul_div_assoc]
      _ ≤ (d : ℝ) * B := by
        gcongr
        dsimp [B]
        linarith [div_le_div_of_nonneg_right hs hT.le]
  have hratio : 1 < T / ε := (one_lt_div he).mpr heT
  have hceil : (⌈T / ε⌉₊ : ℝ) < 2 * (T / ε) := by
    linarith [Nat.ceil_lt_add_one (show 0 ≤ T / ε by positivity)]
  calc
    (⌈T / ε⌉₊ : ℝ) * (∏ i, (N i : ℝ)) ≤ (⌈T / ε⌉₊ : ℝ) * B ^ d :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ < (2 * (T / ε)) * B ^ d :=
      mul_lt_mul_of_pos_right hceil (pow_pos hB _)
    _ = (2 / 3) * m := by
      dsimp [ε]
      field_simp [hT.ne', hm.ne', (pow_pos hB d).ne']
    _ < m := by linarith

end

end AbcTwoNinths.ExteriorE1
