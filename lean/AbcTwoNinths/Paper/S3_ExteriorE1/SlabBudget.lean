/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.IntegerSlab

/-!
# Slab Budget

The module bounds the number of bins available in the slab using ceiling estimates. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.ceilCapacity`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Ceiling subdivision gives positive counts, coordinate widths at most T divided by the dimension, and total width at most T. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem ceilCapacity {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (T : ℝ) (hT : 0 < T) :
    let d := Fintype.card ι
    let N := fun i => ⌈(d : ℝ) * a i / T⌉₊
    (∀ i, 0 < N i) ∧ (∀ i, a i / N i ≤ T / d) ∧ (∑ i, a i / N i) ≤ T := by
  classical
  dsimp only
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  let N : ι → ℕ := fun i => ⌈(Fintype.card ι : ℝ) * a i / T⌉₊
  have hN (i : ι) : 0 < N i := Nat.ceil_pos.mpr (div_pos (mul_pos hd (ha i)) hT)
  have hcoord (i : ι) : a i / N i ≤ T / Fintype.card ι := by
    have hNR : (0 : ℝ) < N i := by exact_mod_cast hN i
    have h := (div_le_iff₀ hT).mp (Nat.le_ceil ((Fintype.card ι : ℝ) * a i / T))
    exact (div_le_div_iff₀ hNR hd).mpr (by simpa [N, mul_comm] using h)
  refine ⟨hN, hcoord, ?_⟩
  calc
    (∑ i, a i / N i) ≤ ∑ _ : ι, T / Fintype.card ι :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = T := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hd.ne']

end

end AbcTwoNinths.ExteriorE1
