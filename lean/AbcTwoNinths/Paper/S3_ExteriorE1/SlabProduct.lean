/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SlabBudget

/-!
# Slab Product

The module bounds a product of slab dimensions by a power of their sum. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.prodLePowOfSumLe`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
If the sum of a positive finite family is at most its cardinality times B > 0, its product is at most B to that cardinality. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem prodLePowOfSumLe {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) (B : ℝ) (hB : 0 < B)
    (hs : ∑ i, f i ≤ (Fintype.card ι : ℝ) * B) :
    ∏ i, f i ≤ B ^ Fintype.card ι := by
  classical
  have hg (i : ι) : 0 < f i / B := div_pos (hf i) hB
  have hsum : (∑ i, (f i / B - 1)) ≤ 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact sub_nonpos.mpr ((div_le_iff₀ hB).mpr hs)
  have hlog : Real.log (∏ i, f i / B) ≤ 0 := by
    rw [Real.log_prod (fun i _ => (hg i).ne')]
    exact (Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hg i)).trans hsum
  have hpos : 0 < ∏ i, f i / B := Finset.prod_pos fun i _ => hg i
  have hone : (∏ i, f i / B) ≤ 1 := by
    rw [← Real.exp_log hpos, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hlog
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] at hone
  exact (div_le_one (pow_pos hB _)).mp hone

end

end AbcTwoNinths.ExteriorE1
