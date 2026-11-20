/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.UnitIntervalBins

/-!
# Slab Collision

The module uses a collision between slab bins to control the difference of two projected points. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.slabCollision`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- A subdivided unit box with more point labels than cells contains two labels whose
weighted coordinate differences are below `a i / N i` and whose sum has absolute value
below `T / M`. -/
theorem slabCollision {ι : Type*} [Fintype ι] [Nonempty ι] {m M : ℕ}
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (hM : 0 < M) (z : Fin m → ι → ℝ)
    (hz₀ : ∀ k i, 0 ≤ z k i) (hz₁ : ∀ k i, z k i < 1)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (T : ℝ) (hT : 0 < T)
    (hbudget : (∑ i, a i / N i) ≤ T)
    (hcard : M * (∏ i, N i) < m) :
    ∃ k l : Fin m, k ≠ l ∧
      (∀ i, |a i * (z k i - z l i)| < a i / N i) ∧
      |∑ i, a i * (z k i - z l i)| < T / M := by
  classical
  let b (k : Fin m) (i : ι) := _root_.AbcTwoNinths.Basic.slabBin (N i) (z k i) (hz₀ k i) (hz₁ k i) (hN i)
  let e (k : Fin m) (i : ι) := z k i - ((b k i).val : ℝ) / N i
  have he (k : Fin m) (i : ι) : 0 ≤ e k i ∧ e k i < 1 / N i :=
    _root_.AbcTwoNinths.Basic.slabBinResidual _ _ _ _ _
  let R (k : Fin m) := ∑ i, a i * e k i
  have hR₀ (k : Fin m) : 0 ≤ R k :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (he k i).1
  have hR₁ (k : Fin m) : R k < T := by
    apply lt_of_lt_of_le (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_) hbudget
    intro i _
    simpa only [mul_one_div] using mul_lt_mul_of_pos_left (he k i).2 (ha i)
  have hq₀ (k : Fin m) : 0 ≤ R k / T := div_nonneg (hR₀ k) hT.le
  have hq₁ (k : Fin m) : R k / T < 1 := (div_lt_one hT).2 (hR₁ k)
  let B (k : Fin m) := _root_.AbcTwoNinths.Basic.slabBin M (R k / T) (hq₀ k) (hq₁ k) hM
  let φ (k : Fin m) : Fin M × (∀ i, Fin (N i)) := (B k, b k)
  have hc : Fintype.card (Fin M × (∀ i, Fin (N i))) < Fintype.card (Fin m) := by
    simpa [Fintype.card_prod, Fintype.card_pi] using hcard
  obtain ⟨k, l, hkl, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hc
  have hb : b k = b l := congrArg Prod.snd hφ
  have hB : B k = B l := congrArg Prod.fst hφ
  have hdiff (i : ι) : z k i - z l i = e k i - e l i := by
    dsimp only [e]
    rw [congrFun hb i]
    ring
  refine ⟨k, l, hkl, ?_, ?_⟩
  · intro i
    rw [hdiff, abs_mul, abs_of_pos (ha i), ← mul_one_div]
    apply mul_lt_mul_of_pos_left _ (ha i)
    apply abs_lt.mpr
    constructor <;> linarith [(he k i).1, (he k i).2, (he l i).1, (he l i).2]
  · have hsum : (∑ i, a i * (z k i - z l i)) = R k - R l := by
      simp only [R, hdiff, mul_sub, Finset.sum_sub_distrib]
    have hk := _root_.AbcTwoNinths.Basic.slabBinResidual M (R k / T) (hq₀ k) (hq₁ k) hM
    have hl := _root_.AbcTwoNinths.Basic.slabBinResidual M (R l / T) (hq₀ l) (hq₁ l) hM
    change 0 ≤ R k / T - ((B k).val : ℝ) / M ∧ _ at hk
    change 0 ≤ R l / T - ((B l).val : ℝ) / M ∧ _ at hl
    have h := show |R k / T - R l / T| < 1 / (M : ℝ) from by
      apply abs_lt.mpr
      have hk' : R k / T - ((B k).val : ℝ) / M < 1 / M := hk.2
      have hl' : R l / T - ((B l).val : ℝ) / M < 1 / M := hl.2
      rw [hB] at hk' hk
      constructor <;> linarith [hk.1, hl.1]
    rw [← sub_div, abs_div, abs_of_pos hT] at h
    rw [hsum]
    simpa only [mul_comm (1 / (M : ℝ)) T, mul_one_div] using (div_lt_iff₀ hT).mp h

end

end AbcTwoNinths.ExteriorE1
