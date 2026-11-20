/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Pigeonhole

The module uses fractional-part bins to find a collision with bounded weighted error.

## Main results
* `AbcTwoNinths.Basic.collision`
* `AbcTwoNinths.Basic.weightedError`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open scoped BigOperators

private theorem fracLower (x : ℝ) : 0 ≤ Int.fract x := Int.fract_nonneg x

/-- The bin. -/
private noncomputable def bin (Q : ℕ) (hQ : 0 < Q) (x : ℝ) : Fin Q :=
  ⟨⌊(Q : ℝ) * Int.fract x⌋.toNat, by
    have h : (Q : ℝ) * Int.fract x < (Q : ℝ) := by
      exact mul_lt_of_lt_one_right (by exact_mod_cast hQ) (Int.fract_lt_one x)
    have hi : ⌊(Q : ℝ) * Int.fract x⌋ < (Q : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h)
    omega⟩

private theorem binBound {Q : ℕ} (hQ : 0 < Q) {x y : ℝ}
    (h : bin Q hQ x = bin Q hQ y) :
    |Int.fract x - Int.fract y| < 1 / (Q : ℝ) := by
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hx : 0 ≤ ⌊(Q : ℝ) * Int.fract x⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hQ'.le (fracLower x))
  have hy : 0 ≤ ⌊(Q : ℝ) * Int.fract y⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hQ'.le (fracLower y))
  have hv := congrArg Fin.val h
  change ⌊(Q : ℝ) * Int.fract x⌋.toNat = ⌊(Q : ℝ) * Int.fract y⌋.toNat at hv
  have hf : ⌊(Q : ℝ) * Int.fract x⌋ = ⌊(Q : ℝ) * Int.fract y⌋ := by omega
  have h1 := Int.floor_le ((Q : ℝ) * Int.fract x)
  have h2 := Int.lt_floor_add_one ((Q : ℝ) * Int.fract x)
  have h3 := Int.floor_le ((Q : ℝ) * Int.fract y)
  have h4 := Int.lt_floor_add_one ((Q : ℝ) * Int.fract y)
  rw [hf] at h1 h2
  rw [abs_lt]
  constructor
  · have h5 : Int.fract y - Int.fract x < 1 / (Q : ℝ) := by
      apply (lt_div_iff₀ hQ').2
      linarith
    linarith
  · apply (lt_div_iff₀ hQ').2
    linarith

/--
A finite-group label and fractional-part bins produce a kernel vector with interior pivot and coordinate errors strictly below the reciprocal bin counts.
-/
theorem collision {ι G : Type*} [Fintype ι] [Group G] [Fintype G]
    (φ : Multiplicative (ℤ × (ι → ℤ)) →* G)
    (E : ℕ) (e : ι → ℤ) (Q : ι → ℕ) (hQ : ∀ q, 0 < Q q)
    (hE : Fintype.card G * ∏ q, Q q < E) :
    ∃ k : ℕ, ∃ v : ι → ℤ, 0 < k ∧ k < E ∧
      φ (Multiplicative.ofAdd ((k : ℤ), v)) = 1 ∧
      ∀ q, |(v q : ℝ) - (k : ℝ) / E * (e q : ℝ)| < 1 / (Q q : ℝ) := by
  classical
  let x (i : Fin E) (q : ι) : ℝ := (i.val : ℝ) / E * (e q : ℝ)
  let d (i : Fin E) (q : ι) : ℤ := ⌊x i q⌋
  let f (i : Fin E) : G × (∀ q, Fin (Q q)) :=
    (φ (Multiplicative.ofAdd ((i.val : ℤ), d i)), fun q => bin (Q q) (hQ q) (x i q))
  have hc : Fintype.card (G × (∀ q, Fin (Q q))) < Fintype.card (Fin E) := by
    simpa [Fintype.card_prod, Fintype.card_pi] using hE
  obtain ⟨i, j, hn, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  suffices aux : ∀ (i j : Fin E), j.val < i.val → f i = f j →
      ∃ k : ℕ, ∃ v : ι → ℤ, 0 < k ∧ k < E ∧
        φ (Multiplicative.ofAdd ((k : ℤ), v)) = 1 ∧
        ∀ q, |(v q : ℝ) - (k : ℝ) / E * (e q : ℝ)| < 1 / (Q q : ℝ) by
    rcases lt_or_gt_of_ne (fun h => hn (Fin.ext h)) with hij | hij
    · exact aux j i hij hf.symm
    · exact aux i j hij hf
  intro i j hij hf
  have hi := i.isLt
  let k := i.val - j.val
  have hk : (k : ℤ) = (i.val : ℤ) - (j.val : ℤ) := by
    exact_mod_cast Nat.cast_sub hij.le
  have hkR : (k : ℝ) = (i.val : ℝ) - (j.val : ℝ) := Nat.cast_sub hij.le
  refine ⟨k, fun q => d i q - d j q, by dsimp [k]; omega, by dsimp [k]; omega, ?_, ?_⟩
  · have hg := congrArg Prod.fst hf
    change φ (Multiplicative.ofAdd ((i.val : ℤ), d i)) =
      φ (Multiplicative.ofAdd ((j.val : ℤ), d j)) at hg
    rw [hk]
    change φ (Multiplicative.ofAdd ((i.val : ℤ), d i) /
      Multiplicative.ofAdd ((j.val : ℤ), d j)) = 1
    rw [map_div, hg, div_self']
  · intro q
    have hb := congrArg (fun z : G × (∀ q, Fin (Q q)) => z.2 q) hf
    change bin (Q q) (hQ q) (x i q) = bin (Q q) (hQ q) (x j q) at hb
    have hr := binBound (hQ q) hb
    rw [abs_sub_comm] at hr
    convert hr using 2
    simp only [Int.cast_sub, d, Int.fract, x]
    rw [hkR, sub_div, sub_mul]
    ring

/--
Strict coordinate errors and positive weights on a nonempty index set give total weighted error below the reciprocal-bin budget bound.
-/
theorem weightedError {ι : Type*} [Fintype ι] [Nonempty ι]
    (Q : ι → ℕ) (w : ι → ℝ) (r : ι → ℝ) (T : ℝ)
    (hw : ∀ q, 0 < w q) (hr : ∀ q, |r q| < 1 / (Q q : ℝ))
    (hT : ∑ q, w q / (Q q : ℝ) ≤ T) :
    ∑ q, |r q| * w q < T := by
  classical
  apply lt_of_lt_of_le _ hT
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro q _
  calc
    |r q| * w q < (1 / (Q q : ℝ)) * w q := mul_lt_mul_of_pos_right (hr q) (hw q)
    _ = w q / (Q q : ℝ) := by ring

/--
Rounding the scaled weights up gives positive bin counts with total weighted reciprocal at most the budget.
-/
theorem ceilBins {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (T : ℝ) (hw : ∀ q, 0 < w q) (hT : 0 < T) :
    (∀ q, 0 < ⌈(Fintype.card ι : ℝ) * w q / T⌉₊) ∧
    (∑ q, w q / (⌈(Fintype.card ι : ℝ) * w q / T⌉₊ : ℝ)) ≤ T := by
  classical
  let n : ℝ := Fintype.card ι
  let Q (q : ι) := ⌈n * w q / T⌉₊
  change (∀ q, 0 < Q q) ∧ (∑ q, w q / (Q q : ℝ)) ≤ T
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hc (q : ι) : n * w q / T ≤ (Q q : ℝ) := Nat.le_ceil _
  have hp (q : ι) : 0 < (Q q : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hn (hw q)) hT) (hc q)
  refine ⟨fun q => by exact_mod_cast hp q, ?_⟩
  calc
    (∑ q, w q / (Q q : ℝ)) ≤ ∑ _q : ι, T / n := by
      apply Finset.sum_le_sum
      intro q _
      have hh := (div_le_iff₀ hT).1 (hc q)
      apply (div_le_iff₀ (hp q)).2
      have hh' : (T / n * (Q q : ℝ)) * n = (Q q : ℝ) * T := by
        field_simp
      apply le_of_mul_le_mul_right _ hn
      rw [hh']
      simpa [mul_comm] using hh
    _ = T := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change n * (T / n) = T
      field_simp

end

end AbcTwoNinths.Basic
