/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib
public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Admissible Transverse Window

Strict inequalities on the diamond parameters give positive slack and an integer truncation. The
depth bounds give an integer interpolation row parameter satisfying the row budget in Section 7
of the paper.

## Main results
* `AbcTwoNinths.Terminal.sharpSlack`
* `AbcTwoNinths.Terminal.sharpRows`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section

/--
Choose two positive real margins and a positive integer truncation preserving both strict diamond inequalities.
-/
theorem sharpSlack {a κ : ℝ} (ha : 0 < a) (hgap : 3 * a < 1 - 2 * κ) :
    ∃ θ Z : ℝ, ∃ J : ℕ, 0 < θ ∧ θ < 1 ∧ 0 < Z ∧ Z < 1 ∧ 0 < J ∧
      3 * a * (1 + θ)^2 < 1 - 2 * κ ∧
      (1 + θ) * (1 - Z)^4 >
        (1 + Z)^3 * (1 + (9/2 : ℝ) * Z + (3/2 : ℝ) * Z^2 + 3 / (4 * (J : ℝ))) := by
  let θ := min (1/2 : ℝ) ((1 - 2 * κ - 3 * a) / (12 * a))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hθhalf : θ ≤ 1/2 := min_le_left _ _
  have hθ1 : θ < 1 := by linarith
  have hm := (le_div_iff₀ (show 0 < 12 * a by positivity)).mp
    (min_le_right (1/2 : ℝ) ((1 - 2 * κ - 3 * a) / (12 * a)))
  have hs : 3 * a * (1 + θ)^2 < 1 - 2 * κ := by
    have hsq : θ^2 ≤ θ := by nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hθ1.le)]
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le, mul_pos ha hθ]
  obtain ⟨J, hJ⟩ := exists_nat_gt (3 / (4 * θ))
  have hJ0 : 0 < (J : ℝ) :=
    lt_trans (by positivity : 0 < 3 / (4 * θ)) hJ
  have ht : 3 / (4 * (J : ℝ)) < θ := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ (show 0 < 4 * θ by positivity)).mp hJ
    nlinarith
  let f : ℝ → ℝ := fun z => (1 + θ) * (1 - z)^4 -
    (1 + z)^3 * (1 + (9/2 : ℝ) * z + (3/2 : ℝ) * z^2 + 3 / (4 * (J : ℝ)))
  have hf : Continuous f := by unfold f; fun_prop
  have hf0 : 0 < f 0 := by unfold f; norm_num; linarith
  obtain ⟨ε, hε, hεf⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hf) (0 : ℝ) hf0
  let Z := min (1/2 : ℝ) (ε/2)
  have hZ : 0 < Z := lt_min (by norm_num) (by positivity)
  have hZε : Z < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hzball : Z ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq, abs_of_pos hZ] using hZε
  have hzf : 0 < f Z := hεf hzball
  refine ⟨θ, Z, J, hθ, hθ1, hZ, lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_, hs, ?_⟩
  · exact_mod_cast hJ0
  · exact sub_pos.mp hzf

/-- The depth bounds give a positive row count `K` with `2 * K - 1 ≤ n < 2 * K + 1`
and `4 * K ≤ 3 * m`. -/
theorem sharpRows {n depth : ℝ} {m : ℕ} (hn : 1 ≤ n)
    (hdepth : n + 1 ≤ depth) (hm : depth ≤ (3 / 2 : ℝ) * m) :
    ∃ K : ℕ, 0 < K ∧ (2 * K - 1 : ℝ) ≤ n ∧ n - 1 < (2 * K : ℝ) ∧
      4 * K ≤ 3 * m := by
  let K := ⌊(n + 1) / 2⌋₊
  have hnK : 0 ≤ (n + 1) / 2 := by linarith
  have hhi : (K : ℝ) ≤ (n + 1) / 2 := Nat.floor_le hnK
  have hlo : (n + 1) / 2 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : 0 < K := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h] at hlo
    norm_num at hlo
    linarith
  have hKm : (4 : ℝ) * K ≤ 3 * m := by linarith
  exact ⟨K, hK, by linarith, by linarith, by exact_mod_cast hKm⟩

end

end AbcTwoNinths.Terminal
