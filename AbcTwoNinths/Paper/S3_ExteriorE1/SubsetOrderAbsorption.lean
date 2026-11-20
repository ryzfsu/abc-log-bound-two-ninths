/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Subset Order Absorption

The module bounds the range of subset orders and absorbs the resulting terms in the analytic estimate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.subsetOrderBoundsAndAbsorb`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open scoped BigOperators

section

/--
Bounds the order of a row subset, its deficit from full order and its factorial weight after accounting for the omitted rows. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem subsetOrderBoundsAndAbsorb {K L : ℕ} (hK : 1 ≤ K) (hL : 2 ≤ L)
    (s : Finset (Fin K × Fin L)) {Q₀ : ℝ} (hQ₀ : 1 ≤ Q₀) :
    let N := K * L
    let E₁ := N * K * (L - 1) / 2
    let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
    E ≤ E₁ ∧
    E₁ - E ≤ (N - s.card) * N ∧
    ((Q₀ ^ N)⁻¹) ^ (N - s.card) * (((E₁ : ℝ) / Q₀) ^ E / (E.factorial : ℝ)) ≤
      (Real.exp 1 / Q₀) ^ E₁ := by
  classical
  intro N E₁ E
  let n := s.card
  let S := ∑ i ∈ s, i.1.val
  let T := ∑ i ∈ Finset.univ \ s, i.1.val
  change E ≤ E₁ ∧ E₁ - E ≤ (N - n) * N ∧ _
  have h2K : 2 * K ≤ N := by
    dsimp [N]
    simpa [mul_comm] using Nat.mul_le_mul_left K hL
  have hN : 1 ≤ N := by omega
  have hu : (Finset.univ : Finset (Fin K × Fin L)).card = N := by
    simp [N, Fintype.card_prod]
  have hn : n ≤ N := by rw [← hu]; exact Finset.card_le_univ s
  have hsum : (∑ i : Fin K × Fin L, i.1.val) = S + T := by
    simpa [S, T, add_comm] using
      (Finset.sum_sdiff (Finset.subset_univ s) (f := fun i => i.1.val)).symm
  have hsum2 : 2 * (S + T) = L * (K * (K - 1)) := by
    rw [← hsum, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have hk : 2 * (∑ i : Fin K, i.val) = K * (K - 1) := by
      have heq := Fin.sum_univ_eq_sum_range (fun j : ℕ => j) K
      change (∑ i : Fin K, i.val) = (∑ i ∈ Finset.range K, i) at heq
      rw [heq, mul_comm, Finset.sum_range_id_mul_two]
    change 2 * (L * (∑ i : Fin K, i.val)) = _
    calc
      _ = L * (2 * ∑ i : Fin K, i.val) := by ring
      _ = _ := by rw [hk]
  have parity (m : ℕ) : 2 * (m * (m - 1) / 2) = m * (m - 1) := by
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))
  have hE₁ : 2 * E₁ = N * K * (L - 1) := by
    dsimp [E₁]
    apply Nat.mul_div_cancel'
    have hd := even_iff_two_dvd.mp (Nat.even_mul_pred_self L)
    convert dvd_mul_of_dvd_right hd (K * K) using 1
    dsimp [N]
    ring
  have hfull : 2 * E₁ + 2 * (S + T) = N * (N - 1) := by
    rw [hE₁, hsum2]
    have hL' : 1 ≤ L := by omega
    zify [hK, hL', hN]
    dsimp [N]
    ring
  have hdiff : N * (N - 1) = n * (n - 1) + (N - n) * (N + n - 1) := by
    by_cases hz : n = 0
    · simp [hz]
    · have hn' : 1 ≤ n := by omega
      have hNn : 1 ≤ N + n := by omega
      zify [hN, hn, hn', hNn]
      ring
  have hT : T ≤ (N - n) * (K - 1) := by
    calc
      T ≤ ∑ _i ∈ (Finset.univ \ s), (K - 1) :=
        Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt i.1.isLt
      _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ s), hu, n]
  have hlow : 2 * T ≤ (N - n) * (N + n - 1) := by
    calc
      2 * T ≤ 2 * ((N - n) * (K - 1)) := Nat.mul_le_mul_left _ hT
      _ = (N - n) * (2 * (K - 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hhigh : (N - n) * (N + n - 1) ≤ 2 * ((N - n) * N) := by
    calc
      _ ≤ (N - n) * (2 * N) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hp := parity n
  have he : E = n * (n - 1) / 2 - S := rfl
  have h₁ : E ≤ E₁ := by omega
  have h₂ : E₁ - E ≤ (N - n) * N := by omega
  refine ⟨h₁, h₂, ?_⟩
  have hExp : E₁ ≤ N * (N - n) + E := by rw [mul_comm N]; omega
  have hQ : 0 < Q₀ := by linarith
  have hnum : (E₁ : ℝ) ^ E / (E.factorial : ℝ) ≤ Real.exp 1 ^ E₁ := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp (E₁ : ℝ) (by positivity) E
  change ((Q₀ ^ N)⁻¹) ^ (N - n) * _ ≤ _
  calc
    _ = ((E₁ : ℝ) ^ E / (E.factorial : ℝ)) / Q₀ ^ (N * (N - n) + E) := by
      rw [inv_pow, ← pow_mul, pow_add, div_pow]
      field_simp
    _ ≤ Real.exp 1 ^ E₁ / Q₀ ^ E₁ :=
      div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_right₀ hQ₀ hExp)
    _ = _ := (div_pow _ _ _).symm

end

end AbcTwoNinths.ExteriorE1
