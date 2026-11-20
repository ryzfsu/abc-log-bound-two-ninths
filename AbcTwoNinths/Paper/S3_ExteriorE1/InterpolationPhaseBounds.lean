/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.DeterminantEnvelopeSum

/-!
# Interpolation Phase Bounds

The module bounds the frequency mass and perturbation and splits the row phases for the real determinant estimate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.splitPhaseSum`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section
open scoped BigOperators

private theorem twiceSumSnd (K L : ℕ) :
    2 * (∑ i : Fin K × Fin L, i.2.val) = K * L * (L - 1) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) L]
  change 2 * (K * (∑ i ∈ Finset.range L, i)) = _
  have h := Finset.sum_range_id_mul_two L
  calc
    _ = K * ((∑ i ∈ Finset.range L, i) * 2) := by ring
    _ = _ := by rw [h]; ring

/--
The sum of the second grid indices, multiplied by the first grid size, equals the scaled triangular number.
-/
theorem frequencyMass (K L : ℕ) :
    (∑ i : Fin K × Fin L, (i.2.val : ℝ)) * K =
      ((K * L * K * (L - 1) / 2 : ℕ) : ℝ) := by
  have h := twiceSumSnd K L
  have hh : 2 * ((∑ i : Fin K × Fin L, i.2.val) * K) =
      K * L * K * (L - 1) := by
    calc
      _ = (2 * (∑ i : Fin K × Fin L, i.2.val)) * K := by ring
      _ = _ := by rw [h]; ring
  have he : K * L * K * (L - 1) / 2 =
      (∑ i : Fin K × Fin L, i.2.val) * K := by omega
  rw [he, Nat.cast_mul, Nat.cast_sum]

/--
Under the small logarithmic-form hypothesis, the absolute phase perturbation is at most one half and its double is at most the inverse radius power.
-/
theorem phasePerturbationBound {N L S a d : ℕ} {Q B Λ : ℝ}
    (hN : 0 < N) (hQ : 2 ≤ Q) (hB : 1 ≤ B) (ha : a ≤ L - 1) (hd : d ≤ S)
    (hS : 2 * (L - 1) * S ≤ N) (hΛ : |Λ| ≤ ((N : ℝ) * Q ^ N)⁻¹) :
    |(a : ℝ) * ((d : ℝ) * Λ / B)| ≤ 1/2 ∧
      2 * |(a : ℝ) * ((d : ℝ) * Λ / B)| ≤ (Q ^ N)⁻¹ := by
  have hQp : 1 ≤ Q ^ N := one_le_pow₀ (by linarith)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (2 : ℝ) * ((L - 1 : ℕ) : ℝ) * S ≤ N := by exact_mod_cast hS
  have hab : (a : ℝ) * (d : ℝ) ≤ (N : ℝ) / 2 := by
    have hw : (a : ℝ) * (d : ℝ) ≤ ((L - 1 : ℕ) : ℝ) * S := by gcongr
    linarith
  have hz : |(a : ℝ) * ((d : ℝ) * Λ / B)| ≤ (Q ^ N)⁻¹ / 2 := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg a),
      abs_of_nonneg (Nat.cast_nonneg d), abs_of_nonneg (by linarith : 0 ≤ B)]
    calc
      _ = ((a : ℝ) * d * |Λ|) / B := by ring
      _ ≤ (a : ℝ) * d * |Λ| := div_le_self (by positivity) hB
      _ ≤ ((N : ℝ) / 2) * (((N : ℝ) * Q ^ N)⁻¹) :=
        mul_le_mul hab hΛ (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hi : (Q ^ N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQp
  constructor <;> linarith

/--
Splitting a nonnegative phase sum along a permuted subset preserves the total mass. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem splitPhaseSum {I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset I) (σ : Equiv.Perm I) (z : I → ℝ) (hz : ∀ j, 0 ≤ z j) :
    (∑ j, if σ j ∈ s then 0 else z j) +
      max (∑ i ∈ s, z (σ.symm i)) 0 = ∑ j, z j := by
  rw [max_eq_left (Finset.sum_nonneg fun i _ => hz (σ.symm i))]
  have h : (∑ i ∈ s, z (σ.symm i)) = ∑ j, if σ j ∈ s then z j else 0 := by
    calc
      _ = ∑ i, if i ∈ s then z (σ.symm i) else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ = _ := by
        symm
        simpa only [Equiv.symm_apply_apply] using
          (Equiv.sum_comp σ (fun i => if i ∈ s then z (σ.symm i) else 0))
  rw [h, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all

end

end AbcTwoNinths.ExteriorE1
