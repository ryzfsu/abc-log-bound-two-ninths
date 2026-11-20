/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationParameterInequalities

/-!
# Exponential Perturbation

The module bounds the exponential perturbation and derives the accompanying parameter inequality from the grid dimensions. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.certQ0AndPerturbationOfGrid`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Gives bounds for the exponential scale, the small exponential perturbation and the weighted phase on the interpolation grid. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem certQ0AndPerturbationOfGrid {r a b : ℝ} {K L R S : ℕ}
    (hr : 0 < r) (hK : 641 ≤ K) (hL : 1 ≤ L)
    (hS : S ≤ K)
    (hsmall : 2 * (L - 1) * S ≤ K * L)
    (hheight : (R : ℝ) * a + (S : ℝ) * b ≤ (5929 / 20000 : ℝ) * r * K) :
    let N := K * L
    let Q := (10 / 3 : ℝ) * Real.exp r / r
    2 ≤ Q ∧ 8 < Q ∧ (7 / 10 : ℝ) * r ≤ Real.log (Q / Real.exp 1) ∧
    ((L - 1 : ℕ) : ℝ) * (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤ 1 / (2 * Q ^ N) ∧
    1 / (2 * Q ^ N) ≤ (1 / 2 : ℝ) ∧
    (∀ z : ℝ, |z| ≤ 1 / 2 → Real.exp |z| < 2 ∧ |Real.exp z - 1| ≤ 2 * |z|) ∧
    (R : ℝ) * Real.exp (-r) * a + (S : ℝ) * Real.exp (-r) * b +
      (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤ (K : ℝ) / Q ∧
    (N : ℝ) / (4 * Q ^ N) ≤ 1 := by
  let Q := (10 / 3 : ℝ) * Real.exp r / r
  let N := K * L
  change 2 ≤ Q ∧ 8 < Q ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  have hN : K ≤ N := by
    dsimp [N]
    simpa using Nat.mul_le_mul_left K hL
  have hN2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he := Real.add_one_le_exp (r - 1)
  rw [Real.exp_sub] at he
  have he' := (le_div_iff₀ (Real.exp_pos 1)).mp he
  have hQ8 : 8 < Q := by
    dsimp [Q]
    apply (lt_div_iff₀ hr).2
    have h := mul_le_mul_of_nonneg_right _root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.1 hr.le
    nlinarith
  have hQ : 0 < Q := by linarith
  have hp : 0 < Q ^ N := pow_pos hQ _
  have hp1 : 1 ≤ Q ^ N := one_le_pow₀ (by linarith)
  have hp8 : 8 * Q ≤ Q ^ N := calc
    8 * Q ≤ Q ^ 2 := by nlinarith
    _ ≤ Q ^ N := pow_le_pow_right₀ (by linarith) hN2
  have hS' : (S : ℝ) ≤ N := by exact_mod_cast hS.trans hN
  have hK' : (641 : ℝ) ≤ K := by exact_mod_cast hK
  have hsmall' : 2 * (((L - 1 : ℕ) : ℝ)) * (S : ℝ) ≤ N := by exact_mod_cast hsmall
  refine ⟨by linarith, hQ8, _root_.AbcTwoNinths.ExteriorE1.certLogQ0DivE hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (mul_pos hn hp) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hsmall' hp.le]
  · apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  · intro z hz
    refine ⟨(Real.exp_le_exp.mpr hz).trans_lt ?_, _root_.AbcTwoNinths.ExteriorE1.certExpPerturbation hz⟩
    exact _root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.2.2.1.trans_lt (by norm_num)
  · have ht : (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤ 1 / (8 * Q) := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ (mul_pos hn hp) (by positivity)).2
      calc
        (S : ℝ) * (8 * Q) ≤ (N : ℝ) * (8 * Q) :=
          mul_le_mul_of_nonneg_right hS' (by positivity)
        _ ≤ (N : ℝ) * Q ^ N := mul_le_mul_of_nonneg_left hp8 hn.le
        _ = 1 * ((N : ℝ) * Q ^ N) := by ring
    have hbase : 1 / Q = (3 / 10 : ℝ) * r * Real.exp (-r) := by
      simp only [Q, Real.exp_neg]
      field_simp [hr.ne', (Real.exp_pos r).ne']
    have ht' : (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤
        (3 / 51280 : ℝ) * r * Real.exp (-r) * K := by
      refine ht.trans ?_
      rw [show 1 / (8 * Q) = (1 / 8 : ℝ) * (1 / Q) by ring, hbase]
      nlinarith [mul_le_mul_of_nonneg_left hK' (show 0 ≤ r * Real.exp (-r) by positivity)]
    change (R : ℝ) * Real.exp (-r) * a + (S : ℝ) * Real.exp (-r) * b +
      (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤ (K : ℝ) / Q
    rw [show (K : ℝ) / Q = (K : ℝ) * (1 / Q) by ring, hbase]
    have hh := mul_le_mul_of_nonneg_right hheight (Real.exp_pos (-r)).le
    have hpos : 0 ≤ r * Real.exp (-r) * (K : ℝ) := by positivity
    nlinarith
  · have hlt : (N : ℝ) < (2 : ℝ) ^ N := by
      exact_mod_cast (Nat.lt_two_pow_self : N < 2 ^ N)
    have hpow : (2 : ℝ) ^ N ≤ Q ^ N :=
      pow_le_pow_left₀ (by norm_num) (by linarith) _
    apply (div_le_iff₀ (show 0 < 4 * Q ^ N by positivity)).2
    linarith

end

end AbcTwoNinths.ExteriorE1
