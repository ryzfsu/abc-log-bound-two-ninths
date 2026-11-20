/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic

/-!
# Dirichlet Basis

The module constructs a lattice basis using a Dirichlet approximation to its shear parameter. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.dirichletBasis`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section

private theorem approximation (c : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ Q : ℕ, 1 ≤ Q ∧ Q ≤ n ∧ ∃ P : ℤ, |(Q : ℝ) * c - P| ≤ 1 / ((n : ℝ) + 1) := by
  obtain ⟨P, k, hk, hkn, herr⟩ := Real.exists_int_int_abs_mul_sub_le c hn
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
  refine ⟨k.toNat, ?_, ?_, P, ?_⟩
  · omega
  · omega
  · have hc : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast he
    simpa only [hc] using herr

/--
Excluding small denominators gives two rational approximants with determinant of absolute value one and controlled errors. This is used in Section 7 of the paper.
-/
theorem dirichletBasis (c : ℝ) {W Qs : ℕ} (hW : 2 ≤ W) (hWQ : W ≤ Qs)
    (good : ∀ Q : ℕ, 1 ≤ Q → Q < W → ∀ P : ℤ,
      1 / ((Qs : ℝ) + 1) < |(Q : ℝ) * c - P|) :
    ∃ P1 P2 : ℤ, ∃ Q1 Q2 : ℕ,
      W ≤ Q1 ∧ Q1 ≤ Qs ∧ 1 ≤ Q2 ∧ Q2 < Q1 ∧
      |(Q1 : ℝ) * c - P1| ≤ 1 / ((Qs : ℝ) + 1) ∧
      |(Q2 : ℝ) * c - P2| ≤ 1 / (Q1 : ℝ) ∧
      ((Q1 : ℤ) * P2 - P1 * Q2 = 1 ∨ (Q1 : ℤ) * P2 - P1 * Q2 = -1) := by
  classical
  let pred := fun Q : ℕ => 1 ≤ Q ∧ Q ≤ Qs ∧
    ∃ P : ℤ, |(Q : ℝ) * c - P| ≤ 1 / ((Qs : ℝ) + 1)
  have hex : ∃ Q, pred Q := approximation c (by omega)
  let Q1 := Nat.find hex
  obtain ⟨hq1, hq1s, P1, herr1⟩ := Nat.find_spec hex
  change 1 ≤ Q1 at hq1
  change Q1 ≤ Qs at hq1s
  change |(Q1 : ℝ) * c - P1| ≤ _ at herr1
  have hw1 : W ≤ Q1 := by
    by_contra! hw
    exact (not_lt_of_ge herr1) (good Q1 hq1 hw P1)
  obtain ⟨Q2, hq2, hq2s, P2, herr2⟩ := approximation c (n := Q1 - 1) (by omega)
  have hq21 : Q2 < Q1 := by omega
  have hn : Q1 - 1 + 1 = Q1 := by omega
  have hnR : ((Q1 - 1 : ℕ) : ℝ) + 1 = (Q1 : ℝ) := by exact_mod_cast hn
  rw [hnR] at herr2
  have hq1R : (0 : ℝ) < Q1 := by exact_mod_cast (show 0 < Q1 by omega)
  have hq2R : (0 : ℝ) ≤ Q2 := by positivity
  have hq21R : (Q2 : ℝ) < Q1 := by exact_mod_cast hq21
  have hq2sR : (Q2 : ℝ) < (Qs : ℝ) + 1 := by
    exact_mod_cast (show Q2 < Qs + 1 by omega)
  let D : ℤ := (Q1 : ℤ) * P2 - P1 * Q2
  have hid : (D : ℝ) = (Q2 : ℝ) * ((Q1 : ℝ) * c - P1) -
      (Q1 : ℝ) * ((Q2 : ℝ) * c - P2) := by
    push_cast [D]
    ring
  have hlim : (Q2 : ℝ) * (1 / ((Qs : ℝ) + 1)) < 1 := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    simpa using hq2sR
  have hb1 := mul_le_mul_of_nonneg_left herr1 hq2R
  have hb2 := mul_le_mul_of_nonneg_left herr2 hq1R.le
  rw [mul_one_div, div_self hq1R.ne'] at hb2
  have habs : |(D : ℝ)| < 2 := by
    calc
      |(D : ℝ)| ≤ (Q2 : ℝ) * |(Q1 : ℝ) * c - P1| +
          (Q1 : ℝ) * |(Q2 : ℝ) * c - P2| := by
        rw [hid, sub_eq_add_neg]
        simpa only [abs_neg, abs_mul, abs_of_nonneg hq2R, abs_of_pos hq1R]
          using abs_add_le ((Q2 : ℝ) * ((Q1 : ℝ) * c - P1))
            (-((Q1 : ℝ) * ((Q2 : ℝ) * c - P2)))
      _ < 2 := by linarith
  have hD : D ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hid
    have hh := congrArg abs (sub_eq_zero.mp hid.symm)
    rw [abs_mul, abs_mul, abs_of_nonneg hq2R, abs_of_pos hq1R] at hh
    have hsmall : |(Q2 : ℝ) * c - P2| ≤ 1 / ((Qs : ℝ) + 1) := by
      have hpos : 0 ≤ (1 : ℝ) / ((Qs : ℝ) + 1) := by positivity
      have hm := mul_le_mul_of_nonneg_right hq21R.le hpos
      exact le_of_mul_le_mul_left (hh ▸ hb1.trans hm) hq1R
    have hmin := Nat.find_min' hex (show pred Q2 from ⟨hq2, by omega, P2, hsmall⟩)
    exact (not_le_of_gt hq21) hmin
  have hDi : |D| < 2 := by exact_mod_cast habs
  refine ⟨P1, P2, Q1, Q2, hw1, hq1s, hq2, hq21, herr1, herr2, ?_⟩
  change D = 1 ∨ D = -1
  by_cases hsign : 0 ≤ D
  · rw [abs_of_nonneg hsign] at hDi
    omega
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hDi
    omega

end

end AbcTwoNinths.Terminal
