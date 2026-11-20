/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TwoLogarithmHeightBound

/-!
# Exact Interpolation Width

The module computes the exact centered width of the interpolation parameters. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.exactWidthL`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE1

section

open scoped BigOperators

/--
The sum of the distances from the midpoint of a row of length L is the integer quotient of L squared by four.
-/
theorem centerSumL (L : ℕ) :
    (∑ j : Fin L, |(j.val : ℝ) - ((L : ℝ) - 1) / 2|) = ((L * L / 4 : ℕ) : ℝ) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    obtain _ | _ | n := L
    · simp
    · norm_num [Fin.sum_univ_one]
    · have h := ih n (by omega : n < n.succ.succ)
      have hdiv : n.succ.succ * n.succ.succ / 4 = n * n / 4 + (n + 1) := by
        have he : n.succ.succ * n.succ.succ = n * n + 4 * (n + 1) := by
          simp only [Nat.succ_eq_add_one]
          ring
        rw [he, Nat.add_mul_div_left _ _ (by decide)]
      rw [hdiv, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
        Nat.cast_succ, Nat.cast_add]
      have hmid (j : Fin n) :
          (j.val : ℝ) + 1 - ((n : ℝ) + 1 + 1 - 1) / 2 =
            (j.val : ℝ) - ((n : ℝ) - 1) / 2 := by ring
      simp only [hmid, h]
      have hn : (0 : ℝ) ≤ n := by positivity
      rw [abs_of_nonpos (by linarith : (0 : ℝ) - ((n : ℝ) + 1 + 1 - 1) / 2 ≤ 0)]
      rw [abs_of_nonneg (by linarith [show (0 : ℝ) ≤ n by positivity] :
        (0 : ℝ) ≤ (n : ℝ) + 1 - ((n : ℝ) + 1 + 1 - 1) / 2)]
      ring

/--
Permuting the exponents of a bounded rectangular array changes their weighted sum by at most K times the integer quarter-square of L times R. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem exactWidthL (K L R : ℕ) (r : Fin K × Fin L → ℕ)
    (hr : ∀ j, r j ≤ R) (σ τ : Equiv.Perm (Fin K × Fin L)) :
    (∑ j, (σ j).2.val * r j) ≤ (∑ j, (τ j).2.val * r j) + K * (L * L / 4) * R := by
  have h := _root_.AbcTwoNinths.Basic.permutationExponentWidth
    (fun i : Fin K × Fin L => (i.2.val : ℝ)) (fun i => (r i : ℝ))
    (((L : ℝ) - 1) / 2) R σ.symm τ.symm
    (fun i => ⟨by positivity, by exact_mod_cast hr i⟩)
  have hc : (∑ i : Fin K × Fin L, |(i.2.val : ℝ) - ((L : ℝ) - 1) / 2|) =
      (K : ℝ) * ((L * L / 4 : ℕ) : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [_root_.AbcTwoNinths.ExteriorE1.centerSumL, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hx (π : Equiv.Perm (Fin K × Fin L)) :
      (∑ j, ((π j).2.val : ℝ) * (r j : ℝ)) =
      ∑ i, (i.2.val : ℝ) * (r (π.symm i) : ℝ) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp π (fun i => (i.2.val : ℝ) * (r (π.symm i) : ℝ)))
  have hle := (abs_le.mp h).2
  rw [← hx σ, ← hx τ, hc] at hle
  have hR : (∑ j, ((σ j).2.val : ℝ) * (r j : ℝ)) ≤
      (∑ j, ((τ j).2.val : ℝ) * (r j : ℝ)) +
        (K : ℝ) * ((L * L / 4 : ℕ) : ℝ) * (R : ℝ) := by linarith
  exact_mod_cast hR

end

end AbcTwoNinths.ExteriorE1
