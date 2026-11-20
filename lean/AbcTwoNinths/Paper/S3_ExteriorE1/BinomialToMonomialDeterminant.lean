/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Binomial To Monomial Determinant

The module identifies the binomial-basis determinant with the monomial-factorial determinant by a polynomial basis change. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.detBinomEqDetMonofact`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE1

section

open Polynomial
open scoped BigOperators

private theorem evalDescPochhammerFin {K : ℕ} (k : Fin K) (x : ℝ) :
    (descPochhammer ℝ k.val).eval x =
      ∑ m : Fin K, (descPochhammer ℝ k.val).coeff m.val * x ^ m.val := by
  calc
    _ = ∑ m ∈ Finset.range K, (descPochhammer ℝ k.val).coeff m * x ^ m :=
      eval_eq_sum_range' (by simpa only [descPochhammer_natDegree] using k.isLt) x
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (descPochhammer ℝ k.val).coeff m * x ^ m) K).symm

/--
Replacing binomial rows by factorial-normalized monomial rows preserves the weighted grid determinant. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem detBinomEqDetMonofact {K L : ℕ}
    (u : Fin K × Fin L → ℕ) (g : Fin L → Fin K × Fin L → ℝ) :
    (Matrix.of fun i j : Fin K × Fin L =>
      (Nat.choose (u j) i.1.val : ℝ) * g i.2 j).det =
    (Matrix.of fun i j : Fin K × Fin L =>
      ((u j : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ)) * g i.2 j).det := by
  classical
  let I := Fin K × Fin L
  let P (k : ℕ) : ℝ[X] := descPochhammer ℝ k
  let c (k m : ℕ) : ℝ := (P k).coeff m * (m.factorial : ℝ) / (k.factorial : ℝ)
  let A : Matrix I I ℝ := Matrix.of fun i j => if i.2 = j.2 then c i.1.val j.1.val else 0
  let B : Matrix I I ℝ := Matrix.of fun i j =>
    ((u j : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ)) * g i.2 j
  let ord : LinearOrder I := LinearOrder.lift' (fun i : I => toLex i) (fun _ _ h => h)
  have hdiag (i : I) : A i i = 1 := by
    have h : (P i.1.val).coeff i.1.val = 1 := by
      simpa only [P, descPochhammer_natDegree] using
        (monic_descPochhammer ℝ i.1.val).coeff_natDegree
    simp [A, c, h, div_self (by positivity : (i.1.val.factorial : ℝ) ≠ 0)]
  have htri : @Matrix.IsLowerTriangular I ℝ _ ord.toLT A := by
    intro i j hij
    change toLex i < toLex j at hij
    rcases Prod.Lex.toLex_lt_toLex.mp hij with h | ⟨_, h⟩
    · have hz : (P i.1.val).coeff j.1.val = 0 :=
        coeff_eq_zero_of_natDegree_lt (by
          change (descPochhammer ℝ i.1.val).natDegree < j.1.val
          rw [descPochhammer_natDegree]
          exact Fin.lt_def.mp h)
      simp [A, c, hz]
    · simp [A, ne_of_lt h]
  have hdet : A.det = 1 := by
    rw [@Matrix.det_of_isLowerTriangular I ℝ _ _ _ ord A htri]
    simp [hdiag]
  have hmul : (Matrix.of fun i j : I =>
      (Nat.choose (u j) i.1.val : ℝ) * g i.2 j) = A * B := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hpoly : (P i.1.val).eval (u j : ℝ) =
        ∑ m : Fin K, (P i.1.val).coeff m.val * (u j : ℝ) ^ m.val := by
      exact evalDescPochhammerFin i.1 _
    simp only [Matrix.of_apply, A, B, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    calc
      (Nat.choose (u j) i.1.val : ℝ) * g i.2 j =
          ((P i.1.val).eval (u j : ℝ) / (i.1.val.factorial : ℝ)) * g i.2 j := by
        rw [show (P i.1.val).eval (u j : ℝ) =
            (i.1.val.factorial : ℝ) * (Nat.choose (u j) i.1.val : ℝ) by
          simp [P, descPochhammer_eval_eq_descFactorial,
            Nat.descFactorial_eq_factorial_mul_choose]]
        field_simp
      _ = _ := by
        rw [hpoly, Finset.sum_div, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        dsimp [c]
        field_simp
  rw [hmul, Matrix.det_mul, hdet, one_mul]

end

end AbcTwoNinths.ExteriorE1
