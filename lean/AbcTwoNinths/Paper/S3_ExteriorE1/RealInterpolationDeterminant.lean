/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RealInterpolationZeroEstimate

/-!
# Real Interpolation Determinant

The module applies the real zero estimate to select a nonzero interpolation determinant. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realInterpolationDeterminant`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE1

section



/--
Section 2 of Laurent (2008): select a nonzero real minor with the
integer-binomial rows and separate monomial powers used in the bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realInterpolationDeterminant
    {R S R' S' L J b₁ b₂ : ℕ} (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : L ≤ (Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeW (R := R) (S := S) a b)).card)
    (h₂ : L * J <
      (Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') b₁ b₂)).card) :
    ∃ f : (Fin (J+1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S'),
      (Matrix.of fun k j : Fin (J+1) × Fin L =>
        (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
          (a : ℝ) ^ (k.2.val * (f j).1.val) *
          (b : ℝ) ^ (k.2.val * (f j).2.val)).det ≠ 0 := by
  obtain ⟨f, hf⟩ := _root_.AbcTwoNinths.ExteriorE1.realInterpolationZeroEstimate a b ha hb h₁ h₂
  refine ⟨f, ?_⟩
  convert hf using 2
  ext k j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, _root_.AbcTwoNinths.Basic.nodeZ, mul_pow,
    ← pow_mul]
  rw [Nat.mul_comm k.2.val (f j).1.val, Nat.mul_comm k.2.val (f j).2.val, mul_assoc]

end

end AbcTwoNinths.ExteriorE1
