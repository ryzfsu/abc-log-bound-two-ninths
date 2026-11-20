/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SelectedRowEnvelope

/-!
# Determinant Envelope Sum

The module sums the analytic envelopes over all selected-row subsets to bound the determinant. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.determinantSumEnvelope`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

open scoped BigOperators

/--
A uniform bound for each row-subset contribution bounds the absolute value of their sum over the rectangular index set. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem determinantSumEnvelope {K L : ℕ} {C : Type*}
    (f : (Fin K × Fin L) ↪ C) (u ε : C → ℝ) (γ H P W X A : ℝ)
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hu : ∀ j, |u (f j)| ≤ H)
    (he : ∀ i j : Fin K × Fin L, |(i.2.val : ℝ) * ε (f j)| ≤ 1/2 ∧
      2 * |(i.2.val : ℝ) * ε (f j)| ≤ P)
    (hw : ∀ s : Finset (Fin K × Fin L), ∀ σ : Equiv.Perm (Fin K × Fin L),
      |∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))| ≤ W)
    (hX : ∀ s : Finset (Fin K × Fin L), ∀ σ : Equiv.Perm (Fin K × Fin L),
      (∑ j, if σ j ∈ s then 0 else ((σ j).2.val : ℝ) * γ * u (f j)) +
        max (∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))) 0 ≤ X)
    (ha : ∀ s : Finset (Fin K × Fin L),
      let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
      P ^ (K * L - s.card) * W ^ E / (E.factorial : ℝ) ≤ A) :
    |∑ s : Finset (Fin K × Fin L),
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s (u ∘ f) (fun i => i.2.val) (ε ∘ f) γ (fun i => i.1.val) 0 1| ≤
      (2 : ℝ) ^ (K * L) * ((K * L).factorial : ℝ) *
        (∏ i : Fin K × Fin L, H ^ i.1.val / (i.1.val.factorial : ℝ)) * A * Real.exp X := by
  classical
  let I := Fin K × Fin L
  let B := ((K * L).factorial : ℝ) *
     (∏ i : I, H ^ i.1.val / (i.1.val.factorial : ℝ)) * Real.exp X
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _s : Finset I, B * A := by
      apply Finset.sum_le_sum
      intro s _
      let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
      refine (_root_.AbcTwoNinths.ExteriorE1.selectedRowSplitEnvelope f s u ε γ H P W hH hP hW hu
        (fun i j _ => he i j) (hw s) X (hX s)).trans ?_
      change _ / (E.factorial : ℝ) ≤ _
      convert mul_le_mul_of_nonneg_left (ha s) hB using 1
      dsimp [B]
      simp only [div_eq_mul_inv, Finset.prod_mul_distrib]
      ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, I, B]
      ring

end

end AbcTwoNinths.ExteriorE1
