/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialTaylorExpansion

/-!
# Exponential Sum Majorant

The module constructs a majorant for the selected-row exponential sums in the interpolation determinant. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.selectedRowSplitMajorant`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The permutation-sum majorant for the Taylor derivative in the real determinant estimate. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def taylorExponentialMajorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ) : ℝ :=
  (∏ i : ι, ((d i).factorial : ℝ)⁻¹) *
  ∑ σ : Equiv.Perm ι,
    |Equiv.Perm.sign σ •
      ∏ j : ι, if σ j ∈ s then u j ^ d (σ j) else
        u j ^ d (σ j) * Real.exp (l (σ j) * γ * u j) *
          (Real.exp (l (σ j) * ε j) - 1)| *
    |∑ i ∈ s, (l i * γ) * u (σ.symm i)| ^ m *
    Real.exp (max (∑ i ∈ s, (l i * γ) * u (σ.symm i)) 0)

/-- The Taylor majorant bounds the absolute exponential sum throughout the unit interval. -/
theorem taylorExponentialSumLeMajorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d m t| ≤ _root_.AbcTwoNinths.ExteriorE1.taylorExponentialMajorant s u l ε γ d m := by
  unfold _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum _root_.AbcTwoNinths.ExteriorE1.taylorExponentialMajorant
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ∏ i : ι, ((d i).factorial : ℝ)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro σ _
  simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  let w : ℝ := ∑ i ∈ s, (l i * γ) * u (σ.symm i)
  change w * t ≤ max w 0
  by_cases hw : 0 ≤ w
  · exact (mul_le_of_le_one_right hw ht.2).trans (le_max_left _ _)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hw) ht.1).trans (le_max_right _ _)

/--
The selected-row exponential sum at one is bounded by the Taylor majorant divided by the factorial of the vanishing order. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem selectedRowSplitMajorant {K L : ℕ} {C : Type*}
    (f : (Fin K × Fin L) ↪ C) (s : Finset (Fin K × Fin L))
    (u ε : C → ℝ) (γ : ℝ) :
    let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
    |_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s (u ∘ f) (fun i => i.2.val) (ε ∘ f) γ (fun i => i.1.val) 0 1| ≤
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialMajorant s (u ∘ f) (fun i => i.2.val) (ε ∘ f) γ (fun i => i.1.val) E /
        (E.factorial : ℝ) := by
  intro E
  obtain ⟨t, ht, h⟩ := _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumExactExpansion s (u ∘ f) (fun i => i.2.val)
    (ε ∘ f) γ (fun i => i.1.val)
  rw [h, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (E.factorial : ℝ))]
  exact div_le_div_of_nonneg_right
    (_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumLeMajorant s _ _ _ γ _ E t ht) (by positivity)

end

end AbcTwoNinths.ExteriorE1
