/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialSumMajorant

/-!
# Selected Row Envelope

The module bounds a selected row split by an exponential envelope with a perturbation term. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.selectedRowSplitEnvelope`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

private theorem expPerturbation {x : ℝ} (hx : |x| ≤ 1/2) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  exact Real.abs_exp_sub_one_le (by linarith)

/--
Bounds the exponential sum for a selected row set using the complementary perturbation bound and the Taylor remainder. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem selectedRowSplitEnvelope {K L : ℕ} {C : Type*}
    (f : (Fin K × Fin L) ↪ C) (s : Finset (Fin K × Fin L))
    (u ε : C → ℝ) (γ H P W : ℝ)
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hu : ∀ j, |u (f j)| ≤ H)
    (he : ∀ (i j : Fin K × Fin L), i ∉ s →
      |(i.2.val : ℝ) * ε (f j)| ≤ 1/2 ∧
        2 * |(i.2.val : ℝ) * ε (f j)| ≤ P)
    (hw : ∀ σ : Equiv.Perm (Fin K × Fin L),
      |∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))| ≤ W)
    (X : ℝ)
    (hX : ∀ σ : Equiv.Perm (Fin K × Fin L),
      (∑ j, if σ j ∈ s then 0 else ((σ j).2.val : ℝ) * γ * u (f j)) +
        max (∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))) 0 ≤ X) :
    let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
    |_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s (u ∘ f) (fun i => i.2.val) (ε ∘ f) γ (fun i => i.1.val) 0 1| ≤
      ((∏ i : Fin K × Fin L, ((i.1.val).factorial : ℝ)⁻¹) *
        ((K*L).factorial : ℝ) * (∏ i : Fin K × Fin L, H ^ i.1.val) *
        P ^ (K*L-s.card) * W ^ E * Real.exp X) / (E.factorial : ℝ) := by
  classical
  intro E
  refine (_root_.AbcTwoNinths.ExteriorE1.selectedRowSplitMajorant f s u ε γ).trans
    (div_le_div_of_nonneg_right ?_ (by positivity))
  unfold _root_.AbcTwoNinths.ExteriorE1.taylorExponentialMajorant
  let I := Fin K × Fin L
  let N : ℝ := ∏ i : I, ((i.1.val).factorial : ℝ)⁻¹
  let Q : ℝ := ∏ i : I, H ^ i.1.val
  calc
    _ ≤ N * ∑ σ : Equiv.Perm I, Q * P ^ (K*L-s.card) * W ^ E * Real.exp X := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [N]; positivity)
      apply Finset.sum_le_sum
      intro σ _
      let p (j : I) : ℝ := if σ j ∈ s then 1 else P
      let z (j : I) : ℝ := if σ j ∈ s then 0 else ((σ j).2.val : ℝ) * γ * u (f j)
      let w : ℝ := ∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))
      have hp (j : I) : 0 ≤ p j := by by_cases h : σ j ∈ s <;> simp [p, h, hP]
      have hprod : (∏ j : I, p j) = P ^ (K*L-s.card) := by
        change (∏ j : I, (fun i : I => if i ∈ s then (1 : ℝ) else P) (σ j)) = _
        rw [Equiv.prod_comp σ (fun i : I => if i ∈ s then (1 : ℝ) else P)]
        simp [I, Finset.prod_ite, Finset.filter_notMem_eq_sdiff,
          Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have hcoeff :
          |Equiv.Perm.sign σ • ∏ j : I, if σ j ∈ s then u (f j) ^ (σ j).1.val else
            u (f j) ^ (σ j).1.val * Real.exp (((σ j).2.val : ℝ) * γ * u (f j)) *
              (Real.exp (((σ j).2.val : ℝ) * ε (f j)) - 1)| ≤
            Q * P ^ (K*L-s.card) * Real.exp (∑ j, z j) := by
        have henv : (∏ j : I, H ^ (σ j).1.val * p j * Real.exp (z j)) =
            Q * P ^ (K*L-s.card) * Real.exp (∑ j, z j) := by
          simp only [Finset.prod_mul_distrib, hprod, Real.exp_sum, Q]
          rw [show (∏ j : I, H ^ (σ j).1.val) = ∏ i : I, H ^ i.1.val from
            Equiv.prod_comp σ (fun i : I => H ^ i.1.val)]
        rw [← henv]
        have hsign : ∀ x : ℝ, |Equiv.Perm.sign σ • x| = |x| := by
          intro x
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · simp [h]
          · simp [h, Units.neg_smul]
        rw [hsign, Finset.abs_prod]
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro j _
        have hh : |u (f j)| ^ (σ j).1.val ≤ H ^ (σ j).1.val :=
          pow_le_pow_left₀ (abs_nonneg _) (hu j) _
        by_cases hj : σ j ∈ s
        · simpa [hj, p, z, abs_pow] using hh
        · have hpert := (expPerturbation (he (σ j) j hj).1).trans (he (σ j) j hj).2
          simp only [p, z, ite_eq_right hj, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
          calc
            _ ≤ (H ^ (σ j).1.val * Real.exp (((σ j).2.val : ℝ) * γ * u (f j))) * P :=
              mul_le_mul (mul_le_mul_of_nonneg_right hh (by positivity)) hpert
                (abs_nonneg _) (by positivity)
            _ = H ^ (σ j).1.val * P * Real.exp (((σ j).2.val : ℝ) * γ * u (f j)) := by
              ring
      change _ * |w| ^ E * Real.exp (max w 0) ≤ _
      have hwp : |w| ^ E ≤ W ^ E := pow_le_pow_left₀ (abs_nonneg _) (hw σ) _
      have hx : (∑ j, z j) + max w 0 ≤ X := hX σ
      calc
        _ ≤ (Q * P ^ (K*L-s.card) * Real.exp (∑ j, z j)) * W ^ E *
            Real.exp (max w 0) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hcoeff hwp (by positivity) (by dsimp [Q]; positivity)
        _ = Q * P ^ (K*L-s.card) * W ^ E * Real.exp ((∑ j, z j) + max w 0) := by
          rw [Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (by dsimp [Q]; positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, N, Q, I]
      ring

end

end AbcTwoNinths.ExteriorE1
