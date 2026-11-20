/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationPhaseBounds
public import AbcTwoNinths.Paper.S3_ExteriorE1.BinomialToMonomialDeterminant
public import AbcTwoNinths.Paper.S3_ExteriorE1.MonomialDeterminantExpansion
public import AbcTwoNinths.Paper.S3_ExteriorE1.SubsetOrderAbsorption
public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Variable Radius Determinant Bound

The module bounds the real interpolation determinant on a variable-radius grid. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realVarRadiusDetBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section
open scoped BigOperators


/--
Bounds the real binomial determinant given its monomial expansion and a bound for every subset term.
-/
theorem realVarRadiusDetBoundFrom {K L R S b₁ b₂ : ℕ}
    (hK : 1 ≤ K) (hL : 2 ≤ L) (hb₂ : 0 < b₂)
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (f : (Fin K × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle R S)
    (V₁ V₂ : ℕ)
    (hV₁ : ∀ σ : Equiv.Perm (Fin K × Fin L), ∑ j, (σ j).2.val * (f j).1.val ≤ V₁)
    (hV₂ : ∀ σ : Equiv.Perm (Fin K × Fin L), ∑ j, (σ j).2.val * (f j).2.val ≤ V₂)
    (Q : ℝ) (hQ : 2 ≤ Q) (hS : 2 * (L - 1) * S ≤ K * L)
    (hγM : (Real.log (q₁ : ℝ) / (b₂ : ℝ)) * ((R * b₂ + S * b₁ : ℕ) : ℝ) ≤ (K : ℝ) / Q)
    (hΛ : |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤
      (((K * L : ℕ) : ℝ) * Q ^ (K * L))⁻¹) :
    let I := Fin K × Fin L
    let N := K * L
    let E₁ := N * K * (L - 1) / 2
    let M : ℝ := ((R * b₂ + S * b₁ : ℕ) : ℝ)
    let u : _root_.AbcTwoNinths.Basic.Rectangle R S → ℝ := fun d => (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ d : ℝ)
    let Λ := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)
    let γ := Real.log (q₁ : ℝ) / (b₂ : ℝ)
    let ε : _root_.AbcTwoNinths.Basic.Rectangle R S → ℝ := fun d => (d.2.val : ℝ) * Λ / (b₂ : ℝ)
    let g : Fin L → I → ℝ := fun i j =>
      (q₁ : ℝ) ^ (i.val * (f j).1.val) * (q₂ : ℝ) ^ (i.val * (f j).2.val)
    (Matrix.of fun i j : I =>
      (u (f j) ^ i.1.val / (i.1.val.factorial : ℝ)) * g i.2 j).det =
      (∑ s : Finset I, _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s (u ∘ f) (fun i => i.2.val) (ε ∘ f) γ (fun i => i.1.val) 0 1) →
    (∀ s : Finset I,
      let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, i.1.val
      ((Q ^ N)⁻¹) ^ (N - s.card) * (((E₁ : ℝ) / Q) ^ E / (E.factorial : ℝ)) ≤
        (Real.exp 1 / Q) ^ E₁) →
    |(Matrix.of fun i j : I => (Nat.choose (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (f j)) i.1.val : ℝ) * g i.2 j).det| ≤
      (2 : ℝ) ^ N * (N.factorial : ℝ) *
      (∏ i : I, M ^ i.1.val / (i.1.val.factorial : ℝ)) *
      (Real.exp 1 / Q) ^ E₁ * (q₁ : ℝ) ^ V₁ * (q₂ : ℝ) ^ V₂ * Real.exp 1 := by
  classical
  intro I N E₁ M u Λ γ ε g hsplit hA
  have hq₁' : (1 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂' : (1 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hγ : 0 ≤ γ := div_nonneg (Real.log_pos hq₁').le (by positivity)
  have hQ' : 0 < Q := by linarith
  have hB : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb₂
  have hN : 0 < N := Nat.mul_pos (by omega) (by omega)
  have hu0 (d : _root_.AbcTwoNinths.Basic.Rectangle R S) : 0 ≤ u d := Nat.cast_nonneg _
  have hu (j : I) : |u (f j)| ≤ M := by
    rw [abs_of_nonneg (hu0 _)]
    dsimp [u, M, _root_.AbcTwoNinths.Basic.nodeZ]
    exact_mod_cast Nat.add_le_add
      (Nat.mul_le_mul_right b₂ (Nat.le_of_lt_succ (f j).1.isLt))
      (Nat.mul_le_mul_right b₁ (Nat.le_of_lt_succ (f j).2.isLt))
  let P := (Q ^ N)⁻¹
  let W := (E₁ : ℝ) / Q
  let X := (V₁ : ℝ) * Real.log (q₁ : ℝ) + (V₂ : ℝ) * Real.log (q₂ : ℝ) + 1
  have he (i j : I) : |(i.2.val : ℝ) * ε (f j)| ≤ 1/2 ∧
      2 * |(i.2.val : ℝ) * ε (f j)| ≤ P :=
    _root_.AbcTwoNinths.ExteriorE1.phasePerturbationBound hN hQ hB (by have := i.2.isLt; omega)
      (Nat.le_of_lt_succ (f j).2.isLt) hS hΛ
  have hw (s : Finset I) (σ : Equiv.Perm I) :
      |∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))| ≤ W := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hγ) (hu0 _))]
    calc
      _ ≤ ∑ i ∈ s, (i.2.val : ℝ) * ((K : ℝ) / Q) := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hu (σ.symm i))) hγ).trans hγM
      _ ≤ ∑ i : I, (i.2.val : ℝ) * ((K : ℝ) / Q) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
      _ = W := by
        rw [← Finset.sum_mul]
        change (∑ i : Fin K × Fin L, (i.2.val : ℝ)) * ((K : ℝ) / Q) = _
        rw [← mul_div_assoc, _root_.AbcTwoNinths.ExteriorE1.frequencyMass K L]
  have hphase (d : _root_.AbcTwoNinths.Basic.Rectangle R S) :
      γ * u d + ε d = (d.1.val : ℝ) * Real.log (q₁ : ℝ) +
        (d.2.val : ℝ) * Real.log (q₂ : ℝ) := by
    dsimp [γ, u, ε, Λ, _root_.AbcTwoNinths.Basic.nodeZ]
    push_cast
    have hb : (b₂ : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hPmass : (N : ℝ) * (P / 2) ≤ 1 := by
    have hpow : (N : ℝ) ≤ Q ^ N := by
      have h : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
      exact h.trans (pow_le_pow_left₀ (by norm_num) hQ _)
    have hP' : 0 < Q ^ N := by positivity
    dsimp [P]
    rw [inv_eq_one_div, ← mul_div_assoc, mul_one_div]
    exact (div_le_div_of_nonneg_right ((div_le_one hP').mpr hpow) (by norm_num)).trans (by norm_num)
  have hX (s : Finset I) (σ : Equiv.Perm I) :
      (∑ j, if σ j ∈ s then 0 else ((σ j).2.val : ℝ) * γ * u (f j)) +
        max (∑ i ∈ s, ((i.2.val : ℝ) * γ) * u (f (σ.symm i))) 0 ≤ X := by
    let z (j : I) := ((σ j).2.val : ℝ) * γ * u (f j)
    have hsplit' := _root_.AbcTwoNinths.ExteriorE1.splitPhaseSum s σ z (fun j =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hγ) (hu0 _))
    simp only [z, σ.apply_symm_apply] at hsplit'
    rw [hsplit']
    calc
      _ ≤ ∑ j : I, ((((σ j).2.val * (f j).1.val : ℕ) : ℝ) * Real.log (q₁ : ℝ) +
            (((σ j).2.val * (f j).2.val : ℕ) : ℝ) * Real.log (q₂ : ℝ) + P / 2) := by
        apply Finset.sum_le_sum
        intro j _
        have h := (he (σ j) j).2
        have hneg := neg_abs_le ((σ j).2.val * ε (f j))
        push_cast
        have e := congrArg (fun t : ℝ => ((σ j).2.val : ℝ) * t) (hphase (f j))
        ring_nf at e ⊢
        linarith only [h, hneg, e]
      _ ≤ X := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum,
          Finset.sum_const, Finset.card_univ, I, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        have h₁ : ((∑ j, (σ j).2.val * (f j).1.val : ℕ) : ℝ) ≤ V₁ := by exact_mod_cast hV₁ σ
        have h₂ : ((∑ j, (σ j).2.val * (f j).2.val : ℕ) : ℝ) ≤ V₂ := by exact_mod_cast hV₂ σ
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right h₁ (Real.log_pos hq₁').le)
          (mul_le_mul_of_nonneg_right h₂ (Real.log_pos hq₂').le)) hPmass
  rw [_root_.AbcTwoNinths.ExteriorE1.detBinomEqDetMonofact (fun j => _root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (f j)) g, hsplit]
  have hh := _root_.AbcTwoNinths.ExteriorE1.determinantSumEnvelope f u ε γ M P W X ((Real.exp 1 / Q) ^ E₁)
    (by dsimp [M]; positivity) (by dsimp [P]; positivity) (by dsimp [W]; positivity)
    hu he hw hX (fun s => by simpa only [P, W, N, mul_div_assoc] using hA s)
  refine hh.trans_eq ?_
  dsimp [X]
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by linarith : (0 : ℝ) < q₁), Real.exp_log (by linarith : (0 : ℝ) < q₂)]
  ring

/--
Bounds the real interpolation determinant at radius Q under the phase and logarithmic-form bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realVarRadiusDetBound {K L R S b₁ b₂ : ℕ}
    (hK : 1 ≤ K) (hL : 2 ≤ L) (_hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (f : (Fin K × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle R S) (V₁ V₂ : ℕ)
    (hV₁ : ∀ σ : Equiv.Perm (Fin K × Fin L), ∑ j, (σ j).2.val * (f j).1.val ≤ V₁)
    (hV₂ : ∀ σ : Equiv.Perm (Fin K × Fin L), ∑ j, (σ j).2.val * (f j).2.val ≤ V₂)
    (Q : ℝ) (hQ : 2 ≤ Q) (hS : 2 * (L - 1) * S ≤ K * L)
    (hγM : (Real.log (q₁ : ℝ) / (b₂ : ℝ)) * ((R * b₂ + S * b₁ : ℕ) : ℝ) ≤ (K : ℝ) / Q)
    (hΛ : |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤
      (((K * L : ℕ) : ℝ) * Q ^ (K * L))⁻¹) :
    let N := K * L
    let E₁ := N * K * (L - 1) / 2
    let M : ℝ := ((R * b₂ + S * b₁ : ℕ) : ℝ)
    |(Matrix.of fun i j : Fin K × Fin L =>
      (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) i.1.val : ℝ) *
      (q₁ : ℝ) ^ (i.2.val * (f j).1.val) * (q₂ : ℝ) ^ (i.2.val * (f j).2.val)).det| ≤
      (2 : ℝ) ^ N * (N.factorial : ℝ) *
      (∏ i : Fin K × Fin L, M ^ i.1.val / (i.1.val.factorial : ℝ)) *
      (Real.exp 1 / Q) ^ E₁ * (q₁ : ℝ) ^ V₁ * (q₂ : ℝ) ^ V₂ * Real.exp 1 := by
  simpa only [_root_.AbcTwoNinths.Basic.nodeZ, mul_assoc] using
    (_root_.AbcTwoNinths.ExteriorE1.realVarRadiusDetBoundFrom hK hL hb₂ q₁ q₂ hq₁ hq₂ f V₁ V₂ hV₁ hV₂ Q hQ hS hγM hΛ
      (_root_.AbcTwoNinths.ExteriorE1.monofactDetEqSumExpSum q₁ q₂ (by linarith) (by linarith) hb₂ f)
      (fun s => (_root_.AbcTwoNinths.ExteriorE1.subsetOrderBoundsAndAbsorb hK hL s
        (le_trans (by norm_num) hQ)).2.2))

end

end AbcTwoNinths.ExteriorE1
