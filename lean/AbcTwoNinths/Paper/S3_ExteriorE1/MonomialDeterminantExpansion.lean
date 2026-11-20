/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationMoments
public import AbcTwoNinths.Basic.DeterminantRowExpansion
public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Monomial Determinant Expansion

The module expands each monomial-factorial determinant row split as a finite exponential sum. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.monofactDetEqSumExpSum`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open scoped BigOperators

section

/--
The determinant with the specified exponential and perturbed rows equals the order-zero exponential sum at one.
-/
theorem detRowsEqExpSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) :
    (Matrix.of fun i j => u j ^ d i / ((d i).factorial : ℝ) *
      (if i ∈ s then Real.exp (l i * γ * u j)
        else Real.exp (l i * γ * u j) * (Real.exp (l i * ε j) - 1))).det =
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d 0 1 := by
  classical
  rw [Matrix.det_apply, _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.of_apply, pow_zero, mul_one]
  have hsum : (∑ i ∈ s, l i * γ * u (σ.symm i)) =
      ∑ j, if σ j ∈ s then l (σ j) * γ * u j else 0 := by
    calc
      _ = ∑ i : ι, if i ∈ s then l i * γ * u (σ.symm i) else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ = _ := by
        simpa only [σ.symm_apply_apply] using
          (Equiv.sum_comp σ (fun i => if i ∈ s then l i * γ * u (σ.symm i) else 0)).symm
  rw [hsum, Real.exp_sum, ← Equiv.prod_comp σ (fun i => ((d i).factorial : ℝ)⁻¹)]
  simp only [Units.smul_def, zsmul_eq_mul]
  rw [show ∀ a b c e : ℝ, a * (b * c * e) = b * (a * c * e) by intros; ring]
  apply congrArg (_ * ·)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : σ j ∈ s <;> simp [hj, div_eq_mul_inv] <;> ring

/--
The factorial-normalized monomial determinant equals the sum over all choices of unperturbed rows. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem monofactDetEqSumExpSum
    {K L R S b₁ b₂ : ℕ} (q₁ q₂ : ℚ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hb₂ : 0 < b₂) (f : (Fin K × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle R S) :
    let u : _root_.AbcTwoNinths.Basic.Rectangle R S → ℝ :=
      fun d => (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ d : ℝ)
    let Λ : ℝ := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)
    let γ : ℝ := Real.log (q₁ : ℝ) / (b₂ : ℝ)
    let ε : _root_.AbcTwoNinths.Basic.Rectangle R S → ℝ := fun d => (d.2.val : ℝ) * Λ / (b₂ : ℝ)
    (Matrix.of fun i j : Fin K × Fin L =>
      (u (f j) ^ i.1.val / (i.1.val.factorial : ℝ)) *
        ((q₁ : ℝ) ^ (i.2.val * (f j).1.val) * (q₂ : ℝ) ^ (i.2.val * (f j).2.val))).det =
    ∑ s : Finset (Fin K × Fin L),
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s (u ∘ f) (fun i => (i.2.val : ℝ)) (ε ∘ f) γ (fun i => i.1.val) 0 1 := by
  classical
  intro u Λ γ ε
  let I := Fin K × Fin L
  let A : Matrix I I ℝ := Matrix.of fun i j =>
    u (f j) ^ i.1.val / (i.1.val.factorial : ℝ) * Real.exp ((i.2.val : ℝ) * γ * u (f j))
  let B : Matrix I I ℝ := Matrix.of fun i j => A i j * (Real.exp ((i.2.val : ℝ) * ε (f j)) - 1)
  have hb : (b₂ : ℝ) ≠ 0 := by exact_mod_cast hb₂.ne'
  have phase (j : _root_.AbcTwoNinths.Basic.Rectangle R S) :
      γ * u j + ε j = (j.1.val : ℝ) * Real.log (q₁ : ℝ) +
        (j.2.val : ℝ) * Real.log (q₂ : ℝ) := by
    dsimp [γ, u, ε, Λ, _root_.AbcTwoNinths.Basic.nodeZ]
    push_cast
    field_simp [hb]
    ring
  have hpow (i j : I) :
      Real.exp ((i.2.val : ℝ) * (γ * u (f j) + ε (f j))) =
      (q₁ : ℝ) ^ (i.2.val * (f j).1.val) * (q₂ : ℝ) ^ (i.2.val * (f j).2.val) := by
    rw [phase, mul_add, Real.exp_add, ← mul_assoc, ← mul_assoc, ← Nat.cast_mul,
      ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (Rat.cast_pos.mpr hq₁), Real.exp_log (Rat.cast_pos.mpr hq₂)]
  have hAB : A + B = Matrix.of (fun i j : I =>
      u (f j) ^ i.1.val / (i.1.val.factorial : ℝ) *
        ((q₁ : ℝ) ^ (i.2.val * (f j).1.val) * (q₂ : ℝ) ^ (i.2.val * (f j).2.val))) := by
    ext i j
    simp only [Matrix.add_apply, A, B, Matrix.of_apply]
    rw [← hpow, mul_add, Real.exp_add]
    all_goals ring
  rw [← hAB, _root_.AbcTwoNinths.Basic.detAddEqSumPowerset]
  apply Finset.sum_congr rfl
  intro s _
  convert _root_.AbcTwoNinths.ExteriorE1.detRowsEqExpSum s (u ∘ f) (fun i => (i.2.val : ℝ)) (ε ∘ f) γ
    (fun i => i.1.val) using 2
  ext i j
  by_cases h : i ∈ s <;> simp [A, B, h, mul_assoc]

end

end AbcTwoNinths.ExteriorE1
