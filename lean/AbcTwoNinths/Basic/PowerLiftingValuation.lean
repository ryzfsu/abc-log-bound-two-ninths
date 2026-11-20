/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PrincipalUnitPowers

/-!
# Power Lifting Valuation

The module bounds the loss in local depth when reducing an unrestricted exponent pair by its gcd.

## Main results
* `AbcTwoNinths.Basic.unboundedLteReduce`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section



/-- The logarithmic exponent scale for the two-logarithm estimate, bounded below by four. -/
noncomputable def unboundedD (p m n : ℕ) (A B : ℝ) : ℝ :=
  max 4 ((2 + Real.log ((m : ℝ) / B + (n : ℝ) / A)) / Real.log p)

/--
The valuation of the gcd of two positive exponents is bounded by twice the squared exponent scale times the product of the height parameters.
-/
theorem unboundedGcdLoss (p m n : ℕ) (A B : ℝ)
    (hp : p.Prime) (hodd : 2 < p) (hm : 0 < m) (hn : 0 < n)
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (padicValNat p (m.gcd n) : ℝ) ≤ 2 * _root_.AbcTwoNinths.Basic.unboundedD p m n A B ^ 2 * (A * B) := by
  let : Fact p.Prime := ⟨hp⟩
  let g := m.gcd n
  let U : ℝ := (m : ℝ) / B + (n : ℝ) / A
  let ℓ := Real.log (p : ℝ)
  let D := _root_.AbcTwoNinths.Basic.unboundedD p m n A B
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hd : p ^ padicValNat p g ∣ g :=
    (padicValNat_dvd_iff_le hg.ne').mpr le_rfl
  have hpm : ((p : ℝ) ^ padicValNat p g) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hm (hd.trans (Nat.gcd_dvd_left m n))
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  have hp0 : (0 : ℝ) < p := by positivity
  have hℓ : 1 < ℓ := (Real.lt_log_iff_exp_lt hp0).2 (Real.exp_one_lt_three.trans_le hp3)
  have hℓ0 : 0 < ℓ := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hB0 : 0 < B := by linarith
  have hAB : 1 ≤ A * B := by nlinarith
  have hmU : (m : ℝ) ≤ U * B := by
    apply (div_le_iff₀ hB0).mp
    dsimp [U]
    exact le_add_of_nonneg_right (by positivity)
  have hv := Real.log_le_log (pow_pos hp0 _) (hpm.trans hmU)
  rw [Real.log_pow, Real.log_mul hU.ne' hB0.ne'] at hv
  have hD : 4 ≤ D := le_max_left _ _
  have hDU : 2 + Real.log U ≤ D * ℓ :=
    (div_le_iff₀ hℓ0).mp (le_max_right _ _)
  have hlogB : Real.log B ≤ A * B := by
    nlinarith [Real.log_le_sub_one_of_pos hB0, mul_nonneg (show 0 ≤ A-1 by linarith) hB0.le]
  have hscaled : (padicValNat p g : ℝ) * ℓ ≤ (D + A * B) * ℓ := by
    nlinarith [mul_nonneg (show 0 ≤ A*B by linarith) (show 0 ≤ ℓ-1 by linarith)]
  have hbound : D + A*B ≤ 2 * D^2 * (A*B) := by
    have hD2 : D + 1 ≤ 2 * D^2 := by nlinarith [sq_nonneg (D - 4)]
    calc
      D + A*B ≤ (D + 1)*(A*B) := by
        nlinarith [mul_nonneg (show 0 ≤ D by linarith) (show 0 ≤ A*B-1 by linarith)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hD2 (by linarith)
  exact ((mul_le_mul_iff_left₀ hℓ0).mp (by simpa only [mul_comm ℓ] using hscaled)).trans hbound

/--
At an odd prime, reduction to coprime exponents bounds the valuation of the original difference of powers with an explicit additive loss.
-/
theorem unboundedLteReduce (p m n : ℕ) (a b : ℚ) (A B : ℝ)
    (hp : p.Prime) (hodd : 2 < p) (ha : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b)
    (hi : _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b) (hm : 0 < m) (hn : 0 < n)
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧
      c ≤ m ∧ d ≤ n ∧
      (padicValRat p (a^m - b^n) : ℝ) ≤
        (padicValRat p (a^c - b^d) : ℝ) + 2 * _root_.AbcTwoNinths.Basic.unboundedD p m n A B ^ 2 * (A * B) := by
  let g := m.gcd n
  let c := m / g
  let d := n / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hmc : c * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have hnd : d * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have hc : 0 < c := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hmc
    omega
  have hd : 0 < d := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hnd
    omega
  refine ⟨c, d, hc, hd, Nat.coprime_div_gcd_div_gcd hg, Nat.div_le_self _ _,
    Nat.div_le_self _ _, ?_⟩
  have h := _root_.AbcTwoNinths.Basic.exponentLTE p c d g a b hp hodd ha hb hi hc hd hg
  rw [hmc, hnd] at h
  rw [h]
  push_cast
  rw [padicValRat.of_nat]
  simpa [g] using add_le_add_right (_root_.AbcTwoNinths.Basic.unboundedGcdLoss p m n A B hp hodd hm hn hA hB)
    (padicValRat p (a^c - b^d) : ℝ)

end

end AbcTwoNinths.Basic
