/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.FloorBudgetTrim
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmoothPartFactorization

/-!
# Modulus Share Selection

The module chooses a modulus carrying a specified share of the small-prime valuation mass. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.modulusShareSelection`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
Sufficient smooth valuation mass yields a modulus of log size between B/2 and B whose positive power captures at least P/16 in log mass. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem modulusShareSelection {A : ℕ} {Q B P : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hfour : Real.log (4 : ℝ) ≤ B)
    (hQ : Q ≤ Real.exp B) (hlarge : 8 * B ≤ P)
    (hrad : ∑ q ∈ A.primeFactors, Real.log (q : ℝ) ≤ 2 * B)
    (hmass : P ≤ ∑ q ∈ _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q,
      (padicValNat q A : ℝ) * Real.log (q : ℝ)) :
    ∃ M L : ℕ, 2 ≤ M ∧ 0 < L ∧ M ^ L ∣ _root_.AbcTwoNinths.ExteriorE2.smoothPart A Q ∧ M ^ L ∣ A ∧
      (¬ 2 ∣ M ∨ 4 ∣ M) ∧ B / 2 ≤ Real.log (M : ℝ) ∧
      Real.log (M : ℝ) ≤ B ∧ P / 16 ≤ (L : ℝ) * Real.log (M : ℝ) := by
  classical
  let n := _root_.AbcTwoNinths.ExteriorE2.smoothPart A Q
  have hsub : _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q ⊆ A.primeFactors := Finset.filter_subset _ _
  obtain ⟨hnA, hlog⟩ := _root_.AbcTwoNinths.ExteriorE2.smoothPartFactorization hA Q
  have hn : 0 < n := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hA.ne' hnA)
  have hmass' : P ≤ Real.log (n : ℝ) := by
    rw [hlog]
    convert hmass using 1
    apply Finset.sum_congr rfl
    intro q hq
    rw [Nat.factorization_def A (Nat.prime_of_mem_primeFactors (hsub hq))]
  have hsmooth (q : ℕ) (hq : q ∈ n.primeFactors) : q ∈ _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q := by
    have hp := Nat.prime_of_mem_primeFactors hq
    have hd := (Nat.mem_primeFactors.mp hq).2.1
    change q ∣ ∏ j ∈ _root_.AbcTwoNinths.ExteriorE2.smoothPrimeFactors A Q, j ^ A.factorization j at hd
    obtain ⟨j, hj, hjd⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun j => j ^ A.factorization j)).mp hd
    have hqj : q ∣ j := hp.dvd_of_dvd_pow hjd
    have he : q = j := ((Nat.dvd_prime (Nat.prime_of_mem_primeFactors (hsub hj))).mp
      hqj).resolve_left hp.ne_one
    simpa [he] using hj
  have hrad' : ∑ q ∈ n.primeFactors, Real.log (q : ℝ) ≤ 2 * B := by
    apply le_trans _ hrad
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => hsub (hsmooth q hq))
      (fun q hq _ => Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le))
  let r := P / (8 * B)
  let L := ⌈r⌉₊
  have h8 : 0 < 8 * B := by positivity
  have hr : 1 ≤ r := (le_div_iff₀ h8).mpr (by simpa using hlarge)
  have hlow : r ≤ (L : ℝ) := Nat.le_ceil r
  have hhigh : (L : ℝ) ≤ 2 * r := by
    have := Nat.ceil_lt_add_one (show 0 ≤ r by linarith)
    change (L : ℝ) < r + 1 at this
    linarith
  have hLr : 0 < (L : ℝ) := by linarith
  have hL : 0 < L := by exact_mod_cast hLr
  have hru : r * (8 * B) = P := div_mul_cancel₀ _ h8.ne'
  have hcapacity : 4 * B ≤ Real.log (n : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLr).mpr
    have h := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ 4 * B by positivity)
    nlinarith only [h, hru, hmass']
  obtain ⟨M, hM, hMd, hparity, hlo, hhi⟩ :=
    _root_.AbcTwoNinths.Basic.floorBudgetTrim hn (dvd_refl n) hL hfour
      (fun q hq => by
        have hp := Nat.prime_of_mem_primeFactors hq
        have hqQ : (q : ℝ) ≤ Q := (Finset.mem_filter.mp (hsmooth q hq)).2
        exact (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).2 (hqQ.trans hQ))
      (by linarith)
  refine ⟨M, L, hM, hL, hMd, hMd.trans hnA, hparity, hlo, hhi, ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hlow (show 0 ≤ B / 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hlo hLr.le
  nlinarith only [hru, h₁, h₂]

end

end AbcTwoNinths.ExteriorE2
