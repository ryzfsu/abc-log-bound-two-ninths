/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.FreshCount
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Prime Supply

The module uses the prime-count estimate and logarithmic exclusion budgets to supply fresh primes. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.adaptiveFreshSupply`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE2

section

/--
For S at least 64, the number of primes up to S is at least S divided by twice its logarithm.
-/
theorem halfPrimeCount {S : ℝ} (hS : 64 ≤ S) :
    S / (2 * Real.log S) ≤ (Nat.primeCounting ⌊S⌋₊ : ℝ) := by
  have hS₁ : 1 < S := by linarith
  have hp := Chebyshev.pi_ge' hS₁
  refine le_trans ?_ hp
  rw [div_mul_eq_div_div]
  apply (div_le_div_iff_of_pos_right (Real.log_pos hS₁)).2
  have h₁ : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h₂ : Real.log (16 : ℝ) < 4 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hy : 0 < (S + 2) / 16 := by linarith
  have hb := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by linarith : S + 2 ≠ 0) (by norm_num : (16:ℝ) ≠ 0)] at hb
  nlinarith [mul_le_mul_of_nonneg_left h₁.le (sub_nonneg.mpr hS₁.le)]

/--
The number of distinct prime factors of a positive integer times log 2 is at most its logarithm.
-/
theorem primeFactorLogBound {n : ℕ} (hn : 0 < n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  classical
  have hl : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    simpa using (Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le) :
      (∏ _p ∈ n.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ n.primeFactors, p)
  have hle := hl.trans (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))
  have hle' : (2 : ℝ)^n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hle
  simpa [Real.log_pow] using Real.log_le_log (by positivity) hle'

/-- If log R equals 3x, then 2R has at most 1 + 6x distinct prime factors. -/
theorem oldPrimeBudget {R : ℕ} (hR : 0 < R) {x : ℝ}
    (hx : Real.log R = 3 * x) : ((2*R).primeFactors.card : ℝ) ≤ 1 + 6*x := by
  let C := ((2*R).primeFactors.card : ℝ)
  have h := _root_.AbcTwoNinths.ExteriorE2.primeFactorLogBound (n := 2*R) (by positivity)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by exact_mod_cast hR.ne'), hx] at h
  change C * Real.log 2 ≤ _ at h
  have hl : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx₀ : 0 ≤ x := by
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith [Real.log_nonneg hR']
  by_cases hC : C ≤ 1
  · change C ≤ 1+6*x
    linarith
  · have hb := mul_le_mul_of_nonneg_left hl.le (show 0 ≤ C-1 by linarith)
    change C ≤ 1+6*x
    nlinarith

/--
Under the shell size bounds, the count up to the square root plus the number of prime divisors of 2R is at most S/(4 log S).
-/
theorem exclusionBudget {R : ℕ} (hR : 0 < R) {x e S : ℝ}
    (hx : Real.log R = 3*x) (he : 0 < e) (hS : 0 < S)
    (hlo : e*x ≤ Real.log S) (h128 : 128 ≤ Real.log S)
    (hE : 16*(1+6/e) ≤ Real.log S) :
    (Nat.primeCounting ⌊Real.sqrt S⌋₊ : ℝ) + ((2*R).primeFactors.card : ℝ) ≤
      S / (4*Real.log S) := by
  set L := Real.log S with hL
  have hLpos : 0 < L := by linarith
  have hpi : (Nat.primeCounting ⌊Real.sqrt S⌋₊ : ℝ) ≤ Real.sqrt S := by
    have h : Nat.primeCounting ⌊Real.sqrt S⌋₊ ≤ ⌊Real.sqrt S⌋₊ := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      exact (Finset.card_le_card (t := Finset.Icc 1 ⌊Real.sqrt S⌋₊) (by
        intro p hp
        obtain ⟨hb,hp⟩ := Nat.mem_primesLE.mp hp
        exact Finset.mem_Icc.mpr ⟨hp.one_lt.le,hb⟩)).trans (by simp)
    exact (by exact_mod_cast h : (Nat.primeCounting ⌊Real.sqrt S⌋₊ : ℝ) ≤ ⌊Real.sqrt S⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg S))
  have hs : Real.sqrt S = Real.exp (L/2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).1
    rw [Real.sq_sqrt hS.le, pow_two, ← Real.exp_add, show L/2+L/2 = L by ring,
      hL, Real.exp_log hS]
  have hsq : (L/4)^2 ≤ Real.sqrt S := by
    rw [hs, pow_two, show L/2=L/4+L/4 by ring, Real.exp_add]
    have heq : L/4 ≤ Real.exp (L/4) := by linarith [Real.add_one_le_exp (L/4)]
    exact mul_le_mul heq heq (by positivity) (Real.exp_pos _).le
  have hlin : 8*L ≤ Real.sqrt S := by
    nlinarith [mul_nonneg hLpos.le (sub_nonneg.mpr h128)]
  have hxL : x ≤ L/e := (le_div_iff₀ he).2 (by linarith)
  have hold : 1+6*x ≤ Real.sqrt S := by
    have h₁ : L*(1+6/e)*16 ≤ L*L := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hE hLpos.le
    have h₂ : L*(1+6/e) = L+6*(L/e) := by ring
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 4*L)).2
  calc
    _ ≤ (2*Real.sqrt S) * (4*L) := by
      exact mul_le_mul_of_nonneg_right (by linarith [_root_.AbcTwoNinths.ExteriorE2.oldPrimeBudget hR hx]) (by positivity)
    _ = Real.sqrt S * (8*L) := by ring
    _ ≤ Real.sqrt S * Real.sqrt S := mul_le_mul_of_nonneg_left hlin (Real.sqrt_nonneg _)
    _ = S := Real.mul_self_sqrt hS.le

/--
Under the shell size bounds, at least S/(4 log S) primes in the interval from sqrt S exclusive to S inclusive avoid 2R.
-/
theorem freshSupply {R : ℕ} (hR : 0 < R) {x e S : ℝ}
    (hx : Real.log R = 3*x) (he : 0 < e) (hS : 0 < S)
    (hlo : e*x ≤ Real.log S) (h128 : 128 ≤ Real.log S)
    (hE : 16*(1+6/e) ≤ Real.log S) :
    S/(4*Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ) := by
  have h64 : 64 ≤ S := by linarith [Real.log_le_sub_one_of_pos hS]
  exact _root_.AbcTwoNinths.ExteriorE2.freshCountLower hR.ne' (by linarith) (_root_.AbcTwoNinths.ExteriorE2.halfPrimeCount h64)
    (_root_.AbcTwoNinths.ExteriorE2.exclusionBudget hR hx he hS hlo h128 hE)

/--
Beyond the admissible threshold, at least M/(4 log M) fresh primes lie in the shell with adaptive cutoff M. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem adaptiveFreshSupply {R : ℕ} (hR : 0 < R) {p H η x : ℝ}
    (hx : Real.log R = 3*x) (a : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x)
    (hX : max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin η)) / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ x) :
    let S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
    S/(4*Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ) := by
  dsimp
  have he := _root_.AbcTwoNinths.ExteriorE2.marginPos a.eta_lt
  have hM := (_root_.AbcTwoNinths.ExteriorE2.shellSlack a).1
  have hcut : max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin η)) ≤ _root_.AbcTwoNinths.ExteriorE2.margin η*x := by
    simpa [mul_comm] using (div_le_iff₀ he).1 hX
  exact _root_.AbcTwoNinths.ExteriorE2.freshSupply hR hx he (_root_.AbcTwoNinths.ExteriorE2.MPos _ _ _ _) hM
    ((le_max_left _ _).trans (hcut.trans hM)) ((le_max_right _ _).trans (hcut.trans hM))

end

end AbcTwoNinths.ExteriorE2
