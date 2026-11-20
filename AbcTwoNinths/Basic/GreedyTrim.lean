/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Greedy Trim

The module greedily trims a prime factorization to a prescribed logarithmic capacity.

## Main results
* `AbcTwoNinths.Basic.trimCapacity`
* `AbcTwoNinths.Basic.trimFactorization`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

open Real

section

private theorem greedy (Q : ℕ) (hQ : Q ≠ 0) (A : ℕ) (hA : A ≠ 0) (B : ℝ)
    (hinit : log (A : ℝ) ≤ B) (htotal : B / 2 ≤ log ((A * Q : ℕ) : ℝ))
    (hp : ∀ p : ℕ, p.Prime → p ∣ Q → log (p : ℝ) ≤ B / 2) :
    ∃ M : ℕ, A ∣ M ∧ M ∣ A * Q ∧ B / 2 ≤ log (M : ℝ) ∧ log (M : ℝ) ≤ B := by
  induction Q using Nat.strong_induction_on generalizing A with
  | h Q ih =>
    by_cases hstop : B / 2 ≤ log (A : ℝ)
    · exact ⟨A, dvd_rfl, dvd_mul_right .., hstop, hinit⟩
    have hQ1 : Q ≠ 1 := by
      intro h
      apply hstop
      simpa [h] using htotal
    let p := Q.minFac
    have hpp : p.Prime := Nat.minFac_prime hQ1
    have hpd : p ∣ Q := Nat.minFac_dvd Q
    obtain ⟨Q', hsplit⟩ := hpd
    have hQ' : Q' ≠ 0 := by
      intro h
      simp [h] at hsplit
      exact hQ hsplit
    have hlt : Q' < Q := by
      rw [hsplit]
      simpa using Nat.mul_lt_mul_of_pos_right hpp.one_lt (Nat.pos_of_ne_zero hQ')
    have hsum : log ((A * p : ℕ) : ℝ) = log (A : ℝ) + log (p : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hA)
        (by exact_mod_cast hpp.ne_zero)]
    have hprod : A * p * Q' = A * Q := by rw [hsplit, Nat.mul_assoc]
    obtain ⟨M, hAM, hMd, hLow, hHigh⟩ := ih Q' hlt hQ' (A * p) (mul_ne_zero hA hpp.ne_zero)
      (by rw [hsum]; linarith [hp p hpp (hsplit ▸ dvd_mul_right p Q')])
      (by rwa [hprod])
      (fun q hq hqd => hp q hq (hsplit ▸ hqd.trans (dvd_mul_left Q' p)))
    exact ⟨M, (dvd_mul_right A p).trans hAM, hprod ▸ hMd, hLow, hHigh⟩

/-- Trim a capacity integer whose 2-adic exponent is not one. -/
theorem trimCapacity {N : ℕ} {B : ℝ} (hN : N ≠ 0)
    (hdyad : ¬ 2 ∣ N ∨ 4 ∣ N) (hfour : log (4 : ℝ) ≤ B)
    (htotal : B / 2 ≤ log (N : ℝ))
    (hcap : ∀ p : ℕ, p.Prime → p ∣ N → log (p : ℝ) ≤ B) :
    ∃ M : ℕ, M ∣ N ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧
      B / 2 ≤ log (M : ℝ) ∧ log (M : ℝ) ≤ B := by
  by_cases hbig : ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ B / 2 < log (p : ℝ)
  · obtain ⟨p, hpp, hpd, hpl⟩ := hbig
    have hlog : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hp2 : ¬ 2 ∣ p := by
      intro hd
      have he : 2 = p := (Nat.dvd_prime hpp).mp hd |>.resolve_left (by decide)
      subst p
      linarith
    exact ⟨p, hpd, Or.inl hp2, hpl.le, hcap p hpp hpd⟩
  have hsmall (p : ℕ) (hpp : p.Prime) (hpd : p ∣ N) : log (p : ℝ) ≤ B / 2 :=
    le_of_not_gt (fun hl => hbig ⟨p, hpp, hpd, hl⟩)
  rcases hdyad with hodd | ⟨Q, hsplit⟩
  · have h0 : (0 : ℝ) ≤ B := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)).trans hfour
    obtain ⟨M, _, hd, hLow, hHigh⟩ := greedy N hN 1 (by decide) B
      (by simpa using h0) (by simpa using htotal) hsmall
    have hd' : M ∣ N := by simpa using hd
    exact ⟨M, hd', Or.inl (fun h => hodd (h.trans hd')), hLow, hHigh⟩
  · have hQ : Q ≠ 0 := by intro h; exact hN (by simp [hsplit, h])
    obtain ⟨M, hd₄, hd, hLow, hHigh⟩ := greedy Q hQ 4 (by decide) B hfour
      (by rwa [← hsplit])
      (fun p hp hpd => hsmall p hp (hsplit ▸ hpd.trans (dvd_mul_left Q 4)))
    exact ⟨M, hsplit ▸ hd, Or.inr hd₄, hLow, hHigh⟩

private theorem logProdPow (s : Finset ℕ) (f : ℕ → ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    log ((∏ p ∈ s, p ^ f p : ℕ) : ℝ) = ∑ p ∈ s, (f p : ℝ) * log (p : ℝ) := by
  classical
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (hs p hp).ne_zero))]
  simp only [Real.log_pow]

/-- C7a with the budget parameter combined into B. -/
theorem trimFactorization {n Λ : ℕ} {B : ℝ} (hn : n ≠ 0) (hΛ : 0 < Λ)
    (hfour : log (4 : ℝ) ≤ B)
    (hcap : ∀ p ∈ n.primeFactors, log (p : ℝ) ≤ B)
    (hbudget : B ≤ log (n : ℝ) / Λ -
      ∑ p ∈ n.primeFactors, log (p : ℝ)) :
    ∃ M : ℕ, 1 < M ∧ M ^ Λ ∣ n ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧
      B / 2 ≤ log (M : ℝ) ∧ log (M : ℝ) ≤ B := by
  classical
  let S := n.primeFactors
  let k (p : ℕ) := n.factorization p / Λ
  let e (p : ℕ) := if p = 2 ∧ k p = 1 then 0 else k p
  let N := ∏ p ∈ S, p ^ e p
  have hprime (p : ℕ) (hp : p ∈ S) := Nat.prime_of_mem_primeFactors hp
  have hnprod : (∏ p ∈ S, p ^ n.factorization p) = n :=
    (Nat.prod_primeFactors_pow_factorization hn).symm
  have e_le (p : ℕ) : e p ≤ k p := by dsimp [e]; split <;> omega
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (hprime p hp).ne_zero
  have hNd : N ^ Λ ∣ n := by
    rw [← hnprod]
    change (∏ p ∈ S, p ^ e p) ^ Λ ∣ ∏ p ∈ S, p ^ n.factorization p
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    rw [← pow_mul]
    exact pow_dvd_pow _ ((Nat.le_div_iff_mul_le hΛ).mp (e_le p))
  have hN2 : N.factorization 2 = if 2 ∈ S then e 2 else 0 := by
    change (∏ p ∈ S, p ^ e p).factorization 2 = _
    rw [Nat.factorization_prod_apply (fun p hp => pow_ne_zero _ (hprime p hp).ne_zero)]
    calc
      _ = ∑ p ∈ S, if p = 2 then e 2 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(hprime p hp).factorization_pow]
        split_ifs with h
        · subst p; simp
        · simp [h]
      _ = _ := Finset.sum_ite_eq' S 2 (fun _ => e 2)
  have hdyad : ¬ 2 ∣ N ∨ 4 ∣ N := by
    have he : e 2 ≠ 1 := by
      intro he
      simp only [e, true_and] at he
      split_ifs at he; omega
    have h0 : N.factorization 2 ≠ 1 := by rw [hN2]; split <;> omega
    by_cases h : 2 ∣ N
    · right
      have hb := (Nat.prime_two.dvd_iff_one_le_factorization hN).mp h
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hN).mpr (show 2 ≤ N.factorization 2 by omega)
    · exact Or.inl h
  have hlogN : log (N : ℝ) = ∑ p ∈ S, (e p : ℝ) * log (p : ℝ) :=
    logProdPow S e hprime
  have hlogn : log (n : ℝ) / Λ =
      ∑ p ∈ S, ((n.factorization p : ℝ) / Λ) * log (p : ℝ) := by
    have h := logProdPow S n.factorization hprime
    rw [hnprod] at h
    rw [h, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hfloor (p : ℕ) : (n.factorization p : ℝ) / Λ ≤ (k p : ℝ) + 1 := by
    have hh : n.factorization p < (k p + 1) * Λ :=
      (Nat.div_lt_iff_lt_mul hΛ).mp (Nat.lt_succ_self (k p))
    exact le_of_lt ((div_lt_iff₀ (by exact_mod_cast hΛ)).mpr (by exact_mod_cast hh))
  have he (p : ℕ) : (k p : ℝ) ≤ (e p : ℝ) + (if p = 2 then 1 else 0) := by
    simp only [e]
    by_cases h : p = 2
    · simp only [h, true_and, ite_true]
      split <;> norm_cast <;> omega
    · simp [h]
  have hsums :
      log (n : ℝ) / Λ ≤ log (N : ℝ) +
        (∑ p ∈ S, log (p : ℝ)) + log 2 := by
    rw [hlogn, hlogN]
    calc
      _ ≤ ∑ p ∈ S, (((e p : ℝ) + 1) * log (p : ℝ) +
          (if p = 2 then log 2 else 0)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpos : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le)
        have hh := mul_le_mul_of_nonneg_right (hfloor p) hpos
        have hhh := mul_le_mul_of_nonneg_right (he p) hpos
        by_cases h : p = 2
        · subst p; simp only [ite_true] at hhh ⊢; push_cast at *; nlinarith
        · simp only [h, ite_false, add_zero] at hhh ⊢; nlinarith
      _ ≤ _ := by
        simp only [add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']
        split <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hlogfour : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have htotal : B / 2 ≤ log (N : ℝ) := by
    change B ≤ log (n : ℝ) / Λ - ∑ p ∈ S, log (p : ℝ) at hbudget
    linarith
  have hNd' : N ∣ n := (dvd_pow_self N (Nat.ne_of_gt hΛ)).trans hNd
  obtain ⟨M, hMd, hMdyad, hML, hMU⟩ := _root_.AbcTwoNinths.Basic.trimCapacity hN hdyad hfour htotal
    (fun p hp hpd => hcap p (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hNd', hn⟩))
  have hM : 1 < M := by
    by_contra! hh
    have hM0 : M ≠ 0 := ne_zero_of_dvd_ne_zero hN hMd
    have hM1 : M = 1 := by omega
    simp [hM1] at hML
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  exact ⟨M, hM, (pow_dvd_pow_of_dvd hMd Λ).trans hNd, hMdyad, hML, hMU⟩

end

end AbcTwoNinths.Basic
