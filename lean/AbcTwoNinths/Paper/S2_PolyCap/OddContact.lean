/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Odd Contact

The module expresses an odd side's logarithm as a sum of prime contributions and extracts a weighted contact bound. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddSideContact`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

private theorem logFactorization (n : ℕ) (hn : n ≠ 0) :
    log (n : ℝ) = ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * log (q : ℝ) := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  simp only [Nat.cast_prod, Nat.cast_pow] at h
  rw [h, Real.log_prod]
  · simp only [Real.log_pow]
  · intro q hq
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)

/--
An odd integer greater than one has a prime whose valuation mass times its number of prime factors bounds its logarithm.
-/
theorem oddWeightedContact (n : ℕ) (hn : 1 < n) (hodd : ¬ 2 ∣ n) :
    ∃ p ∈ n.primeFactors, p.Prime ∧ 2 < p ∧
      log (n : ℝ) ≤ (n.primeFactors.card : ℝ) * ((n.factorization p : ℝ) * log (p : ℝ)) := by
  classical
  have hs : n.primeFactors.Nonempty := ⟨n.minFac, Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩⟩
  let f := fun q : ℕ => (n.factorization q : ℝ) * log (q : ℝ)
  obtain ⟨p, hp, hmax⟩ := n.primeFactors.exists_max_image f hs
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := fun he => hodd (he ▸ Nat.dvd_of_mem_primeFactors hp)
  refine ⟨p, hp, hpr, lt_of_le_of_ne hpr.two_le hne.symm, ?_⟩
  rw [logFactorization n (by omega)]
  calc
    _ ≤ ∑ _q ∈ n.primeFactors, f p := Finset.sum_le_sum hmax
    _ = _ := by simp [f]

/--
For an ordered triple with H greater than two, twice the chosen odd side's prime count times one valuation mass bounds H. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem oddSideContact (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hH : 2 < t.logHeight) :
    ∃ M : ℕ, (M = t.b ∨ M = t.c) ∧ ¬ 2 ∣ M ∧
      ∃ p ∈ M.primeFactors, p.Prime ∧ 2 < p ∧
        t.logHeight ≤ 2 * (M.primeFactors.card : ℝ) * ((M.factorization p : ℝ) * log (p : ℝ)) := by
  have hc : 0 < t.c := by have := t.add; have := t.apos; omega
  have hb := t.bpos
  have hat := t.add
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
  have hsel (M : ℕ) (hM : 1 < M) (ho : ¬ 2 ∣ M) (hm : t.logHeight ≤ 2 * log (M : ℝ)) :
      ∃ p ∈ M.primeFactors, p.Prime ∧ 2 < p ∧
        t.logHeight ≤ 2 * (M.primeFactors.card : ℝ) * ((M.factorization p : ℝ) * log (p : ℝ)) := by
    obtain ⟨p, hp, hpr, hpo, hw⟩ := _root_.AbcTwoNinths.PolyCap.oddWeightedContact M hM ho
    exact ⟨p, hp, hpr, hpo, by linarith⟩
  by_cases hpar : 2 ∣ t.c
  · have hodd : ¬ 2 ∣ t.b := by
      intro hd
      have ha : 2 ∣ t.a := by omega
      have hg := Nat.dvd_gcd ha hd
      rw [t.coprime.gcd_eq_one] at hg
      norm_num at hg
    have hlogb : t.logHeight ≤ log 2 + log (t.b : ℝ) := by
      have hcb : (t.c : ℝ) ≤ 2 * t.b := by exact_mod_cast (show t.c ≤ 2 * t.b by omega)
      have hle := Real.log_le_log (by exact_mod_cast hc) hcb
      rwa [Real.log_mul (by norm_num) (by exact_mod_cast hb.ne')] at hle
    have hm : t.logHeight ≤ 2 * log (t.b : ℝ) := by linarith
    have hb' : 1 < t.b := by
      by_contra! h
      have hb1 : t.b = 1 := by omega
      simp [hb1] at hm
      linarith
    exact ⟨t.b, Or.inl rfl, hodd, hsel _ hb' hodd hm⟩
  · have hc' : 1 < t.c := by have := t.apos; omega
    exact ⟨t.c, Or.inr rfl, hpar, hsel _ hc' hpar (by change t.logHeight ≤ 2 * t.logHeight; linarith)⟩

end

end AbcTwoNinths.PolyCap
