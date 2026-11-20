/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.PrimeSupportCount
public import AbcTwoNinths.Paper.S2_PolyCap.WeightedValuationSelection
public import AbcTwoNinths.Paper.S2_PolyCap.OddSideSignChoice
public import Mathlib.Data.Nat.Squarefree

/-!
# Odd Side Prime Selection

For an ordered triple of logarithmic height greater than two, an odd side contains a prime whose
weighted valuation is at least the logarithmic height divided by twice the number of distinct prime
divisors of the triple. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddSideFullCountSameSide`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
An ordered triple with logarithmic height `H > 2` has an odd side `M` among `b` and `c` with an odd prime
`p` satisfying the same-side identity and `H ≤ 2 * r * v_p(M) * log p`, where `r` counts the prime divisors
of `abc` and satisfies `1 ≤ r ≤ rad(abc)` and `r ≤ 2 * log(rad(abc))`.
-/
theorem oddSideFullCountSameSide (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b) (hH : 2 < t.logHeight) :
    let r := (t.a * t.b * t.c).primeFactors.card
    ∃ M p : ℕ,
      (M = t.b ∨ M = t.c) ∧ ¬ 2 ∣ M ∧ p.Prime ∧ 2 < p ∧ p ∣ M ∧
      0 < M.factorization p ∧ p ∣ t.radical ∧ 3 ≤ t.radical ∧ 1 < t.logRadical ∧
      1 ≤ r ∧ (r : ℝ) ≤ 2 * t.logRadical ∧ r ≤ t.radical ∧
      t.logHeight ≤ 2 * (r : ℝ) * ((M.factorization p : ℝ) * log (p : ℝ)) ∧
      _root_.AbcTwoNinths.PolyCap.SameSide t M p := by
  let S := (t.a * t.b * t.c).primeFactors
  have ha := t.apos
  have hb := t.bpos
  have hadd := t.add
  have hc : 0 < t.c := by omega
  have logtwo : log (2 : ℝ) ≤ 1 := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hc2 : 2 < t.c := by
    by_contra! h
    have hlog := log_le_log (by exact_mod_cast hc : 0 < (t.c : ℝ))
      (by exact_mod_cast h : (t.c : ℝ) ≤ 2)
    change t.logHeight ≤ log 2 at hlog
    linarith
  obtain ⟨M, p, hM, ho, hp, hp2, hd, hfac, hw⟩ :=
    _root_.AbcTwoNinths.PolyCap.weightedValuationSelector t hord hc2
  have hprod : M ∣ t.a * t.b * t.c := by
    rcases hM with h | h
    · rw [h]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · rw [h]
      exact dvd_mul_left _ _
  have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, hd.trans hprod, by positivity⟩
  have hpR : p ∣ t.radical := Finset.dvd_prod_of_mem _ hpS
  have hRpos : 0 < t.radical :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hR : 3 ≤ t.radical := (show 3 ≤ p by omega).trans (Nat.le_of_dvd hRpos hpR)
  have hW : 1 < t.logRadical := (lt_log_iff_exp_lt (by exact_mod_cast hRpos)).2
    ((exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).trans_le
      (by exact_mod_cast hR : (3 : ℝ) ≤ t.radical))
  have hsub : S ⊆ Finset.Icc 1 t.radical := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hq).one_le,
      Nat.le_of_dvd hRpos (Finset.dvd_prod_of_mem _ hq)⟩
  have hrR : S.card ≤ t.radical := by simpa using Finset.card_le_card hsub
  have logtwo' : (1 : ℝ) / 2 ≤ log 2 := by
    linarith [log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num),
      log_inv (2 : ℝ)]
  have hlogs : t.logRadical = ∑ q ∈ S, log (q : ℝ) := by
    unfold _root_.AbcTwoNinths.Basic.Triple.logRadical _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical
    rw [Nat.cast_prod, log_prod]
    intro q hq
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hsum : (∑ q ∈ S, (1 : ℝ) / 2) ≤ ∑ q ∈ S, log (q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact logtwo'.trans (log_le_log (by norm_num)
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le))
  rw [← hlogs] at hsum
  simp [nsmul_eq_mul] at hsum
  refine ⟨M, p, hM, ho, hp, hp2, hd, hfac, hpR, hR, hW,
    Finset.card_pos.mpr ⟨p, hpS⟩, by change (S.card : ℝ) ≤ _; linarith,
    hrR, by linarith, _root_.AbcTwoNinths.PolyCap.sameSideOfSelected t hord hM hp hp2 hd⟩

end

end AbcTwoNinths.PolyCap
