/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Weighted Valuation Selection

The module selects a prime maximizing its logarithmically weighted valuation on an odd side. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.weightedValuationSelector`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

open scoped BigOperators

section

private theorem largeOddSide (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b) :
    ∃ x : ℕ, (x = t.b ∨ x = t.c) ∧ 0 < x ∧ ¬ 2 ∣ x ∧ t.c ≤ 2 * x := by
  have ha := t.apos
  have hb := t.bpos
  have hs := t.add
  by_cases h : 2 ∣ t.b
  · have hna : ¬ 2 ∣ t.a := by
      intro hd
      have hg := Nat.dvd_gcd hd h
      rw [show Nat.gcd t.a t.b = 1 from t.coprime] at hg
      norm_num at hg
    exact ⟨t.c, Or.inr rfl, by omega, by omega, by omega⟩
  · exact ⟨t.b, Or.inl rfl, hb, h, by omega⟩

private theorem weightedMaximum {x : ℕ} (hx : 1 < x) :
    ∃ p ∈ x.primeFactors, Real.log (x : ℝ) ≤
      (x.primeFactors.card : ℝ) * ((x.factorization p : ℝ) * Real.log p) := by
  let w (p : ℕ) : ℝ := (x.factorization p : ℝ) * Real.log p
  have hmem : x.minFac ∈ x.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd x, by omega⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image x.primeFactors w ⟨_, hmem⟩
  refine ⟨p, hp, ?_⟩
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ q ∈ x.primeFactors, w q) ≤ _
  calc
    _ ≤ ∑ q ∈ x.primeFactors, w p := Finset.sum_le_sum hmax
    _ = _ := by simp [nsmul_eq_mul, w]

/--
Selects a weighted valuation on an actual odd side without a cap or a band hypothesis. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem weightedValuationSelector (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b)
    (hc : 2 < t.c) :
    ∃ x p : ℕ, (x = t.b ∨ x = t.c) ∧ ¬ 2 ∣ x ∧ p.Prime ∧ 2 < p ∧
      p ∣ x ∧ 0 < x.factorization p ∧ t.logHeight - Real.log 2 ≤
        ((t.a * t.b * t.c).primeFactors.card : ℝ) *
          ((x.factorization p : ℝ) * Real.log p) := by
  obtain ⟨x, hxside, hxpos, hxodd, hxlarge⟩ := largeOddSide t hord
  have hx : 1 < x := by omega
  obtain ⟨p, hpm, hw⟩ := weightedMaximum hx
  obtain ⟨hp, hd, hxn⟩ := Nat.mem_primeFactors.mp hpm
  have hp2 : 2 < p := by
    have hple := hp.two_le
    by_contra! h
    have he : p = 2 := by omega
    exact hxodd (he ▸ hd)
  have hxsub : x.primeFactors ⊆ (t.a * t.b * t.c).primeFactors := by
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    have hdn : x ∣ t.a * t.b * t.c := by
      rcases hxside with rfl | rfl
      · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      · exact dvd_mul_left _ _
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans hdn, by
      have := t.apos
      have := t.bpos
      positivity⟩
  have hsize : t.logHeight ≤ Real.log 2 + Real.log (x : ℝ) := by
    unfold _root_.AbcTwoNinths.Basic.Triple.logHeight
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : (x : ℝ) ≠ 0)]
    apply Real.log_le_log
    · exact_mod_cast (show 0 < t.c by omega)
    · exact_mod_cast hxlarge
  have hwpos : 0 ≤ (x.factorization p : ℝ) * Real.log p :=
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega)))
  refine ⟨x, p, hxside, hxodd, hp, hp2, hd, hp.factorization_pos_of_dvd hxn hd, ?_⟩
  exact (sub_le_iff_le_add.mpr (by linarith)).trans
    (hw.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hxsub) hwpos))

end

end AbcTwoNinths.PolyCap
