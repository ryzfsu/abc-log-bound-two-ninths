/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.SourceOrder

/-!
# Source Support

The module bounds the support and logarithmic weight of the squared source exponent vector. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.squaredSourceSupportWeight`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
Every prime dividing the product of the squared source coordinates divides the product of the three entries of the triple.
-/
theorem squaredSourceSupportSubset (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) :
    ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2 * (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2).primeFactors ⊆
      (t.a * t.b * t.c).primeFactors := by
  have hc : t.c ≠ 0 := by rw [← t.add]; exact (Nat.add_pos_left t.apos _).ne'
  have ht := mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hprod : p ∣ (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 * (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 := by
    rw [← mul_pow] at hd
    exact hprime.dvd_of_dvd_pow hd
  have hsrc : (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 * (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ∣ t.a * t.b * t.c := by
    cases s
    · change t.c * t.b ∣ t.a * t.b * t.c
      exact ⟨t.a, by ac_rfl⟩
    · change t.c * t.a ∣ t.a * t.b * t.c
      exact ⟨t.b, by ac_rfl⟩
    · change t.b * t.a ∣ t.a * t.b * t.c
      exact ⟨t.c, by ac_rfl⟩
  exact Nat.mem_primeFactors.mpr ⟨hprime, hprod.trans hsrc, ht⟩

/--
The sum of the logarithms of the primes supporting the squared source pair is at most three times the log-radical scale. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem squaredSourceSupportWeight (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) :
    (∑ p ∈ ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2 * (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2).primeFactors,
      Real.log (p : ℝ)) ≤ 3 * t.thirdLogRadical := by
  have hfull : (∑ p ∈ (t.a * t.b * t.c).primeFactors, Real.log (p : ℝ)) = 3 * t.thirdLogRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical
    push_cast
    rw [Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    ring
  rw [← hfull]
  apply Finset.sum_le_sum_of_subset_of_nonneg (_root_.AbcTwoNinths.ExteriorE2.squaredSourceSupportSubset t s)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)

end

end AbcTwoNinths.ExteriorE2
