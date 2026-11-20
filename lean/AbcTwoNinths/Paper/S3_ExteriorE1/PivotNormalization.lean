/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.QuotientHeight
public import AbcTwoNinths.Paper.S3_ExteriorE1.PrimitiveQuotient

/-!
# Pivot Normalization

The module normalizes the pivot coordinate and bounds the weight of the remaining quotient support. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.normalizePivot`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
The sum of the logarithms of primes in the quotient support is at most three times the radical parameter.
-/
theorem quotientSupportWeight (t : _root_.AbcTwoNinths.Basic.Triple) :
    (∑ i : _root_.AbcTwoNinths.Basic.supp t, Real.log (i.val : ℝ)) ≤ 3 * t.thirdLogRadical := by
  let S := _root_.AbcTwoNinths.Basic.supp t
  have hc : 0 < t.c := by have := t.apos; have := t.add; omega
  have hn : t.a * t.b * t.c ≠ 0 :=
    mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc.ne'
  have hs : S ⊆ (t.a * t.b * t.c).primeFactors := by
    intro p hp
    rcases Finset.mem_union.mp hp with hb | hc'
    · exact Nat.primeFactors_mono
        ((Nat.dvd_mul_left t.b t.a).trans (Nat.dvd_mul_right (t.a * t.b) t.c)) hn hb
    · exact Nat.primeFactors_mono (Nat.dvd_mul_left t.c (t.a * t.b)) hn hc'
  have hlog : Real.log (t.radical : ℝ) = ∑ p ∈ (t.a * t.b * t.c).primeFactors, Real.log (p : ℝ) := by
    rw [_root_.AbcTwoNinths.Basic.Triple.radical, _root_.AbcTwoNinths.Basic.radical, Nat.cast_prod, Real.log_prod]
    exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hx : Real.log (t.radical : ℝ) = 3 * t.thirdLogRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical
    ring
  change (∑ i ∈ S.attach, Real.log (i.val : ℝ)) ≤ _
  rw [Finset.sum_attach S (fun p => Real.log (p : ℝ)), ← hx, hlog]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)

/--
A common sign makes a nonzero maximal coordinate positive and bounds every absolute coordinate by that pivot. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem normalizePivot {ι : Type*} (w : ι → ℤ) (r : ι)
    (hr : w r ≠ 0) (hmax : ∀ i, |w i| ≤ |w r|) :
    ∃ v : ι → ℤ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (∀ i, w i = s * v i) ∧
      v r = |w r| ∧ 0 < v r ∧ (∀ i, |v i| ≤ v r) := by
  by_cases h : 0 ≤ w r
  · refine ⟨w, 1, Or.inl rfl, fun i => (one_mul _).symm, ?_, ?_, ?_⟩
    · exact (abs_of_nonneg h).symm
    · omega
    · simpa only [abs_of_nonneg h] using hmax
  · refine ⟨fun i => -w i, -1, Or.inr rfl, fun i => by ring, ?_, ?_, ?_⟩
    · exact (abs_of_neg (lt_of_not_ge h)).symm
    · exact neg_pos.mpr (lt_of_not_ge h)
    · intro i
      simpa only [abs_neg, abs_of_neg (lt_of_not_ge h)] using hmax i

end

end AbcTwoNinths.ExteriorE1
