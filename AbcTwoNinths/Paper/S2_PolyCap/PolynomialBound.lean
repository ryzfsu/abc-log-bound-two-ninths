/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.RankDecomposition
public import AbcTwoNinths.Paper.S2_PolyCap.OddSidePrimeSelection
public import AbcTwoNinths.Paper.S2_PolyCap.OrderedPrimitiveSource

/-!
# Polynomial Bound

The logarithmic height of a primitive triple is bounded by an absolute constant times the twentieth
power of its radical. This is Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.polynomialCap`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

/-- Proposition 2.1 of the paper. This is used in Section 2 of the paper. -/
theorem polynomialCap : _root_.AbcTwoNinths.Statement.PolyCap := by
  apply _root_.AbcTwoNinths.PolyCap.polyCapOfMaster
  intro t ht hH
  obtain ⟨M, p₀, _, _, _, _, _, _, _, hR, hW, _, hrW, hrR, _, _⟩ :=
    _root_.AbcTwoNinths.PolyCap.oddSideFullCountSameSide t ht hH
  rcases _root_.AbcTwoNinths.PolyCap.orderedPrimitiveSource t ht hH with h | h
  · left
    have hr' : (((t.a * t.b * t.c).primeFactors.card : ℕ) : ℝ) ≤ t.radical := by exact_mod_cast hrR
    have hR' : (1 : ℝ) ≤ t.radical := by exact_mod_cast (show 1 ≤ t.radical by omega)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    calc
      _ ≤ (t.radical : ℝ)^2 := by gcongr
      _ ≤ (t.radical : ℝ)^3 := by
        simpa only [pow_succ] using (le_mul_of_one_le_right (sq_nonneg (t.radical : ℝ)) hR')
  · obtain ⟨p, S, e, hc, hp, ho, hpR, hr, hSr, hS, _, he, hprim, hn, hd, hl, hh⟩ := h
    have haway (j : S) : ¬ p ∣ j.val :=
      hp.coprime_iff_not_dvd.mp (hc j).symm
    exact _root_.AbcTwoNinths.PolyCap.rankSplit t hp ho hr hH hW hrW hrR hpR S hSr hS haway e he hprim hn hh hl hd

end

end AbcTwoNinths.PolyCap
