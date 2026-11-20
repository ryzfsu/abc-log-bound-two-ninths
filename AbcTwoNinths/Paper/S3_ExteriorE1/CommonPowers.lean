/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Basic.TripleAndHeight
public import AbcTwoNinths.Basic.IndependentMonomialFactorization

/-!
# Common Powers

The module proves the real-contact estimate for large common powers using the gap between consecutive bases. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.e1OfLargeCommonPower`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- For natural bases `B < C`, the power `C^(n+1)` exceeds or equals `B^(n+1) + C^n`. -/
theorem powerGap {B C : ℕ} (hBC : B < C) (n : ℕ) :
    C ^ n + B ^ (n + 1) ≤ C ^ (n + 1) := by
  have hpow : B ^ n ≤ C ^ n := Nat.pow_le_pow_left hBC.le _
  calc
    C ^ n + B ^ (n + 1) ≤ C ^ n + C ^ n * B := by
      rw [pow_succ]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right B hpow) _
    _ = C ^ n * (B + 1) := by ring
    _ ≤ C ^ (n + 1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ hBC

/--
Powers of distinct increasing bases satisfy the real-contact bound when their common exponent times the margin is at least one. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem e1OfLargeCommonPower (t : _root_.AbcTwoNinths.Basic.Triple) (κ : ℝ) (B C n : ℕ)
    (hBC : B < C) (hb : t.b = B ^ (n + 1)) (hc : t.c = C ^ (n + 1))
    (hκ : 1 ≤ (n + 1 : ℝ) * κ) : _root_.AbcTwoNinths.Statement.RealContactBound κ t := by
  have ha := t.apos
  have hadd := t.add
  have hgap := _root_.AbcTwoNinths.ExteriorE1.powerGap hBC n
  rw [← hb, ← hc] at hgap
  have hA : C ^ n ≤ t.a := by omega
  have hC : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hAr : (0 : ℝ) < t.a := by exact_mod_cast ha
  have hcr : (0 : ℝ) < t.c := by
    rw [hc, Nat.cast_pow]
    exact pow_pos hC _
  have hLa := Real.log_le_log (pow_pos hC n)
    (show (C : ℝ) ^ n ≤ t.a by exact_mod_cast hA)
  rw [Real.log_pow] at hLa
  have hH : t.logHeight = (n + 1 : ℝ) * Real.log (C : ℝ) := by
    rw [_root_.AbcTwoNinths.Basic.Triple.logHeight, hc, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  have hnonneg : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hκL := mul_le_mul_of_nonneg_right hκ hnonneg
  unfold _root_.AbcTwoNinths.Statement.RealContactBound
  rw [Real.log_div hcr.ne' hAr.ne', ← _root_.AbcTwoNinths.Basic.Triple.logHeight, hH]
  nlinarith only [hLa, hκL]

end

end AbcTwoNinths.ExteriorE1
