/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SameSidePrimeSelection
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Same Side Valuation Depth

The module bounds the selected prime depth on the side where it occurs in the source triple. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.sameSideDepth`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- The same-side identity yields distinct positive integers `x, y` coprime to `p`, bounded by `c²`
and dividing `(abc)²`, with `v_p(x / y - 1) = v_p(M)` on the chosen side `M`. -/
theorem sameSideDepth (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a < t.b) {M p : ℕ}
    (hp : p.Prime) (hd : p ∣ M) (hs : _root_.AbcTwoNinths.PolyCap.SameSideSameSidePrimeSelection t M p) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧
      ¬ p ∣ x ∧ ¬ p ∣ y ∧
      x ≤ t.c ^ 2 ∧ y ≤ t.c ^ 2 ∧
      x ∣ (t.a * t.b * t.c)^2 ∧ y ∣ (t.a * t.b * t.c)^2 ∧
      padicValRat p ((x : ℚ) / y - 1) = (M.factorization p : ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have ha := t.apos
  have hb := t.bpos
  have hadd := t.add
  have hc : 0 < t.c := by omega
  have haN : t.a ∣ t.a * t.b * t.c := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hbN : t.b ∣ t.a * t.b * t.c := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hcN : t.c ∣ t.a * t.b * t.c := dvd_mul_left _ _
  have hA : (t.a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hB : (t.b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hC : (t.c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hv (n : ℕ) : padicValRat p (n : ℚ) = (n.factorization p : ℤ) := by
    rw [padicValRat.of_nat, Nat.factorization_def _ hp]
  have hz (n : ℕ) (h : ¬ p ∣ n) : padicValRat p (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
    rfl
  rcases hs with ⟨rfl, hpa, hid⟩ | ⟨rfl, hpa, hid, hdiff⟩
  · have hpc : ¬ p ∣ t.c := by
      intro h
      apply hpa
      have hh := Nat.dvd_sub h hd
      rwa [show t.c - t.b = t.a by omega] at hh
    have hc2 : t.c ≤ t.c ^ 2 := by nlinarith
    refine ⟨t.c, t.a, hc, ha, by omega, hpc, hpa, hc2, le_trans (by omega) hc2,
      hcN.trans (dvd_pow_self _ (by decide)), haN.trans (dvd_pow_self _ (by decide)), ?_⟩
    rw [hid, padicValRat.div hB hA, hv, hz _ hpa, sub_zero]
  · have hpb : ¬ p ∣ t.b := by
      intro h
      apply hpa
      have hh := Nat.dvd_sub hd h
      rwa [show t.c - t.b = t.a by omega] at hh
    have hD : ((t.b - t.a : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show t.b - t.a ≠ 0 by omega)
    refine ⟨t.b ^ 2, t.a ^ 2, by positivity, by positivity, ?_, ?_, ?_,
      Nat.pow_le_pow_left (by omega) _, Nat.pow_le_pow_left (by omega) _,
      pow_dvd_pow_of_dvd hbN _, pow_dvd_pow_of_dvd haN _, ?_⟩
    · exact ne_of_gt (Nat.pow_lt_pow_left hab (by decide))
    · simpa [pow_two, hp.dvd_mul] using hpb
    · simpa [pow_two, hp.dvd_mul] using hpa
    · rw [Nat.cast_pow, Nat.cast_pow, ← div_pow, hid,
        ← Nat.cast_sub hab.le, padicValRat.div (mul_ne_zero hD hC) (pow_ne_zero _ hA),
        padicValRat.mul hD hC, hz _ hdiff, hv, zero_add, padicValRat.pow,
        hz _ hpa, mul_zero, sub_zero]

end

end AbcTwoNinths.PolyCap
