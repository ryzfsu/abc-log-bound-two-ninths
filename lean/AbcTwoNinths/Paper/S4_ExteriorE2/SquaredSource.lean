/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Squared Source

The module bounds the depth and height of the squared coprime source pair. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.sourcePairCoprime`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
Select the ordered pair of complementary coordinates for the chosen side. This is used in the proof of Proposition 4.1 of the paper.
-/
def sourcePair (t : _root_.AbcTwoNinths.Basic.Triple) : _root_.AbcTwoNinths.Statement.Side → ℕ × ℕ
  | .a => (t.c, t.b)
  | .b => (t.c, t.a)
  | .c => (t.b, t.a)

/--
A modulus power dividing the chosen side divides the natural difference of the squared source coordinates.
-/
theorem sourceSqDepth (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) {M L : ℕ}
    (h : M ^ L ∣ _root_.AbcTwoNinths.Statement.sideValue t s) :
    M ^ L ∣ (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2 - (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2 := by
  apply h.trans
  cases s <;> simp only [_root_.AbcTwoNinths.Statement.sideValue, _root_.AbcTwoNinths.ExteriorE2.sourcePair]
  · rw [← t.add, add_sq]
    refine ⟨t.a + 2 * t.b, ?_⟩
    rw [Nat.add_sub_cancel]
    ring
  · rw [← t.add, add_comm t.a t.b, add_sq]
    refine ⟨t.b + 2 * t.a, ?_⟩
    rw [Nat.add_sub_cancel]
    ring
  · rw [← t.add]
    by_cases hab : t.a ≤ t.b
    · refine ⟨t.b - t.a, ?_⟩
      zify [hab, Nat.pow_le_pow_left hab 2]
      ring
    · rw [Nat.sub_eq_zero_of_le (Nat.pow_le_pow_left (by omega) 2)]
      exact dvd_zero _

/--
For an ordered triple with b at least two, twice the logarithm of the first source coordinate lies between H and 2H.
-/
theorem sourceSqHeight (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side)
    (hab : t.a ≤ t.b) (hb : 2 ≤ t.b) :
    t.logHeight ≤ 2 * Real.log ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 : ℝ) ∧
      2 * Real.log ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 : ℝ) ≤ 2 * t.logHeight := by
  have hc : 0 < t.c := by rw [← t.add]; omega
  have hbc : t.b ≤ t.c := by rw [← t.add]; omega
  have hsq : t.c ≤ t.b ^ 2 := by rw [← t.add]; nlinarith
  have hpos := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t.c) : (1 : ℝ) ≤ t.c)
  cases s <;> simp only [_root_.AbcTwoNinths.ExteriorE2.sourcePair, _root_.AbcTwoNinths.Basic.Triple.logHeight]
  · exact ⟨by linarith, le_rfl⟩
  · exact ⟨by linarith, le_rfl⟩
  · constructor
    · have h := Real.log_le_log (by exact_mod_cast hc : (0 : ℝ) < t.c)
          (by exact_mod_cast hsq : (t.c : ℝ) ≤ (t.b : ℝ) ^ 2)
      simpa [Real.log_pow] using h
    · have h := Real.log_le_log (by exact_mod_cast t.bpos : (0 : ℝ) < t.b)
          (by exact_mod_cast hbc : (t.b : ℝ) ≤ t.c)
      linarith

/--
The source coordinates are coprime, and their product is coprime to the chosen side. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem sourcePairCoprime (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) :
    (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1.Coprime (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ∧
      ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 * (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2).Coprime (_root_.AbcTwoNinths.Statement.sideValue t s) := by
  have hac : t.a.Coprime t.c := by
    rw [← t.add, add_comm t.a t.b, Nat.coprime_add_self_right]
    exact t.coprime
  have hbc : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact t.coprime.symm
  cases s <;> simp only [_root_.AbcTwoNinths.ExteriorE2.sourcePair, _root_.AbcTwoNinths.Statement.sideValue]
  · exact ⟨hbc.symm, hac.symm.mul_left t.coprime.symm⟩
  · exact ⟨hac.symm, hbc.symm.mul_left t.coprime⟩
  · exact ⟨t.coprime.symm, hbc.mul_left hac⟩

end

end AbcTwoNinths.ExteriorE2
