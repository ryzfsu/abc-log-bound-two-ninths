/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Logarithmic Height

The multiplicative height of a reduced rational is the maximum of the absolute numerator and the
denominator. The selected source has height at most the largest entry of the triple, so expressing
it as a power of a rational of height at least two bounds the exponent by the triple's logarithmic
height divided by `log 2` . This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.mulHeight`
* `AbcTwoNinths.Statement.mulHeightSelectedSourceLe`
* `AbcTwoNinths.Statement.exponentLeHeight`
-/

@[expose] public section


namespace AbcTwoNinths.Statement

section



/-- The multiplicative height of a rational number is the maximum of its absolute
numerator and its positive denominator in lowest terms. -/
def mulHeight (u : ℚ) : ℕ := max u.num.natAbs u.den

/-- The multiplicative height of a natural power is the same power of the base height. -/
theorem mulHeightPow (u : ℚ) (g : ℕ) : _root_.AbcTwoNinths.Statement.mulHeight (u ^ g) = _root_.AbcTwoNinths.Statement.mulHeight u ^ g := by
  unfold _root_.AbcTwoNinths.Statement.mulHeight
  rw [Rat.num_pow, Rat.den_pow, Int.natAbs_pow]
  rcases le_total u.num.natAbs u.den with h | h
  · rw [max_eq_right h, max_eq_right (Nat.pow_le_pow_left h g)]
  · rw [max_eq_left h, max_eq_left (Nat.pow_le_pow_left h g)]

private theorem mulHeightDiv {a b : ℕ} (hb : 0 < b) (hc : a.Coprime b) :
    _root_.AbcTwoNinths.Statement.mulHeight ((a : ℚ) / b) = max a b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : Nat.Coprime (a : ℤ).natAbs (b : ℤ).natAbs := by simpa using hc
  have hn := Rat.num_div_eq_of_coprime hb' hc'
  have hd := Rat.den_div_eq_of_coprime hb' hc'
  push_cast at hn
  have hd' : ((a : ℚ) / b).den = b := Int.ofNat.inj hd
  simp [_root_.AbcTwoNinths.Statement.mulHeight, hn, hd']

/-- The multiplicative height of the quotient associated with the least-radical side is
at most the largest entry `t.c`. -/
theorem mulHeightSelectedSourceLe (t : _root_.AbcTwoNinths.Basic.Triple) :
    _root_.AbcTwoNinths.Statement.mulHeight (_root_.AbcTwoNinths.Statement.selectedSource t) ≤ t.c := by
  have ha : t.a ≤ t.c := by rw [← t.add]; omega
  have hb : t.b ≤ t.c := by rw [← t.add]; omega
  have hca : t.c.Coprime t.a := by
    rw [← t.add, Nat.add_comm, Nat.coprime_add_self_left]
    exact t.coprime.symm
  have hcb : t.c.Coprime t.b := by
    rw [← t.add, Nat.coprime_add_self_left]
    exact t.coprime
  unfold _root_.AbcTwoNinths.Statement.selectedSource
  cases _root_.AbcTwoNinths.Statement.minRadicalSide t with
  | a => rw [mulHeightDiv t.bpos hcb, max_eq_left hb]
  | b => rw [mulHeightDiv t.apos hca, max_eq_left ha]
  | c =>
    rw [neg_div]
    have hs : ∀ z : ℚ, _root_.AbcTwoNinths.Statement.mulHeight (-z) = _root_.AbcTwoNinths.Statement.mulHeight z := by
      intro z
      simp [_root_.AbcTwoNinths.Statement.mulHeight]
    rw [hs, mulHeightDiv t.bpos t.coprime]
    exact max_le ha hb

private theorem twoLeMulHeight {u : ℚ} (hu : u ≠ 0) (h1 : u ≠ 1)
    (hn : u ≠ -1) : 2 ≤ _root_.AbcTwoNinths.Statement.mulHeight u := by
  by_contra! h
  have hd : u.den = 1 := by
    have := le_max_right u.num.natAbs u.den
    have := u.den_pos
    unfold _root_.AbcTwoNinths.Statement.mulHeight at h
    omega
  have hnum : u.num = 0 ∨ u.num = 1 ∨ u.num = -1 := by
    have := le_max_left u.num.natAbs u.den
    unfold _root_.AbcTwoNinths.Statement.mulHeight at h
    omega
  rcases hnum with he | he | he
  · exact hu (by simpa [Rat.num_divInt_den, he, hd] using (Rat.num_divInt_den u).symm)
  · exact h1 (by simpa [he, hd] using (Rat.num_divInt_den u).symm)
  · exact hn (by simpa [he, hd] using (Rat.num_divInt_den u).symm)

/-- A power representation of the selected quotient with base outside `0`, `1`, and `-1`
has exponent at most `t.logHeight / Real.log 2`. -/
theorem exponentLeHeight {t : _root_.AbcTwoNinths.Basic.Triple} {u : ℚ} {g : ℕ}
    (hu : u ≠ 0) (hu₁ : u ≠ 1) (hun : u ≠ -1)
    (hpow : _root_.AbcTwoNinths.Statement.selectedSource t = u ^ g) :
    (g : ℝ) ≤ t.logHeight / Real.log 2 := by
  have hb := _root_.AbcTwoNinths.Statement.mulHeightSelectedSourceLe t
  rw [hpow, _root_.AbcTwoNinths.Statement.mulHeightPow] at hb
  have htwo := (Nat.pow_le_pow_left (twoLeMulHeight hu hu₁ hun) g).trans hb
  have hc : (2 : ℝ) ^ g ≤ t.c := by exact_mod_cast htwo
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ g) hc
  rw [Real.log_pow] at he
  exact (le_div_iff₀ hlog).mpr he

end

end AbcTwoNinths.Statement
