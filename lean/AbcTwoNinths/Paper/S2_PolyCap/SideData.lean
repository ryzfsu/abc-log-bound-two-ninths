/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Side Data

For a prime dividing the least-radical side, select the other two entries and record that the prime
divides neither of them. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.SideData`
* `AbcTwoNinths.PolyCap.selectedSideData`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section


/-- The side data. This is used in the proof of Proposition 2.1 of the paper. -/
structure SideData (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) where
  n : ℕ
  d : ℕ
  neg : Bool
  hn : n ≠ 0
  hd : d ≠ 0
  avoidN : ¬ p ∣ n
  avoidD : ¬ p ∣ d
  dunit : (d : ZMod p) ≠ 0
  residue : (n : ZMod p) = if neg then -(d : ZMod p) else d
  source : _root_.AbcTwoNinths.Statement.selectedSource t = if neg then -((n : ℚ) / d) else (n : ℚ) / d

/--
A prime dividing the first member of a coprime pair cannot divide the second.
-/
theorem primeNotDvdCoprimeOfDvd {p a b : ℕ} (hp : p.Prime) (h : a.Coprime b)
    (ha : p ∣ a) : ¬ p ∣ b := by
  intro hb
  exact hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd ha hb)

/-- The selected side data. This is used in the proof of Proposition 2.1 of the paper. -/
def selectedSideData (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) : _root_.AbcTwoNinths.PolyCap.SideData t p := by
  have hmem := Nat.mem_primeFactors.mp hp
  have hdiv := hmem.2.1
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hac : t.a.Coprime t.c := by
    rw [← t.add, Nat.add_comm t.a t.b, Nat.coprime_add_self_right]
    exact t.coprime
  have hbc : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact t.coprime.symm
  have hadd : (t.a : ZMod p) + t.b = t.c := by
    rw [← Nat.cast_add, t.add]
  cases h : _root_.AbcTwoNinths.Statement.minRadicalSide t <;> simp only [h, _root_.AbcTwoNinths.Statement.sideValue] at hdiv
  · have hb := primeNotDvdCoprimeOfDvd hmem.1 t.coprime hdiv
    have ha := (ZMod.natCast_eq_zero_iff t.a p).mpr hdiv
    refine ⟨t.c,t.b,false,hc.ne',t.bpos.ne',primeNotDvdCoprimeOfDvd hmem.1 hac hdiv,hb,
      fun he => hb ((ZMod.natCast_eq_zero_iff ..).mp he), ?_, ?_⟩
    · simpa [ha] using hadd.symm
    · simp [_root_.AbcTwoNinths.Statement.selectedSource, h]
  · have ha := primeNotDvdCoprimeOfDvd hmem.1 t.coprime.symm hdiv
    have hb := (ZMod.natCast_eq_zero_iff t.b p).mpr hdiv
    refine ⟨t.c,t.a,false,hc.ne',t.apos.ne',primeNotDvdCoprimeOfDvd hmem.1 hbc hdiv,ha,
      fun he => ha ((ZMod.natCast_eq_zero_iff ..).mp he), ?_, ?_⟩
    · simpa [hb] using hadd.symm
    · simp [_root_.AbcTwoNinths.Statement.selectedSource, h]
  · have hb := primeNotDvdCoprimeOfDvd hmem.1 hbc.symm hdiv
    have hz := (ZMod.natCast_eq_zero_iff t.c p).mpr hdiv
    refine ⟨t.a,t.b,true,t.apos.ne',t.bpos.ne',primeNotDvdCoprimeOfDvd hmem.1 hac.symm hdiv,hb,
      fun he => hb ((ZMod.natCast_eq_zero_iff ..).mp he), ?_, ?_⟩
    · exact eq_neg_of_add_eq_zero_left (hadd.trans hz)
    · simp [_root_.AbcTwoNinths.Statement.selectedSource, h, neg_div]

end

end AbcTwoNinths.PolyCap
