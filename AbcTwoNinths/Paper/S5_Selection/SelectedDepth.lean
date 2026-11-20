/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Selected Depth

The module proves divisibility of the selected source difference by the appropriate power of its prime. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.selectedSourceDepth`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section



private theorem noCommon {p a b : ℕ} (hp : p.Prime) (hab : a.Coprime b)
    (ha : p ∣ a) : ¬ p ∣ b := by
  intro hb
  have hg := Nat.dvd_gcd ha hb
  change a.gcd b = 1 at hab
  exact hp.not_dvd_one (hab ▸ hg)

private theorem depthDiv {p a b : ℕ} [Fact p.Prime] (ha : 0 < a)
    (hb : 0 < b) (hpb : ¬ p ∣ b) :
    padicValRat p ((a : ℚ) / (b : ℚ)) = (padicValNat p a : ℤ) := by
  rw [padicValRat.div (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'),
    ← padicValRat_of_nat, ← padicValRat_of_nat,
    padicValNat.eq_zero_of_not_dvd hpb, Nat.cast_zero, sub_zero]

/--
The same selected source has unit valuation and exact selected-side depth. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem selectedSourceDepth (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) :
    padicValRat p (_root_.AbcTwoNinths.Statement.selectedSource t) = 0 ∧
      padicValRat p (_root_.AbcTwoNinths.Statement.selectedSource t - 1) =
        (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hab := t.coprime
  have hac : t.a.Coprime t.c := by
    rw [← t.add, Nat.add_comm t.a t.b, Nat.coprime_add_self_right]
    exact hab
  have hbc : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact hab.symm
  have hA : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
  have hB : (t.b : ℚ) ≠ 0 := by exact_mod_cast t.bpos.ne'
  have hadd : (t.a : ℚ) + (t.b : ℚ) = (t.c : ℚ) := by exact_mod_cast t.add
  unfold _root_.AbcTwoNinths.Statement.selectedSource
  cases h : _root_.AbcTwoNinths.Statement.minRadicalSide t <;> simp only [h, _root_.AbcTwoNinths.Statement.sideValue] at hd ⊢
  · have hpb := noCommon hp hab hd
    have hpc := noCommon hp hac hd
    constructor
    · rw [depthDiv hc t.bpos hpb, padicValNat.eq_zero_of_not_dvd hpc, Nat.cast_zero]
    · rw [show (t.c : ℚ) / t.b - 1 = (t.a : ℚ) / t.b by field_simp; linarith]
      exact depthDiv t.apos t.bpos hpb
  · have hpa := noCommon hp hab.symm hd
    have hpc := noCommon hp hbc hd
    constructor
    · rw [depthDiv hc t.apos hpa, padicValNat.eq_zero_of_not_dvd hpc, Nat.cast_zero]
    · rw [show (t.c : ℚ) / t.a - 1 = (t.b : ℚ) / t.a by field_simp; linarith]
      exact depthDiv t.bpos t.apos hpa
  · have hpa := noCommon hp hac.symm hd
    have hpb := noCommon hp hbc.symm hd
    constructor
    · rw [neg_div, padicValRat.neg, depthDiv t.apos t.bpos hpb,
        padicValNat.eq_zero_of_not_dvd hpa, Nat.cast_zero]
    · rw [show -(t.a : ℚ) / t.b - 1 = -((t.c : ℚ) / t.b) by field_simp; linarith,
        padicValRat.neg]
      exact depthDiv hc t.bpos hpb

/-- At a prime in the minimum-radical side's support, the selected source has valuation zero
and its difference from one has the valuation of that side. -/
theorem selectedSourceDepthOfMem (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) :
    padicValRat p (_root_.AbcTwoNinths.Statement.selectedSource t) = 0 ∧
      padicValRat p (_root_.AbcTwoNinths.Statement.selectedSource t - 1) =
        (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) := by
  have h := Nat.mem_primeFactors.mp hp
  exact _root_.AbcTwoNinths.Selection.selectedSourceDepth t h.1 h.2.1

end

end AbcTwoNinths.Selection
