/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import Mathlib.Tactic

/-!
# Least Radical Side

The least side radical is at most the cube root of the triple radical, as is the product of any two
distinct primes on that side. The real-contact bound also gives a lower bound for the sum of the
prime-power logarithms on that side. This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.minSideLeScale`
* `AbcTwoNinths.Statement.minSidePair`
* `AbcTwoNinths.Statement.minSideFull`
-/

@[expose] public section


namespace AbcTwoNinths.Statement

open scoped BigOperators


section

private theorem sidePos (t : _root_.AbcTwoNinths.Basic.Triple) (i : _root_.AbcTwoNinths.Statement.Side) : 0 < _root_.AbcTwoNinths.Statement.sideValue t i := by
  cases i
  · exact t.apos
  · exact t.bpos
  · change 0 < t.c
    rw [← t.add]
    exact Nat.add_pos_left t.apos _

/-- For an ordered triple satisfying the real contact bound, the valuation mass of its
least-radical side is at least `(1 - κ) * t.logHeight`. -/
theorem minSideFull (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b) {κ : ℝ}
    (he : _root_.AbcTwoNinths.Statement.RealContactBound κ t) :
    (1 - κ) * t.logHeight ≤
      ∑ q ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
        (padicValNat q (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log q := by
  let u := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
  have hau : t.a ≤ u := by
    cases h : _root_.AbcTwoNinths.Statement.minRadicalSide t
    · simp [u, h, _root_.AbcTwoNinths.Statement.sideValue]
    · simpa [u, h, _root_.AbcTwoNinths.Statement.sideValue] using hord
    · have hs := t.add
      simpa [u, h, _root_.AbcTwoNinths.Statement.sideValue] using (show t.a ≤ t.c by omega)
  have hapos : 0 < (t.a : ℝ) := by exact_mod_cast t.apos
  have hcpos : 0 < (t.c : ℝ) := by exact_mod_cast sidePos t .c
  unfold _root_.AbcTwoNinths.Statement.RealContactBound at he
  rw [Real.log_div hcpos.ne' hapos.ne'] at he
  have hlog : Real.log (t.a : ℝ) ≤ Real.log (u : ℝ) :=
    Real.log_le_log hapos (by exact_mod_cast hau)
  have hm : (1 - κ) * t.logHeight ≤ Real.log (u : ℝ) := by
    change (1 - κ) * Real.log (t.c : ℝ) ≤ Real.log (u : ℝ)
    change Real.log (t.c : ℝ) - Real.log (t.a : ℝ) ≤ κ * Real.log (t.c : ℝ) at he
    linarith
  change (1 - κ) * t.logHeight ≤ ∑ q ∈ u.primeFactors, (padicValNat q u : ℝ) * Real.log q
  refine hm.trans_eq ?_
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ q ∈ u.primeFactors, (u.factorization q : ℝ) * Real.log q) = _
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.factorization_def u (Nat.prime_of_mem_primeFactors hq)]

private theorem radicalProduct (t : _root_.AbcTwoNinths.Basic.Triple) :
    t.radical = _root_.AbcTwoNinths.Statement.sideRadical t .a * _root_.AbcTwoNinths.Statement.sideRadical t .b * _root_.AbcTwoNinths.Statement.sideRadical t .c := by
  have ha : t.a ≠ 0 := (sidePos t .a).ne'
  have hb : t.b ≠ 0 := (sidePos t .b).ne'
  have hc : t.c ≠ 0 := (sidePos t .c).ne'
  have hab : t.a.Coprime t.b := t.coprime
  have hac : t.a.Coprime t.c := by
    rw [← t.add, Nat.add_comm t.a t.b, Nat.coprime_add_self_right]
    exact hab
  have hbc : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact hab.symm
  have habc : (t.a * t.b).Coprime t.c := hac.mul_left hbc
  have hdis : Disjoint (t.a * t.b).primeFactors t.c.primeFactors := habc.disjoint_primeFactors
  unfold _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Statement.sideRadical _root_.AbcTwoNinths.Statement.sideValue _root_.AbcTwoNinths.Basic.radical
  rw [Nat.primeFactors_mul (mul_ne_zero ha hb) hc, Finset.prod_union hdis,
    Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

/-- The radical of the least-radical side is at most the exponential of the radical scale. -/
theorem minSideLeScale (t : _root_.AbcTwoNinths.Basic.Triple) :
    (_root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) : ℝ) ≤ Real.exp t.thirdLogRadical := by
  let M := _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
  have hMa := _root_.AbcTwoNinths.Statement.minRadicalSideSpec t .a
  have hMb := _root_.AbcTwoNinths.Statement.minRadicalSideSpec t .b
  have hMc := _root_.AbcTwoNinths.Statement.minRadicalSideSpec t .c
  have hcube : M ^ 3 ≤ t.radical := by
    rw [radicalProduct, pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul hMa hMb) hMc
  have hmpos : 0 < M := Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hpos : 0 < (M : ℝ) := by exact_mod_cast hmpos
  have hlog := Real.log_le_log (pow_pos hpos 3) (show (M : ℝ)^3 ≤ t.radical by exact_mod_cast hcube)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  change (M : ℝ) ≤ Real.exp (Real.log (t.radical : ℝ) / 3)
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by linarith)

/--
The product of two distinct primes on the least-radical side is bounded by the exponential of the radical scale. This is used in the proof of Theorem 1.1 of the paper.
-/
theorem minSidePair (t : _root_.AbcTwoNinths.Basic.Triple) :
    ∀ p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
      ∀ q ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors, p ≠ q →
        (p : ℝ) * q ≤ Real.exp t.thirdLogRadical := by
  intro p hp q hq hpq
  let u := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
  have hs : ({p, q} : Finset ℕ) ⊆ u.primeFactors :=
    Finset.insert_subset_iff.mpr ⟨hp, Finset.singleton_subset_iff.mpr hq⟩
  have hd : (∏ s ∈ ({p, q} : Finset ℕ), s) ∣ _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) :=
    Finset.prod_dvd_prod_of_subset _ _ id hs
  simp [hpq] at hd
  have hm : 0 < _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  exact (show (p : ℝ) * q ≤ (_root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) : ℝ) by
    exact_mod_cast Nat.le_of_dvd hm hd).trans (_root_.AbcTwoNinths.Statement.minSideLeScale t)

end

end AbcTwoNinths.Statement
