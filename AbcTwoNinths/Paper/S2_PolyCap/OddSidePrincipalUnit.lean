/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SameSideValuationDepth
public import AbcTwoNinths.Paper.S2_PolyCap.OddContact

/-!
# Odd Side Principal Unit

The module constructs a principal-unit ratio for the source attached to an odd prime. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddPrincipalSource`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- An ordered triple of logarithmic height greater than two admits a positive principal unit `x / y`
at an odd prime divisor `p` of `b` or `c`, with `x, y ≤ c²` dividing `(abc)²`, exact depth `v_p(M)`
on the chosen side `M`, and weighted depth at least the logarithmic height divided by twice the
number of prime divisors of `M`. -/
theorem oddPrincipalSource (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b)
    (hH : 2 < t.logHeight) :
    ∃ M p x y : ℕ, (M = t.b ∨ M = t.c) ∧ p ∈ M.primeFactors ∧ p.Prime ∧
      2 < p ∧ 0 < x ∧ 0 < y ∧ x ≠ y ∧ ¬ p ∣ x ∧ ¬ p ∣ y ∧
      x ≤ t.c ^ 2 ∧ y ≤ t.c ^ 2 ∧
      x ∣ (t.a * t.b * t.c)^2 ∧ y ∣ (t.a * t.b * t.c)^2 ∧
      _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p ((x : ℚ) / y) ∧
      padicValRat p ((x : ℚ) / y - 1) = (M.factorization p : ℤ) ∧
      t.logHeight ≤ 2 * (M.primeFactors.card : ℝ) *
        ((padicValRat p ((x : ℚ) / y - 1) : ℝ) * Real.log p) := by
  have hstrict : t.a < t.b := by
    by_contra! h
    have hh := hab.antisymm h
    have hg := t.coprime.gcd_eq_one
    rw [← hh, Nat.gcd_self] at hg
    have ha := t.add
    have hc : t.c = 2 := by omega
    change 2 < Real.log (t.c : ℝ) at hH
    rw [hc] at hH
    norm_num at hH
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  obtain ⟨M, hM, _, p, hpM, hp, hp2, hbound⟩ := _root_.AbcTwoNinths.PolyCap.oddSideContact t hab hH
  let _ : Fact p.Prime := ⟨hp⟩
  have hd := Nat.dvd_of_mem_primeFactors hpM
  obtain ⟨x, y, hx, hy, hxy, hpx, hpy, hxc, hyc, hxN, hyN, hv⟩ :=
    _root_.AbcTwoNinths.PolyCap.sameSideDepth t hstrict hp hd (_root_.AbcTwoNinths.PolyCap.sameSidePrimeSelectionSameSideOfSelected t hab hM hp hp2 hd)
  have hz : 0 < (x : ℚ) / y := by positivity
  refine ⟨M, p, x, y, hM, hpM, hp, hp2, hx, hy, hxy, hpx, hpy, hxc, hyc, hxN, hyN,
    ⟨hz, hz.ne', ?_, Or.inr ?_⟩, hv, ?_⟩
  · rw [padicValRat.div (by positivity) (by positivity), padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpx,
      padicValNat.eq_zero_of_not_dvd hpy]
    rfl
  · rw [hv]
    exact_mod_cast hp.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hpM).2.2 hd
  · rw [hv, Int.cast_natCast]
    exact hbound

end

end AbcTwoNinths.PolyCap
