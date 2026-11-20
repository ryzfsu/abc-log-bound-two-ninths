/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.RankTwoHeightInequality
public import AbcTwoNinths.Paper.S2_PolyCap.PolynomialHeightBound
public import AbcTwoNinths.Paper.S2_PolyCap.RankOneKernelHeight

/-!
# Rank Decomposition

The module divides the source prime support into the rank cases needed by the polynomial bound. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.rankSplit`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

/-- A primitive exponent vector in the residue kernel with the stated height and depth bounds yields
either `log c ≤ 192 * rad(abc)³` or a nonnegative `s ≤ min (2 * W) (3 * W / log W)` satisfying
`Z - 2 * s * log Z ≤ 9 + 2 * log W + W + s * (24 + 3 * log W)`, where `W = log(rad(abc))`
and `Z = 1 + log(20 * log c)`. -/
theorem rankSplit (t : _root_.AbcTwoNinths.Basic.Triple) {p r : ℕ}
    (hp : p.Prime) (ho : 2 < p) (hr : 1 ≤ r) (hH : 2 < t.logHeight)
    (hW : 1 < t.logRadical) (hrW : (r : ℝ) ≤ 2 * t.logRadical) (hrR : r ≤ t.radical) (hpR : p ∣ t.radical)
    (S : Finset ℕ) (hSr : S.card ≤ r) (hS : S ⊆ t.radical.primeFactors)
    (haway : ∀ j : S, ¬ p ∣ j.val) (e : S → ℤ)
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue Subtype.val (_root_.AbcTwoNinths.Basic.awayCoprime hp Subtype.val haway)).ker)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn (_root_.AbcTwoNinths.Basic.residue Subtype.val (_root_.AbcTwoNinths.Basic.awayCoprime hp Subtype.val haway)).ker e)
    (hne : _root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e ≠ 1)
    (hh : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e) ≤ 4 * t.logHeight)
    (hlt : t.logHeight / (4 * (r : ℝ)) < _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e))
    (hdepth : t.logHeight / (4 * (r : ℝ)) ≤
      (padicValRat p (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e - 1) : ℝ) * log (p : ℝ)) :
    t.logHeight ≤ 192 * (t.radical : ℝ) ^ (3 : ℕ) ∨
      ∃ s : ℝ, 1 < t.logRadical ∧ 0 ≤ s ∧ s ≤ 2 * t.logRadical ∧ s ≤ 3 * t.logRadical / log t.logRadical ∧
        let Z := 1 + log (20 * t.logHeight)
        Z - (2 * s) * log Z ≤ 9 + 2 * log t.logRadical + t.logRadical + s * (24 + 3 * log t.logRadical) := by
  classical
  by_cases hcard : 2 ≤ S.card
  · exact Or.inr (_root_.AbcTwoNinths.PolyCap.masterInequalityOfRankGeTwo t hp ho hr hH hW hrW hpR
      S hcard hSr hS haway e he hprim hne hh hlt hdepth)
  have hneS : S.card ≠ 0 := by
    intro h0
    have hzero : Fintype.card S = 0 := by simpa using h0
    let : IsEmpty S := Fintype.card_eq_zero_iff.mp hzero
    exact hne (by simp [_root_.AbcTwoNinths.PolyCap.prodMonomial])
  have hs : Fintype.card S = 1 := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨huniq⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hs
  let : Unique S := huniq
  let : Fact p.Prime := ⟨hp⟩
  let j : S := default
  have hj := hS j.property
  have hqPrime := Nat.prime_of_mem_primeFactors hj
  have hqR := Nat.dvd_of_mem_primeFactors hj
  have hcp : p.Coprime j.val := hp.coprime_iff_not_dvd.mpr (haway j)
  have hprod : p * j.val ∣ t.radical := hcp.mul_dvd_of_dvd_of_dvd hpR hqR
  have hRpos : 0 < t.radical := Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hcap := _root_.AbcTwoNinths.PolyCap.singletonHeight Subtype.val (_root_.AbcTwoNinths.Basic.awayCoprime hp Subtype.val haway)
    (fun k : S => (Nat.prime_of_mem_primeFactors (hS k.property)).one_lt)
    he hprim (r := (r : ℝ)) (R := (t.radical : ℝ)) (by exact_mod_cast hr)
    (by exact_mod_cast hrR) (by exact_mod_cast Nat.le_of_dvd hRpos hprod) hlt
  exact Or.inl (hcap.le.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)))

end

end AbcTwoNinths.PolyCap
