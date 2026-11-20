/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ExponentResidue
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationMonomialRatio

/-!
# Factorization Residues

The module shows that depth forces a factorization ratio to reduce to one and yields a kernel monomial. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.kernelMonomialOfDepth`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open scoped BigOperators

/--
The factorization difference of two nonzero congruent integers belongs to the residue kernel on a support containing their prime factors.
-/
theorem residueFactorizationRatio {p x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (S : Finset ℕ) (hS : x.primeFactors ∪ y.primeFactors ⊆ S)
    (hq : ∀ q : S, Nat.Coprime q.val p) (hxy : (x : ZMod p) = (y : ZMod p)) :
    (fun q : S => (x.factorization q.val : ℤ) - y.factorization q.val)
      ∈ (_root_.AbcTwoNinths.Basic.residue (fun q : S => q.val) hq).ker := by
  classical
  let u := fun q : S => ZMod.unitOfCoprime q.val (hq q)
  have hprod (n : ℕ) (hn : n ≠ 0) (hs : n.primeFactors ⊆ S) :
      (((∏ q : S, u q ^ n.factorization q.val) : (ZMod p)ˣ) : ZMod p) = (n : ZMod p) := by
    push_cast
    simp only [u, ZMod.coe_unitOfCoprime]
    rw [Finset.prod_coe_sort S (fun q : ℕ => (q : ZMod p) ^ n.factorization q)]
    have hnat : (∏ q ∈ S, q ^ n.factorization q) = n := by
      exact_mod_cast _root_.AbcTwoNinths.PolyCap.expandFactorization n hn S hs
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun m : ℕ => (m : ZMod p)) hnat
  have he :
      (∏ q : S, u q ^ x.factorization q.val) =
        (∏ q : S, u q ^ y.factorization q.val) := by
    apply Units.ext
    rw [hprod x hx (fun q hq => hS (Finset.mem_union_left _ hq)),
      hprod y hy (fun q hq => hS (Finset.mem_union_right _ hq)), hxy]
  change (∏ q : S, u q ^ ((x.factorization q.val : ℤ) - y.factorization q.val)) = 1
  simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    he, mul_inv_cancel]

/--
Positive depth of a quotient minus one gives equal numerator and denominator residues when the denominator is a unit modulo the prime.
-/
theorem castEqOfDepth {p x y : ℕ} [Fact p.Prime] (hy : y ≠ 0)
    (hpy : ¬ p ∣ y) (hd : 0 < padicValRat p ((x : ℚ) / y - 1)) :
    (x : ZMod p) = (y : ZMod p) := by
  let d : ℤ := (x : ℤ) - y
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hrew : (x : ℚ) / y - 1 = (d : ℚ) / y := by
    push_cast [d]
    field_simp
  have hdn : d ≠ 0 := by
    intro h
    simp [hrew, h] at hd
  rw [hrew, padicValRat.div (by exact_mod_cast hdn) hyq,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpy, Int.natCast_zero, sub_zero,
    padicValRat.of_int] at hd
  have hdiv : (p : ℤ) ∣ d := by
    by_contra hn
    rw [padicValInt.eq_zero_of_not_dvd hn] at hd
    omega
  have hz := (CharP.intCast_eq_zero_iff (ZMod p) p d).mpr hdiv
  push_cast [d] at hz
  exact sub_eq_zero.mp hz

/--
A quotient of positive depth at one has a residue-kernel exponent vector of logarithmic length at most the sum of the numerator and denominator logarithms. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem kernelMonomialOfDepth {p x y : ℕ} [Fact p.Prime] (hx : x ≠ 0)
    (hy : y ≠ 0) (hpy : ¬ p ∣ y) (hd : 0 < padicValRat p ((x : ℚ) / y - 1))
    (S : Finset ℕ) (hS : x.primeFactors ∪ y.primeFactors ⊆ S)
    (hq : ∀ q : S, Nat.Coprime q.val p) (hpos : ∀ q ∈ S, 1 ≤ q) :
    ∃ e : ℕ → ℤ, (fun q : S => e q.val) ∈ (_root_.AbcTwoNinths.Basic.residue (fun q : S => q.val) hq).ker ∧
      (∏ q ∈ S, (q : ℚ) ^ e q) = (x : ℚ) / y ∧
      (∑ q ∈ S, |(e q : ℝ)| * Real.log q) ≤ Real.log x + Real.log y := by
  refine ⟨fun q => (x.factorization q : ℤ) - y.factorization q,
    _root_.AbcTwoNinths.PolyCap.residueFactorizationRatio hx hy S hS hq (_root_.AbcTwoNinths.PolyCap.castEqOfDepth hy hpy hd),
    _root_.AbcTwoNinths.PolyCap.factorizationRatio hx hy S hS hpos, ?_⟩
  simpa only [Int.cast_sub, Int.cast_natCast] using _root_.AbcTwoNinths.PolyCap.factorizationRatioLength hx hy S hS hpos

end

end AbcTwoNinths.PolyCap
