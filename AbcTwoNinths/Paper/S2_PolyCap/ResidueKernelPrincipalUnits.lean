/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationResidues
public import AbcTwoNinths.Paper.S2_PolyCap.OddSidePrincipalUnit
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationMonomialPowers

/-!
# Residue Kernel Principal Units

The module proves that a rational quotient lies in the principal units when its residue is one. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.monomialPrincipalOfKernel`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The quotient of two positive integers prime to p with equal residues is a principal unit at p.
-/
theorem ratioPrincipalOfCastEq {p x y : ℕ} [Fact p.Prime]
    (hx : 0 < x) (hy : 0 < y) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y)
    (hxy : (x : ZMod p) = (y : ZMod p)) : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p ((x : ℚ) / y) := by
  have hz : 0 < (x : ℚ) / y := by positivity
  refine ⟨hz, hz.ne', ?_, ?_⟩
  · rw [padicValRat.div (by positivity) (by positivity), padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpx,
      padicValNat.eq_zero_of_not_dvd hpy]
    rfl
  by_cases he : x = y
  · exact Or.inl (by subst x; exact div_self (by positivity))
  right
  let d : ℤ := (x : ℤ) - y
  have hdn : d ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
  have hdZ : (d : ZMod p) = 0 := by simp [d, hxy]
  have hdiv := (CharP.intCast_eq_zero_iff (ZMod p) p d).mp hdZ
  have hda : p ∣ d.natAbs := Int.natCast_dvd.mp hdiv
  have hval := (dvd_iff_padicValNat_ne_zero (Int.natAbs_ne_zero.mpr hdn)).mp hda
  have hrew : (x : ℚ) / y - 1 = (d : ℚ) / y := by
    push_cast [d]
    field_simp
  rw [hrew, padicValRat.div (by exact_mod_cast hdn) (by positivity),
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpy, Int.natCast_zero,
    sub_zero, padicValRat.of_int]
  change (0 : ℤ) < (padicValNat p d.natAbs : ℤ)
  exact_mod_cast Nat.pos_of_ne_zero hval

/--
The monomial of a residue-kernel exponent on positive bases prime to p is a principal unit at p. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem monomialPrincipalOfKernel {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (q : ι → ℕ) (hq : ∀ i, Nat.Coprime (q i) p) (hqpos : ∀ i, 0 < q i)
    (e : ι → ℤ) (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q hq).ker) :
    _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p (∏ i, (q i : ℚ) ^ e i) := by
  let u := fun i => ZMod.unitOfCoprime (q i) (hq i)
  let x := ∏ i, q i ^ (e i).toNat
  let y := ∏ i, q i ^ (-e i).toNat
  have hu (i : ι) : u i ^ e i = u i ^ (e i).toNat / u i ^ (-e i).toNat := by
    rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← zpow_sub]
    congr 1
    omega
  change (∏ i, u i ^ e i) = 1 at he
  simp only [hu, Finset.prod_div_distrib, div_eq_one] at he
  have hxZ : (x : ZMod p) = (y : ZMod p) := by
    have hc := congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) he
    push_cast at hc
    simpa only [u,
      ZMod.coe_unitOfCoprime, x, y, Nat.cast_prod, Nat.cast_pow] using hc
  have haway (n : ι → ℕ) : ¬ p ∣ ∏ i, q i ^ n i := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      rw [Nat.cast_pow, ← ZMod.coe_unitOfCoprime (q i) (hq i)]
      exact pow_ne_zero _ (Units.ne_zero _)
  rw [_root_.AbcTwoNinths.PolyCap.monomialSplit q e hqpos]
  exact _root_.AbcTwoNinths.PolyCap.ratioPrincipalOfCastEq
    (Finset.prod_pos fun i _ => pow_pos (hqpos i) _)
    (Finset.prod_pos fun i _ => pow_pos (hqpos i) _)
    (haway _) (haway _) hxZ

end

end AbcTwoNinths.PolyCap
