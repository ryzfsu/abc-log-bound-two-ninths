/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedMonomialCoordinates
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeMonomial
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueParts

/-!
# Composite Principal Units

The module transports injective monomial evaluation to composite principal units and rewrites contact as numerator divisibility. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositePrincipalOfKernel`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/-- Distinct prime bases coprime to the modulus give an injective monomial character. -/
theorem compositeMonomialInjective {I : Type*} [Fintype I] {B : ℕ}
    (q : I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (hi : Function.Injective q) :
    Function.Injective (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc) := by
  intro x y h
  apply _root_.AbcTwoNinths.ExteriorE2.injective q hp hi
  apply Units.ext
  rw [← _root_.AbcTwoNinths.ExteriorE2.compositeMonomialRational q hp hc, ← _root_.AbcTwoNinths.ExteriorE2.compositeMonomialRational q hp hc, h]

/--
Divisibility of the contact numerator of an oriented difference of exponent vectors identifies the two powers modulo the given modulus power.
-/
theorem compositeOrientedContact {I : Type*} [Fintype I] {B n c d : ℕ}
    (q : I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (u z V : I → ℤ) (hV : V = (c : ℤ) • u - (d : ℤ) • z)
    (hd : (B : ℤ) ^ n ∣ ((_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd V)).val - 1).val.num) :
    (Units.map (Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B n)).toMonoidHom
      (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd u))) ^ c =
    (Units.map (Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B n)).toMonoidHom
      (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd z))) ^ d := by
  let f := (Units.map (Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B n)).toMonoidHom).comp
    (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc)
  have h : f (Multiplicative.ofAdd V) = 1 := by
    apply Units.ext
    exact (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff _ 1).2 hd
  rw [hV] at h
  change f (Multiplicative.ofAdd u ^ (c : ℤ) / Multiplicative.ofAdd z ^ (d : ℤ)) = 1 at h
  simpa only [map_div, map_zpow, zpow_natCast, div_eq_one, map_pow, f,
    MonoidHom.comp_apply] using h

/--
Divisibility of the difference of the positive and negative monomial parts implies divisibility of the reduced numerator of the monomial minus one.
-/
theorem compositePartsNumerator {I : Type*} [Fintype I] {B n : ℕ}
    (q : I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (e : I → ℤ)
    (hd : (B : ℤ)^n ∣ (↑(∏ i, q i ^ (e i).toNat) : ℤ) -
      (↑(∏ i, q i ^ (-e i).toNat) : ℤ)) :
    (B : ℤ)^n ∣ ((_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd e)).val - 1).val.num := by
  classical
  let f : I → (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ := fun i => _root_.AbcTwoNinths.ExteriorE2.compositePrimeUnit (hp i) (hc i)
  let P := ∏ i, f i ^ (e i).toNat
  let D := ∏ i, f i ^ (-e i).toNat
  have he : _root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd e) = P / D := by
    change (∏ i, f i ^ e i) = _
    dsimp only [P, D]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have h : e i = ((e i).toNat : ℤ) - ((-e i).toNat : ℤ) := by omega
    conv_lhs => rw [h, zpow_sub]
    simp only [zpow_natCast, div_eq_mul_inv]
  have hPD : P.val - D.val =
      ((↑(∏ i, q i ^ (e i).toNat) : ℤ) -
        (↑(∏ i, q i ^ (-e i).toNat) : ℤ) : ℤ) := by
    simp [P, D, f, _root_.AbcTwoNinths.ExteriorE2.compositePrimeUnit, Units.val_pow_eq_pow_val]
  have hcast : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)^n ∣ P.val - D.val := by
    rw [hPD]
    rcases hd with ⟨k, hk⟩
    exact ⟨(k : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B), by rw [hk]; norm_cast⟩
  apply _root_.AbcTwoNinths.ExteriorE2.compositeNumOfDvd
  have hh : (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd e)).val - 1 =
      (P.val - D.val) * D.inv := by
    rw [he, div_eq_mul_inv, Units.val_mul, sub_mul]
    simp
  rw [hh]
  exact dvd_mul_of_dvd_left hcast _

/--
Divisibility of the difference of monomial parts for the oriented vector passes to the numerator of the difference of powers.
-/
theorem compositeContactNumerator {I : Type*} [Fintype I] {B n c d : ℕ}
    (q : I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (u z V : I → ℤ) (hV : V = (c : ℤ) • u - (d : ℤ) • z)
    (hd : (B : ℤ)^n ∣ (↑(∏ i, q i ^ (V i).toNat) : ℤ) -
      (↑(∏ i, q i ^ (-V i).toNat) : ℤ)) :
    let U := (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd u)).val
    let Z := (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd z)).val
    (B : ℤ)^n ∣ (U^c - Z^d).val.num :=
  (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff _ _).1 (by
    simpa using congrArg Units.val
      (_root_.AbcTwoNinths.ExteriorE2.compositeOrientedContact q hp hc u z V hV (_root_.AbcTwoNinths.ExteriorE2.compositePartsNumerator q hp hc V hd)))

/--
An exponent vector in the reduction kernel gives a monomial congruent to one modulo the modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositePrincipalOfKernel {I : Type*} [Fintype I] {B : ℕ}
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (e : Unit ⊕ I → ℤ) (he : e ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction B q hc).ker) :
    Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1)
      (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd e)).val = 1 := by
  have hh := (_root_.AbcTwoNinths.ExteriorE2.kernelIffParts B q hc e).1 he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (↑(∏ i, q i ^ (-e i).toNat) : ℤ) (↑(∏ i, q i ^ (e i).toNat) : ℤ) B).1
    (by push_cast; exact hh.symm)
  have hh' := _root_.AbcTwoNinths.ExteriorE2.compositePartsNumerator (n := 1) q hp hc e (by simpa using hd)
  simpa using (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff (E := 1) _ 1).2 hh'

end

end AbcTwoNinths.ExteriorE2
