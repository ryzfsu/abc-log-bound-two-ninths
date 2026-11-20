/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Residue Quotient Ring

The module represents rationals coprime to the composite modulus in a subring and relates divisibility to their numerators. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeDvdOfNum`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
The subring of rationals whose reduced denominators are coprime to the given modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
def SubringCoprime (B : ℕ) : Subring ℚ where
  carrier := {q | q.den.Coprime B}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (Nat.Coprime.mul_left ha hb).coprime_dvd_left (Rat.add_den_dvd a b)
  mul_mem' := fun {a b} ha hb =>
    (Nat.Coprime.mul_left ha hb).coprime_dvd_left (Rat.mul_den_dvd a b)
  neg_mem' := by
    intro a ha
    change a.den.Coprime B at ha
    simpa using ha

/--
Divisibility of the reduced numerator by a modulus power implies divisibility in the coprime-denominator ring. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeDvdOfNum {B E : ℕ} (x : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (h : (B : ℤ) ^ E ∣ x.val.num) : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ E ∣ x := by
  obtain ⟨z, hz⟩ := h
  have hden : (Rat.divInt z (x.val.den : ℤ)).den ∣ x.val.den := by
    exact_mod_cast Rat.den_dvd z (x.val.den : ℤ)
  have hx : x.val.den.Coprime B := x.property
  refine ⟨⟨Rat.divInt z (x.val.den : ℤ), hx.coprime_dvd_left hden⟩, ?_⟩
  apply Subtype.ext
  change x.val = (B : ℚ) ^ E * Rat.divInt z (x.val.den : ℤ)
  calc
    x.val = (x.val.num : ℚ) / (x.val.den : ℚ) := x.val.num_div_den.symm
    _ = _ := by rw [hz]; push_cast; rw [Rat.divInt_eq_div, mul_div_assoc]; norm_cast

/--
Divisibility in the coprime-denominator ring by a modulus power implies divisibility of the reduced numerator.
-/
theorem compositeNumOfDvd {B E : ℕ} (x : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (h : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ E ∣ x) : (B : ℤ) ^ E ∣ x.val.num := by
  obtain ⟨y, hy⟩ := h
  have e : x.val = (B : ℚ) ^ E * y.val := congrArg Subtype.val hy
  have eqQ : (x.val.num : ℚ) * y.val.den =
      (B : ℚ) ^ E * y.val.num * x.val.den := by
    have hx : (x.val.den : ℚ) ≠ 0 := by exact_mod_cast x.val.den_nz
    have hy' : (y.val.den : ℚ) ≠ 0 := by exact_mod_cast y.val.den_nz
    rw [← x.val.num_div_den, ← y.val.num_div_den] at e
    field_simp at e
    linear_combination e
  have eqZ : x.val.num * (y.val.den : ℤ) =
      (B : ℤ) ^ E * y.val.num * (x.val.den : ℤ) := by exact_mod_cast eqQ
  have eqN := congrArg Int.natAbs eqZ
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at eqN
  have hc : (B ^ E).Coprime y.val.den :=
    (show y.val.den.Coprime B from y.property).symm.pow_left E
  have hd : B ^ E ∣ x.val.num.natAbs * y.val.den := by
    rw [eqN, mul_assoc]
    exact dvd_mul_right _ _
  have hnum : B ^ E ∣ x.val.num.natAbs := hc.dvd_of_dvd_mul_right hd
  rw [← Int.natAbs_dvd_natAbs]
  simpa using hnum

end

end AbcTwoNinths.ExteriorE2
