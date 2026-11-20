/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts
public import AbcTwoNinths.Basic.ExponentResidue

/-!
# Valuation Residue Kernel

The module identifies the residue kernel with a local principal-unit condition and deduces a strict height bound. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.logLtRatHeightOfMemKer`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

private theorem gpDivIff {p P Q : ℕ} (hp : p.Prime)
    (hP : 0 < P) (hQ : 0 < Q) (haP : ¬ p ∣ P) (haQ : ¬ p ∣ Q) :
    _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p ((P : ℚ) / (Q : ℚ)) ↔ (P : ZMod p) = (Q : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hP' : 0 < (P : ℚ) := by exact_mod_cast hP
  have hQ' : 0 < (Q : ℚ) := by exact_mod_cast hQ
  have hz : 0 < (P : ℚ) / (Q : ℚ) := div_pos hP' hQ'
  have hvQ := padicValNat.eq_zero_of_not_dvd haQ
  have hv : padicValRat p ((P : ℚ) / (Q : ℚ)) = 0 := by
    rw [padicValRat.div hP'.ne' hQ'.ne', padicValRat.of_nat, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd haP, hvQ]
    simp
  have hg : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p ((P : ℚ) / (Q : ℚ)) ↔
      ((P : ℚ) / (Q : ℚ) = 1 ∨ 0 < padicValRat p ((P : ℚ) / (Q : ℚ) - 1)) := by
    exact ⟨fun h => h.2.2.2, fun h => ⟨hz, ne_of_gt hz, hv, h⟩⟩
  rw [hg]
  rw [← sub_eq_zero (a := (P : ZMod p)) (b := (Q : ZMod p))]
  have hcast : (P : ZMod p) - (Q : ZMod p) = (((P : ℤ) - (Q : ℤ) : ℤ) : ZMod p) := by push_cast; rfl
  rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  by_cases h : P = Q
  · subst Q
    simp [div_self hP'.ne']
  · have he : (P : ℤ) - (Q : ℤ) ≠ 0 := by omega
    have hne : (P : ℚ) / (Q : ℚ) ≠ 1 := by
      intro hh
      have hh' := (div_eq_iff hQ'.ne').mp hh
      rw [one_mul] at hh'
      exact h (by exact_mod_cast hh')
    have hsub : (P : ℚ) / (Q : ℚ) - 1 =
        (((P : ℤ) - (Q : ℤ) : ℤ) : ℚ) / (Q : ℚ) := by
      push_cast
      rw [sub_div, div_self hQ'.ne']
    simp only [hne, false_or]
    rw [hsub, padicValRat.div (by exact_mod_cast he) hQ'.ne', padicValRat.of_int,
      padicValRat.of_nat, hvQ, Nat.cast_zero, sub_zero]
    have hd := padicValInt_dvd_iff (p := p) 1 ((P : ℤ) - (Q : ℤ))
    rw [pow_one] at hd
    rw [hd, or_iff_right he]
    omega

/-- For distinct prime bases away from `p`, an exponent vector lies in the residue kernel exactly
when its rational monomial is a positive principal unit at `p`. -/
theorem memResidueKerIffGp {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : p.Prime) (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (haway : ∀ j, ¬ p ∣ q j) (e : ι → ℤ) :
    e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker ↔ _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) := by
  let ac := _root_.AbcTwoNinths.Basic.awayCoprime hp q haway
  let u (j : ι) := ZMod.unitOfCoprime (q j) (ac j)
  let up (b : ι → ℤ) := ∏ j, (u j) ^ (b j).toNat
  have hc (b : ι → ℤ) : (up b : ZMod p) = (_root_.AbcTwoNinths.PolyCap.posPartNat q b : ZMod p) := by
    simp [up, u, _root_.AbcTwoNinths.PolyCap.posPartNat, ZMod.coe_unitOfCoprime]
  have hnp (b : ι → ℤ) : ¬ p ∣ _root_.AbcTwoNinths.PolyCap.posPartNat q b := by
    intro hd
    have hd' : (p : ℤ) ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q b : ℤ) := by exact_mod_cast hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd'
    have hzero : (_root_.AbcTwoNinths.PolyCap.posPartNat q b : ZMod p) = 0 := by simpa using hz
    let : Fact p.Prime := ⟨hp⟩
    exact (Units.ne_zero (up b)) ((hc b).trans hzero)
  have hu : (∏ j, u j ^ e j) = up e / up (-e) := by
    simp only [up, ← Finset.prod_div_distrib, Pi.neg_apply]
    apply Finset.prod_congr rfl
    intro j _
    have he : e j = ((e j).toNat : ℤ) - ((-e j).toNat : ℤ) := by omega
    conv_lhs => rw [he, zpow_sub]
    simp only [zpow_natCast, div_eq_mul_inv]
  obtain ⟨hP, hQ, _, hm, _, _⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime q hq hinj e
  rw [hm, gpDivIff hp hP hQ (hnp e) (hnp (-e))]
  change (∏ j, u j ^ e j) = 1 ↔ _
  rw [hu, div_eq_one]
  change up e = up (-e) ↔ (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ZMod p) = (_root_.AbcTwoNinths.PolyCap.posPartNat q (-e) : ZMod p)
  constructor
  · intro h
    rw [← hc, ← hc]
    exact congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h
  · intro h
    apply Units.ext
    rw [hc, hc]
    exact h

/--
A nonzero vector in the residue kernel on distinct prime bases away from `p` gives a rational
monomial of logarithmic height strictly greater than `log p`.
-/
theorem logLtRatHeightOfMemKer {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : p.Prime) (q : ι → ℕ) (hq : ∀ j, (q j).Prime)
    (hinj : Function.Injective q) (haway : ∀ j, ¬ p ∣ q j)
    {e : ι → ℤ} (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker) (hne : e ≠ 0) :
    log (p : ℝ) < _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) := by
  refine _root_.AbcTwoNinths.PolyCap.logLtRatHeightOfGp hp ((_root_.AbcTwoNinths.PolyCap.memResidueKerIffGp hp q hq hinj haway e).mp he) ?_
  intro hx
  exact hne (funext ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff q hq hinj e).mp hx))

end

end AbcTwoNinths.PolyCap
