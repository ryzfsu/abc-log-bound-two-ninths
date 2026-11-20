/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import AbcTwoNinths.Basic.PrincipalUnitData

public import Mathlib
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Residue Lattice Contact

Lifts a signed residue-kernel monomial to a principal unit at the chosen prime. It supports
Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.signedLiftPrincipal`
-/

@[expose] public section
namespace AbcTwoNinths.ExteriorE2

section




variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {ι : Type*} [Fintype ι]
variable (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (avoid : ∀ i, p ≠ q i)

/-- The integral prime. This is used in the proof of Proposition 4.1 of the paper. -/
private noncomputable def integralPrime (i : ι) : ℤ_[p]ˣ :=
  (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => avoid i ((Nat.prime_dvd_prime_iff_eq Fact.out (hq i)).mp h))))).unit

omit [Fact (2 < p)] [Fintype ι] in
private theorem integralPrimeVal (i : ι) :
    (integralPrime q hq avoid i : ℤ_[p]) = q i := IsUnit.unit_spec _

/-- The integral monomial. This is used in the proof of Proposition 4.1 of the paper. -/
private noncomputable def integralMonomial : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* ℤ_[p]ˣ :=
  _root_.AbcTwoNinths.ExteriorE2.eval (integralPrime q hq avoid)

/--
The signed lift of an exponent vector in the residue kernel is a rational principal unit at the chosen odd prime. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem signedLiftPrincipal (w : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)) :
    _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)
      (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) w : ℚ) := by
  classical
  let R := _root_.AbcTwoNinths.ExteriorE2.residue q hq avoid
  let U := integralMonomial q hq avoid w.val
  let red : ℤ_[p]ˣ →* (ZMod p)ˣ := Units.map (PadicInt.toZMod (p := p)).toMonoidHom
  have hred : red U = R w.val := by
    change red (∏ i, integralPrime q hq avoid i ^ w.val.toAdd i) =
      ∏ i, _root_.AbcTwoNinths.ExteriorE2.residueUnit q hq avoid i ^ w.val.toAdd i
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow]
    congr 1
    apply Units.ext
    change PadicInt.toZMod (integralPrime q hq avoid i : ℤ_[p]) = (q i : ZMod p)
    rw [integralPrimeVal, map_natCast]
  let e : ℤ_[p] := if R w.val = 1 then 1 else -1
  let z : ℤ_[p] := e * U
  have hres : PadicInt.toZMod z = 1 := by
    have hu : PadicInt.toZMod (U : ℤ_[p]) = (R w.val : ZMod p) :=
      congrArg Units.val hred
    change PadicInt.toZMod (e * (U : ℤ_[p])) = 1
    rw [map_mul, hu]
    rcases (_root_.AbcTwoNinths.ExteriorE2.memKer R w.val).mp w.property with hr | hr
    · simp [e, hr]
    · simp [e, hr, _root_.AbcTwoNinths.ExteriorE2.minusNeOne]
  have hcast : (((U : ℤ_[p]) : ℚ_[p])) =
      ((_root_.AbcTwoNinths.ExteriorE2.monomial q hq w.val : ℚˣ) : ℚ) := by
    let l : ℤ_[p]ˣ →* ℚ_[p]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom
    let r : ℚˣ →* ℚ_[p]ˣ := Units.map (Rat.castHom ℚ_[p]).toMonoidHom
    change (l U : ℚ_[p]) = (r (_root_.AbcTwoNinths.ExteriorE2.monomial q hq w.val) : ℚ_[p])
    congr 1
    change l (∏ i, integralPrime q hq avoid i ^ w.val.toAdd i) =
      r (∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit q hq i ^ w.val.toAdd i)
    rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow, map_zpow]
    congr 1
    apply Units.ext
    change ((integralPrime q hq avoid i : ℤ_[p]) : ℚ_[p]) = (((q i : ℕ) : ℚ) : ℚ_[p])
    rw [integralPrimeVal]
    simp
  have hz : (z : ℚ_[p]) =
      ((_root_.AbcTwoNinths.ExteriorE2.gammaStar R (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) w : ℚ) : ℚ_[p]) := by
    by_cases he : R w.val = 1 <;>
      simp [z, e, _root_.AbcTwoNinths.ExteriorE2.gammaStar, _root_.AbcTwoNinths.ExteriorE2.signUnit, he, hcast]
  have hk : z - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hres, map_one, sub_self]
  have hn : ‖z - 1‖ < 1 :=
    PadicInt.not_isUnit_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hk)
  simpa [_root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData, PadicInt.norm_def, hz] using hn

end

end AbcTwoNinths.ExteriorE2
