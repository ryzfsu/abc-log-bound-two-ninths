/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.SignedPrincipalUnitEstimate
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Signed Principal Unit Bracket

The module orients signed exponent pairs and derives a valuation bracket for two positive powers of principal units. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.signedBound`
* `AbcTwoNinths.Diamond.signedLiftIndependent`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

section

open Real

variable {p : ℕ} [Fact p.Prime]

/-- The orient. This is used in Section 6 of the paper. -/
private def orient (u : ℚ) (rev : Bool) : ℚ := if rev then u⁻¹ else u

private theorem orientPrincipal {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) (b : Bool) :
    _root_.AbcTwoNinths.Basic.Principal p (orient u b) := by cases b; exact hu; exact _root_.AbcTwoNinths.Basic.principalInv hu

private theorem orientHeight {u : ℚ} (hu : u ≠ 0) (b : Bool) :
    _root_.AbcTwoNinths.Basic.rationalHeight (orient u b) = _root_.AbcTwoNinths.Basic.rationalHeight u := by cases b; rfl; exact _root_.AbcTwoNinths.Basic.heightInv hu

private theorem orientIndependent {u v : ℚ} (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent u v) (a b : Bool) :
    _root_.AbcTwoNinths.Basic.RatMulIndependent (orient u a) (orient v b) := by
  intro i j h
  cases a <;> cases b <;> simp only [orient, Bool.false_eq_true, ↓reduceIte, inv_zpow, ← zpow_neg] at h
  · exact hi _ _ h
  · simpa using hi _ _ h
  · simpa using hi _ _ h
  · simpa using hi _ _ h

private theorem orientPow (u : ℚ) (c : ℤ) : orient u (decide (c < 0)) ^ c.natAbs = u ^ c := by
  cases c <;> simp [orient, zpow_negSucc, inv_pow]

private theorem orientDiv (u v : ℚ) (c d : ℤ) :
    orient u (decide (c < 0)) ^ c.natAbs / orient v (decide (0 < d)) ^ d.natAbs =
      u ^ c * v ^ d := by
  rw [orientPow]
  cases d with
  | ofNat d =>
    change u ^ c / orient v (decide (0 < (d : ℤ))) ^ d = u ^ c * v ^ (d : ℤ)
    rw [zpow_natCast]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · simp [orient, hd, div_eq_mul_inv, inv_pow]
  | negSucc d => simp [orient, div_eq_mul_inv, zpow_negSucc]

/--
The normalized two-logarithm estimate bounds the valuation of a product of nonzero signed powers of independent rational principal units minus one. This is used in Section 6 of the paper.
-/
theorem signedBound (hp : 5 ≤ p) {u v z : ℚ} {c d : ℤ} {B₁ B₂ : ℝ}
    (hu : _root_.AbcTwoNinths.Basic.Principal p u) (hv : _root_.AbcTwoNinths.Basic.Principal p v) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent u v) (hc : c ≠ 0) (hd : d ≠ 0) (hz : z = u ^ c * v ^ d)
    (h₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight u) (log (p : ℝ)) ≤ B₁)
    (h₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight v) (log (p : ℝ)) ≤ B₂) :
    let ell := log (p : ℝ)
    let b := (c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁
    (padicValRat p (z - 1) : ℝ) * ell ^ 2 ≤
      588 * B₁ * B₂ * (max 4 (log (exp 2 * ell * (b / 2)) / ell)) ^ 2 := by
  have h := _root_.AbcTwoNinths.Basic.bound (B₁ := B₁) (B₂ := B₂) hp
    (orientPrincipal hu (decide (c < 0))) (orientPrincipal hv (decide (0 < d)))
    (orientIndependent hi _ _) (Int.natAbs_pos.mpr hc) (Int.natAbs_pos.mpr hd)
    (by rw [orientHeight hu0]; exact h₁) (by rw [orientHeight hv0]; exact h₂)
  dsimp only at h ⊢
  rwa [orientDiv, ← hz] at h

section Lift

variable [Fact (2 < p)] {ι : Type*} [Fintype ι]
variable (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (avoid : ∀ i, p ≠ q i)

/-- The integral prime. This is used in Section 6 of the paper. -/
private noncomputable def integralPrime (i : ι) : ℤ_[p]ˣ :=
  (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => avoid i ((Nat.prime_dvd_prime_iff_eq Fact.out (hq i)).mp h))))).unit

omit [Fact (2 < p)] [Fintype ι] in
private theorem integralPrimeVal (i : ι) :
    (integralPrime q hq avoid i : ℤ_[p]) = q i := IsUnit.unit_spec _

/--
The signed character of a residue-kernel vector is a rational principal unit at the selected prime.
-/
theorem signedLiftPrincipal (w : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)) :
    _root_.AbcTwoNinths.Basic.Principal p (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) w : ℚ) := by
  classical
  let R := _root_.AbcTwoNinths.ExteriorE2.residue q hq avoid
  let U := _root_.AbcTwoNinths.ExteriorE2.eval (integralPrime q hq avoid) w.val
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
    have hu : PadicInt.toZMod (U : ℤ_[p]) = (R w.val : ZMod p) := congrArg Units.val hred
    change PadicInt.toZMod (e * (U : ℤ_[p])) = 1
    rw [map_mul, hu]
    rcases (_root_.AbcTwoNinths.ExteriorE2.memKer R w.val).mp w.property with hr | hr
    · simp [e, hr]
    · simp [e, hr, _root_.AbcTwoNinths.ExteriorE2.minusNeOne]
  have hcast : (((U : ℤ_[p]) : ℚ_[p])) = ((_root_.AbcTwoNinths.ExteriorE2.monomial q hq w.val : ℚˣ) : ℚ) := by
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
    by_cases he : R w.val = 1 <;> simp [z, e, _root_.AbcTwoNinths.ExteriorE2.gammaStar, _root_.AbcTwoNinths.ExteriorE2.signUnit, he, hcast]
  have hk : z - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hres, map_one, sub_self]
  have hn : ‖z - 1‖ < 1 := PadicInt.not_isUnit_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hk)
  simpa [_root_.AbcTwoNinths.Basic.Principal, PadicInt.norm_def, hz] using hn

local notation "γ" => _root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)

/--
Two residue-kernel vectors with injective integer coordinate combinations have multiplicatively independent signed characters on distinct support primes. This is used in Section 6 of the paper.
-/
theorem signedLiftIndependent (hqinj : Function.Injective q)
    (w₁ w₂ : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid))
    (hcoords : Function.Injective
      (fun a : ℤ × ℤ => fun i => a.1 * w₁.val.toAdd i + a.2 * w₂.val.toAdd i)) :
    _root_.AbcTwoNinths.Basic.RatMulIndependent (γ w₁ : ℚ) (γ w₂ : ℚ) := by
  intro a b h
  have hzero : (a, b) = ((0, 0) : ℤ × ℤ) := hcoords (by
    funext i
    let : Fact (q i).Prime := ⟨hq i⟩
    have hval := congrArg (padicValRat (q i)) h
    rw [padicValRat.mul (zpow_ne_zero _ (γ w₁).ne_zero) (zpow_ne_zero _ (γ w₂).ne_zero),
      padicValRat.zpow, padicValRat.zpow, padicValRat.one,
      _root_.AbcTwoNinths.ExteriorE2.signedCoordinate q hq hqinj avoid w₁,
      _root_.AbcTwoNinths.ExteriorE2.signedCoordinate q hq hqinj avoid w₂] at hval
    simpa [mul_comm] using hval)
  exact Prod.mk.inj hzero

/--
For a residue-kernel vector expressed in two independent coordinates with nonzero coefficients, the normalized two-logarithm bracket bounds the valuation of its signed character minus one.
-/
theorem liftedBound (hp : 5 ≤ p) (hqinj : Function.Injective q)
    (w₁ w₂ v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid))
    (hcoords : Function.Injective
      (fun a : ℤ × ℤ => fun i => a.1 * w₁.val.toAdd i + a.2 * w₂.val.toAdd i))
    {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (hv : v = w₁ ^ c * w₂ ^ d) {B₁ B₂ : ℝ}
    (h₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight (γ w₁ : ℚ)) (log (p : ℝ)) ≤ B₁)
    (h₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight (γ w₂ : ℚ)) (log (p : ℝ)) ≤ B₂) :
    let ell := log (p : ℝ)
    let b := (c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁
    (padicValRat p ((γ v : ℚ) - 1) : ℝ) * ell ^ 2 ≤
      588 * B₁ * B₂ * (max 4 (log (exp 2 * ell * (b / 2)) / ell)) ^ 2 := by
  have hz : (γ v : ℚ) = (γ w₁ : ℚ) ^ c * (γ w₂ : ℚ) ^ d := by
    rw [hv, map_mul, map_zpow, map_zpow, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  exact _root_.AbcTwoNinths.Diamond.signedBound hp (_root_.AbcTwoNinths.Diamond.signedLiftPrincipal q hq avoid w₁) (_root_.AbcTwoNinths.Diamond.signedLiftPrincipal q hq avoid w₂)
    (γ w₁).ne_zero (γ w₂).ne_zero (_root_.AbcTwoNinths.Diamond.signedLiftIndependent q hq avoid hqinj w₁ w₂ hcoords)
    hc hd hz h₁ h₂

end Lift

section LiftConsumer
variable [Fact (2 < p)] {ι : Type*} [Fintype ι]

end LiftConsumer

end

end AbcTwoNinths.Diamond
