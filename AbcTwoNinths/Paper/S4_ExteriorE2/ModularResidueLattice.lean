/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.BigOperators

/-!
# Modular Residue Lattice

The module defines signed prime monomial evaluation and relates its residue reduction to an exponent lattice. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.modularResidueLatticeInjective`
-/

@[expose] public section
namespace AbcTwoNinths.ExteriorE2

section

/-- The exponents. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev Exponents (ι : Type*) := Multiplicative (ι → ℤ)

variable {ι : Type*} [Fintype ι]

/-- The eval. This is used in the proof of Proposition 4.1 of the paper. -/
def eval {G : Type*} [CommGroup G] (base : ι → G) : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* G where
  toFun w := ∏ i, base i ^ w.toAdd i
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

section

/-- The rat unit. This is used in the proof of Proposition 4.1 of the paper. -/
def ratUnit (base : ι → ℕ) (hp : ∀ i, (base i).Prime) (i : ι) : ℚˣ :=
  Units.mk0 (base i : ℚ) (Nat.cast_ne_zero.mpr (hp i).ne_zero)

/-- The monomial. This is used in the proof of Proposition 4.1 of the paper. -/
def monomial (base : ι → ℕ) (hp : ∀ i, (base i).Prime) : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* ℚˣ :=
  _root_.AbcTwoNinths.ExteriorE2.eval (_root_.AbcTwoNinths.ExteriorE2.ratUnit base hp)

/-- The valuation. This is used in the proof of Proposition 4.1 of the paper. -/
def valuation (p : ℕ) [Fact p.Prime] : ℚˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (padicValRat p x)
  map_one' := by change Multiplicative.ofAdd (padicValRat p 1) = _; simp
  map_mul' x y := congrArg Multiplicative.ofAdd (padicValRat.mul x.ne_zero y.ne_zero)

/--
For distinct prime bases, the valuation of a rational monomial at `base j` recovers its
exponent at `j` .
-/
theorem coordinate (base : ι → ℕ) (hp : ∀ i, (base i).Prime)
    (hi : Function.Injective base) (w : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) (j : ι) :
    padicValRat (base j) (_root_.AbcTwoNinths.ExteriorE2.monomial base hp w : ℚ) = w.toAdd j := by
  classical
  let : Fact (base j).Prime := ⟨hp j⟩
  have h := map_prod (_root_.AbcTwoNinths.ExteriorE2.valuation (base j))
    (fun i => _root_.AbcTwoNinths.ExteriorE2.ratUnit base hp i ^ w.toAdd i) Finset.univ
  change ((_root_.AbcTwoNinths.ExteriorE2.valuation (base j)) (∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit base hp i ^ w.toAdd i)).toAdd = _
  rw [h]
  change (∑ i, ((_root_.AbcTwoNinths.ExteriorE2.valuation (base j)) (_root_.AbcTwoNinths.ExteriorE2.ratUnit base hp i ^ w.toAdd i)).toAdd) = _
  trans ((_root_.AbcTwoNinths.ExteriorE2.valuation (base j)) (_root_.AbcTwoNinths.ExteriorE2.ratUnit base hp j ^ w.toAdd j)).toAdd
  · apply Finset.sum_eq_single j
    · intro i _ hij
      let : Fact (base i).Prime := ⟨hp i⟩
      change padicValRat (base j) (↑(_root_.AbcTwoNinths.ExteriorE2.ratUnit base hp i ^ w.toAdd i) : ℚ) = 0
      rw [Units.val_zpow_eq_zpow_val]
      simp [_root_.AbcTwoNinths.ExteriorE2.ratUnit, padicValNat_primes (fun he => hij (hi he.symm))]
    · simp
  · change padicValRat (base j) (↑(_root_.AbcTwoNinths.ExteriorE2.ratUnit base hp j ^ w.toAdd j) : ℚ) = _
    rw [Units.val_zpow_eq_zpow_val]
    simp [_root_.AbcTwoNinths.ExteriorE2.ratUnit, padicValNat_self]

/-- The rational monomial map with pairwise distinct prime bases is injective. -/
theorem injective (base : ι → ℕ) (hp : ∀ i, (base i).Prime)
    (hi : Function.Injective base) : Function.Injective (_root_.AbcTwoNinths.ExteriorE2.monomial base hp) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  funext j
  rw [← _root_.AbcTwoNinths.ExteriorE2.coordinate base hp hi a j, ← _root_.AbcTwoNinths.ExteriorE2.coordinate base hp hi b j, hab]

end

section

/-- The signs. This is used in the proof of Proposition 4.1 of the paper. -/
def signs (p : ℕ) : Subgroup (ZMod p)ˣ where
  carrier := {x | x = 1 ∨ x = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by rintro a (rfl | rfl) <;> simp

variable {p : ℕ} [Fact p.Prime]

/-- The residue unit. This is used in the proof of Proposition 4.1 of the paper. -/
def residueUnit (base : ι → ℕ) (hp : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (i : ι) : (ZMod p)ˣ :=
  Units.mk0 (base i : ZMod p) (by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => avoid i ((Nat.prime_dvd_prime_iff_eq Fact.out (hp i)).mp h))

/-- The residue. This is used in the proof of Proposition 4.1 of the paper. -/
def residue (base : ι → ℕ) (hp : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i) :=
  _root_.AbcTwoNinths.ExteriorE2.eval (_root_.AbcTwoNinths.ExteriorE2.residueUnit base hp avoid)

/-- The label. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev Label (p : ℕ) := (ZMod p)ˣ ⧸ _root_.AbcTwoNinths.ExteriorE2.signs p

/-- The reduction. This is used in the proof of Proposition 4.1 of the paper. -/
def reduction (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* _root_.AbcTwoNinths.ExteriorE2.Label p :=
  (QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p)).comp r

omit [Fintype ι] in
/--
An exponent vector lies in the reduction kernel modulo signs exactly when its residue is `1`
or `-1` .
-/
theorem memKer (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (x : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) :
    x ∈ (_root_.AbcTwoNinths.ExteriorE2.reduction r).ker ↔ r x = 1 ∨ r x = -1 :=
  QuotientGroup.eq_one_iff (r x)

end

section


variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

/-- The units `-1` and `1` are distinct modulo an odd prime. -/
theorem minusNeOne : (-1 : (ZMod p)ˣ) ≠ 1 :=
  fun he => ZMod.neg_one_ne_one (congrArg Units.val he)

/-- The kernel. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev Kernel (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) := (_root_.AbcTwoNinths.ExteriorE2.reduction r).ker

/-- The choose negative. This is used in the proof of Proposition 4.1 of the paper. -/
def chooseNegative (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) : Bool :=
  decide (r w.val ≠ 1)

/-- The sign unit. This is used in the proof of Proposition 4.1 of the paper. -/
def signUnit (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) : ℚˣ :=
  if r w.val = 1 then 1 else -1

omit [Fintype ι] in
/--
For a vector in the reduction kernel modulo signs, `chooseNegative` is the unique sign
choice that gives residue `1` .
-/
theorem principalIff (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) (neg : Bool) :
    (if neg then -r w.val else r w.val) = 1 ↔ neg = _root_.AbcTwoNinths.ExteriorE2.chooseNegative r w := by
  rcases (_root_.AbcTwoNinths.ExteriorE2.memKer r w.val).mp w.property with hw | hw <;> cases neg <;>
    simp [_root_.AbcTwoNinths.ExteriorE2.chooseNegative, hw, _root_.AbcTwoNinths.ExteriorE2.minusNeOne]

/-- The gamma star. This is used in the proof of Proposition 4.1 of the paper. -/
def gammaStar (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (m : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* ℚˣ) :
    _root_.AbcTwoNinths.ExteriorE2.Kernel r →* ℚˣ where
  toFun w := _root_.AbcTwoNinths.ExteriorE2.signUnit r w * m w.val
  map_one' := by simp [_root_.AbcTwoNinths.ExteriorE2.signUnit]
  map_mul' x y := by
    rcases (_root_.AbcTwoNinths.ExteriorE2.memKer r x.val).mp x.property with hx | hx <;>
      rcases (_root_.AbcTwoNinths.ExteriorE2.memKer r y.val).mp y.property with hy | hy <;>
      simp [_root_.AbcTwoNinths.ExteriorE2.signUnit, hx, hy, _root_.AbcTwoNinths.ExteriorE2.minusNeOne]

omit [Fintype ι] in
/--
The canonical sign correction gives residue `1` and expresses `gammaStar` as the rational
monomial with that sign.
-/
theorem signCharacterization (r : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (m : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* ℚˣ)
    (w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) :
    (if _root_.AbcTwoNinths.ExteriorE2.chooseNegative r w then -r w.val else r w.val) = 1 ∧
    _root_.AbcTwoNinths.ExteriorE2.gammaStar r m w = (if _root_.AbcTwoNinths.ExteriorE2.chooseNegative r w then -m w.val else m w.val) := by
  refine ⟨(_root_.AbcTwoNinths.ExteriorE2.principalIff r w _).mpr rfl, ?_⟩
  by_cases h : r w.val = 1 <;> simp [_root_.AbcTwoNinths.ExteriorE2.gammaStar, _root_.AbcTwoNinths.ExteriorE2.signUnit, _root_.AbcTwoNinths.ExteriorE2.chooseNegative, h]

/--
The valuation at each base prime recovers the corresponding exponent of a sign-corrected
rational monomial.
-/
theorem signedCoordinate (base : ι → ℕ) (hp : ∀ i, (base i).Prime)
    (hi : Function.Injective base) (avoid : ∀ i, p ≠ base i)
    (w : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue base hp avoid)) (i : ι) :
    padicValRat (base i) (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue base hp avoid)
      (_root_.AbcTwoNinths.ExteriorE2.monomial base hp) w : ℚ) = w.val.toAdd i := by
  classical
  change padicValRat _ (↑(_root_.AbcTwoNinths.ExteriorE2.signUnit _ w * _) : ℚ) = _
  unfold _root_.AbcTwoNinths.ExteriorE2.signUnit
  split <;> simp [_root_.AbcTwoNinths.ExteriorE2.coordinate base hp hi]

/--
The sign-corrected rational monomial map is injective on the residue kernel modulo signs for
distinct prime bases different from the modulus prime.
-/
theorem modularResidueLatticeInjective (base : ι → ℕ) (hp : ∀ i, (base i).Prime)
    (hi : Function.Injective base) (avoid : ∀ i, p ≠ base i) :
    Function.Injective (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue base hp avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial base hp)) := by
  intro a b he
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  rw [← _root_.AbcTwoNinths.ExteriorE2.signedCoordinate base hp hi avoid a i, ← _root_.AbcTwoNinths.ExteriorE2.signedCoordinate base hp hi avoid b i, he]

end

section

end

end

end AbcTwoNinths.ExteriorE2
