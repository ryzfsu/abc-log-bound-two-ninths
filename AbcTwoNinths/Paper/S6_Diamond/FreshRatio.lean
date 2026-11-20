/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic

/-!
# Fresh Ratio

The module proves injectivity of bounded fresh-prime ratios from a modular cross-product equality. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.injOnRatio`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

section

/-- An ordered pair of distinct primes. This is used in Section 6 of the paper. -/
abbrev Pair := {v : ℕ × ℕ // v.1.Prime ∧ v.2.Prime ∧ v.1 ≠ v.2}

/--
The ratio of the two prime coordinates in the field of residues modulo the given prime. This is used in Section 6 of the paper.
-/
def ratio (p : ℕ) [Fact p.Prime] (v : _root_.AbcTwoNinths.Diamond.Pair) : ZMod p := (v.val.1 : ZMod p) / (v.val.2 : ZMod p)

/--
Every first coordinate times any second coordinate in the set is strictly below the modulus. This is used in Section 6 of the paper.
-/
def CrossBound (p : ℕ) (S : Set _root_.AbcTwoNinths.Diamond.Pair) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, v.val.1 * w.val.2 < p

-- At the last possible representative p - 1, reduction is still exact.

-- Beyond the bound, even reversed distinct prime pairs can collide.

-- If diagonal pairs were admitted, both ratios would be 1.

/--
A common upper bound for both coordinates gives the cross-product bound when its square is below the modulus.
-/
theorem crossBoundOfUpper {p : ℕ} {M : ℝ} {S : Set _root_.AbcTwoNinths.Diamond.Pair}
    (hM : M ^ 2 < (p : ℝ))
    (hu : ∀ v ∈ S, (v.val.1 : ℝ) ≤ M ∧ (v.val.2 : ℝ) ≤ M) : _root_.AbcTwoNinths.Diamond.CrossBound p S := by
  intro v hv w hw
  have hnonneg : 0 ≤ M := le_trans (Nat.cast_nonneg _) (hu v hv).1
  have hle := mul_le_mul (hu v hv).1 (hu w hw).2 (Nat.cast_nonneg _) hnonneg
  have hlt : (v.val.1 : ℝ) * w.val.2 < p := lt_of_le_of_lt hle (by simpa [pow_two] using hM)
  exact_mod_cast hlt

/-- The cross-product bound makes every denominator nonzero modulo the modulus. -/
theorem denominatorNeZero {p : ℕ} {S : Set _root_.AbcTwoNinths.Diamond.Pair} (h : _root_.AbcTwoNinths.Diamond.CrossBound p S)
    {v : _root_.AbcTwoNinths.Diamond.Pair} (hv : v ∈ S) : (v.val.2 : ZMod p) ≠ 0 := by
  have hlt : v.val.2 < p :=
    (Nat.le_mul_of_pos_left _ v.property.1.pos).trans_lt (h v hv v hv)
  intro hz
  have he := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at he
  exact v.property.2.1.ne_zero he

/-- Equality of the prime ratios gives equality of the two cross-products modulo the prime. -/
theorem crossEqMod {p : ℕ} [Fact p.Prime] {S : Set _root_.AbcTwoNinths.Diamond.Pair} (h : _root_.AbcTwoNinths.Diamond.CrossBound p S)
    {v w : _root_.AbcTwoNinths.Diamond.Pair} (hv : v ∈ S) (hw : w ∈ S) (he : _root_.AbcTwoNinths.Diamond.ratio p v = _root_.AbcTwoNinths.Diamond.ratio p w) :
    ((v.val.1 * w.val.2 : ℕ) : ZMod p) = ((w.val.1 * v.val.2 : ℕ) : ZMod p) := by
  simpa only [Nat.cast_mul] using
    (div_eq_div_iff (_root_.AbcTwoNinths.Diamond.denominatorNeZero h hv) (_root_.AbcTwoNinths.Diamond.denominatorNeZero h hw)).1 he

/-- Two natural numbers below the modulus agree if their residues agree. -/
theorem exactOfMod {p a b : ℕ} (ha : a < p) (hb : b < p)
    (he : (a : ZMod p) = (b : ZMod p)) : a = b := by
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val he

/--
Equality of the natural cross-products identifies both members of an ordered pair of distinct primes.
-/
theorem pairEqOfCrossEq {v w : _root_.AbcTwoNinths.Diamond.Pair} (he : v.val.1 * w.val.2 = w.val.1 * v.val.2) :
    v = w := by
  have hd : v.val.1 ∣ w.val.1 * v.val.2 := he ▸ dvd_mul_right _ _
  have hnum : v.val.1 = w.val.1 := by
    rcases v.property.1.dvd_mul.mp hd with hn | hden
    · exact (Nat.prime_dvd_prime_iff_eq v.property.1 w.property.1).mp hn
    · exact (v.property.2.2 ((Nat.prime_dvd_prime_iff_eq v.property.1 v.property.2.1).mp hden)).elim
  rw [← hnum] at he
  exact Subtype.ext (Prod.ext hnum (Nat.eq_of_mul_eq_mul_left v.property.1.pos he).symm)

/--
Under the cross-product bound, the modular ratio is injective on the given set of ordered pairs of distinct primes. This is used in Section 6 of the paper.
-/
theorem injOnRatio {p : ℕ} [Fact p.Prime] {S : Set _root_.AbcTwoNinths.Diamond.Pair} (h : _root_.AbcTwoNinths.Diamond.CrossBound p S) :
    Set.InjOn (_root_.AbcTwoNinths.Diamond.ratio p) S := by
  intro v hv w hw he
  exact _root_.AbcTwoNinths.Diamond.pairEqOfCrossEq (_root_.AbcTwoNinths.Diamond.exactOfMod (h v hv w hw) (h w hw v hv) (_root_.AbcTwoNinths.Diamond.crossEqMod h hv hw he))

end

end AbcTwoNinths.Diamond
