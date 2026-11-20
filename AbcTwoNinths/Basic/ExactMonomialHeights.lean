/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Exact Monomial Heights

The module identifies the height of a side ratio with logarithms of its coprime monomial parts.

## Main results
* `AbcTwoNinths.Basic.exactLogHeight`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section
open Real

/-- Multiply the support primes raised to the positive parts of their exponents. -/
def side (s : Finset ℕ) (b : ℕ → ℤ) : ℕ := ∏ q ∈ s, q ^ (b q).toNat

/-- The positive-exponent product on a finite set of primes is positive. -/
theorem sidePos (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    0 < _root_.AbcTwoNinths.Basic.side s b :=
  Finset.prod_pos fun q hq => pow_pos (hp q hq).pos _

/-- The products from an exponent vector and its negative are coprime. -/
theorem sideCoprime (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    (_root_.AbcTwoNinths.Basic.side s b).Coprime (_root_.AbcTwoNinths.Basic.side s (fun q => -b q)) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hps
  apply Nat.coprime_prod_right_iff.mpr
  intro q hqs
  by_cases he : p = q
  · subst q
    by_cases h : 0 ≤ b p
    · simp [Int.toNat_eq_zero.mpr (show -b p ≤ 0 by omega)]
    · simp [Int.toNat_eq_zero.mpr (show b p ≤ 0 by omega)]
  · exact (((Nat.coprime_primes (hp p hps) (hp q hqs)).mpr he).pow_left _).pow_right _

/--
A rational prime monomial with coefficient one is the quotient of its positive and negative exponent products.
-/
theorem splitMonomial (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    _root_.AbcTwoNinths.Basic.monomial s b 1 = (_root_.AbcTwoNinths.Basic.side s b : ℚ) / (_root_.AbcTwoNinths.Basic.side s (fun q => -b q) : ℚ) := by
  simp only [_root_.AbcTwoNinths.Basic.monomial, one_mul, _root_.AbcTwoNinths.Basic.side, Nat.cast_prod, Nat.cast_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have hne : (q : ℚ) ≠ 0 := by exact_mod_cast (hp q hq).ne_zero
  have he : b q = ((b q).toNat : ℤ) - ((-b q).toNat : ℤ) := by omega
  conv_lhs => rw [he, zpow_sub₀ hne]
  simp only [zpow_natCast]

/-- The logarithmic height is the logarithm of the larger of the two exponent products. -/
theorem exactHeight (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.Basic.monomial s b 1) = log (max (_root_.AbcTwoNinths.Basic.side s b) (_root_.AbcTwoNinths.Basic.side s (fun q => -b q)) : ℕ) := by
  let n := _root_.AbcTwoNinths.Basic.side s b
  let d := _root_.AbcTwoNinths.Basic.side s (fun q => -b q)
  have hd : 0 < (d : ℤ) := by exact_mod_cast _root_.AbcTwoNinths.Basic.sidePos s (fun q => -b q) hp
  have hcop : (n : ℤ).natAbs.Coprime (d : ℤ).natAbs := by simpa [n,d] using _root_.AbcTwoNinths.Basic.sideCoprime s b hp
  have hn := Rat.num_div_eq_of_coprime hd hcop
  have hden := Rat.den_div_eq_of_coprime hd hcop
  simp only [Int.cast_natCast] at hn hden
  have hden' : ((n : ℚ) / d).den = d := by exact_mod_cast hden
  rw [_root_.AbcTwoNinths.Basic.splitMonomial s b hp]
  change log (max ((n : ℚ) / d).num.natAbs ((n : ℚ) / d).den : ℕ) = _
  simp [hn, hden', n, d]

/--
The logarithm of the positive-exponent product is the sum of the positive exponents weighted by log prime.
-/
theorem logSide (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    log (_root_.AbcTwoNinths.Basic.side s b : ℝ) = ∑ q ∈ s, ((b q).toNat : ℝ) * log (q : ℝ) := by
  simp only [_root_.AbcTwoNinths.Basic.side, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod (fun q hq => pow_ne_zero _ (by exact_mod_cast (hp q hq).ne_zero))]
  simp only [Real.log_pow]

/--
The height of a rational prime monomial is the maximum of its positive and negative exponent log sums.
-/
theorem exactLogHeight (s : Finset ℕ) (b : ℕ → ℤ) (hp : ∀ q ∈ s, q.Prime) :
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.Basic.monomial s b 1) =
      max (∑ q ∈ s, ((b q).toNat : ℝ) * log (q : ℝ))
          (∑ q ∈ s, ((-b q).toNat : ℝ) * log (q : ℝ)) := by
  rw [_root_.AbcTwoNinths.Basic.exactHeight s b hp, ← _root_.AbcTwoNinths.Basic.logSide s b hp, ← _root_.AbcTwoNinths.Basic.logSide s (fun q => -b q) hp]
  by_cases h : _root_.AbcTwoNinths.Basic.side s b ≤ _root_.AbcTwoNinths.Basic.side s (fun q => -b q)
  · rw [max_eq_right h, max_eq_right (Real.log_le_log (by exact_mod_cast _root_.AbcTwoNinths.Basic.sidePos s b hp) (by exact_mod_cast h))]
  · have h' := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (Real.log_le_log (by exact_mod_cast _root_.AbcTwoNinths.Basic.sidePos s (fun q => -b q) hp) (by exact_mod_cast h'))]

end

end AbcTwoNinths.Basic
