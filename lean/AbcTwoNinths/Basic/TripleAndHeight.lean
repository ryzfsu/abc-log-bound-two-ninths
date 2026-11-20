/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Triple And Height

The module defines the radical, height, and local-prime conditions for the triple estimates.

## Main results
* `AbcTwoNinths.Basic.PrincipalUnitLengthBound`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

noncomputable section

open Real

/-- The radical. -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The rational size. -/
def rationalSize (y : ℚ) : ℕ := y.num.natAbs * y.den
/-- The rational length. -/
def rationalLength (y : ℚ) : ℝ := log (_root_.AbcTwoNinths.Basic.rationalSize y)
/-- The rational height. -/
def rationalHeight (y : ℚ) : ℝ := log (max y.num.natAbs y.den : ℕ)

/-- The rat principal unit. -/
def RatPrincipalUnit (p : ℕ) (a : ℚ) : Prop :=
  a ≠ 0 ∧ padicValRat p a = 0 ∧ (a = 1 ∨ 0 < padicValRat p (a - 1))

/-- The rat mul independent. -/
def RatMulIndependent (a b : ℚ) : Prop :=
  ∀ m n : ℤ, a ^ m * b ^ n = 1 → m = 0 ∧ n = 0

/-- The is positive principal unit. -/
def IsPositivePrincipalUnit (p : ℕ) (y : ℚ) : Prop := 0 < y ∧ _root_.AbcTwoNinths.Basic.RatPrincipalUnit p y

/-- The triple. -/
structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  apos : 0 < a
  bpos : 0 < b
  add : a + b = c
  coprime : a.Coprime b

/-- The triple.radical. -/
def Triple.radical (t : _root_.AbcTwoNinths.Basic.Triple) : ℕ := _root_.AbcTwoNinths.Basic.radical (t.a * t.b * t.c)
/-- The triple.log height. -/
def Triple.logHeight (t : _root_.AbcTwoNinths.Basic.Triple) : ℝ := log t.c
/-- The triple.log radical. -/
def Triple.logRadical (t : _root_.AbcTwoNinths.Basic.Triple) : ℝ := log t.radical
/-- The triple.third log radical. -/
def Triple.thirdLogRadical (t : _root_.AbcTwoNinths.Basic.Triple) : ℝ := t.logRadical / 3

/-- The monomial. -/
def monomial (s : Finset ℕ) (b : ℕ → ℤ) (e : ℚ) : ℚ :=
  e * ∏ q ∈ s, (q : ℚ) ^ b q

/-- The principal unit length bound. -/
def PrincipalUnitLengthBound : Prop :=
  ∀ (p : ℕ) (y : ℚ), p.Prime → _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p y → y ≠ 1 →
    p + 1 ≤ max y.num.natAbs y.den ∧ (log (p : ℝ)) < _root_.AbcTwoNinths.Basic.rationalLength y

end

end

end AbcTwoNinths.Basic
