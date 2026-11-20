/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Plane Diamond

The module defines the exponent plane, its signed kernel lattice, and the logarithmic coordinates of monomial evaluation.

## Main results
* `AbcTwoNinths.Basic.heightLinLe`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section
noncomputable section Geometry
open scoped BigOperators

/-- The coord. -/
abbrev Coord := ℝ × ℝ

/-- Finite distinct prime support, and an ordered basis of a rank-two exponent lattice. -/
structure Shape (n : ℕ) where
  primeAt : Fin n → ℕ
  prime : ∀ i, (primeAt i).Prime
  distinct : Function.Injective primeAt
  v : Fin n → ℤ
  u : Fin n → ℤ
  independent : ∀ a b : ℝ, (∀ i, a * (v i : ℝ) + b * (u i : ℝ) = 0) → a = 0 ∧ b = 0

variable {n : ℕ}

/-- The exponent. -/
def exponent (s : _root_.AbcTwoNinths.Basic.Shape n) (z : _root_.AbcTwoNinths.Basic.Coord) (i : Fin n) : ℝ :=
  z.1 * (s.v i : ℝ) + z.2 * (s.u i : ℝ)

/-- The plane diamond monomial. -/
def planeDiamondMonomial (s : _root_.AbcTwoNinths.Basic.Shape n) (w : Fin n → ℤ) : ℚ :=
  ∏ i, (s.primeAt i : ℚ) ^ w i

/-- The log coord. -/
def logCoord (s : _root_.AbcTwoNinths.Basic.Shape n) (z : _root_.AbcTwoNinths.Basic.Coord) (i : Fin n) : ℝ :=
  _root_.AbcTwoNinths.Basic.exponent s z i * Real.log (s.primeAt i : ℝ)

/-- The height. -/
def height (s : _root_.AbcTwoNinths.Basic.Shape n) (z : _root_.AbcTwoNinths.Basic.Coord) : ℝ :=
  max (∑ i, max (_root_.AbcTwoNinths.Basic.logCoord s z i) 0) (∑ i, max (-_root_.AbcTwoNinths.Basic.logCoord s z i) 0)

/-- The lin. -/
def lin (a b : ℝ) (x y : _root_.AbcTwoNinths.Basic.Coord) : _root_.AbcTwoNinths.Basic.Coord := (a*x.1+b*y.1, a*x.2+b*y.2)

/-- Each logarithmic coordinate is linear in the two plane coordinates. -/
theorem logCoordLin (s : _root_.AbcTwoNinths.Basic.Shape n) (a b : ℝ) (x y : _root_.AbcTwoNinths.Basic.Coord) (i : Fin n) :
    _root_.AbcTwoNinths.Basic.logCoord s (_root_.AbcTwoNinths.Basic.lin a b x y) i = a * _root_.AbcTwoNinths.Basic.logCoord s x i + b * _root_.AbcTwoNinths.Basic.logCoord s y i := by
  unfold _root_.AbcTwoNinths.Basic.logCoord _root_.AbcTwoNinths.Basic.exponent _root_.AbcTwoNinths.Basic.lin
  dsimp
  ring

/-- Twice the height is the sum of the absolute log coordinates plus the absolute value
of their sum. -/
theorem heightAbs (s : _root_.AbcTwoNinths.Basic.Shape n) (z : _root_.AbcTwoNinths.Basic.Coord) :
    2 * _root_.AbcTwoNinths.Basic.height s z = (∑ i, |_root_.AbcTwoNinths.Basic.logCoord s z i|) + |∑ i, _root_.AbcTwoNinths.Basic.logCoord s z i| := by
  let P := ∑ i, max (_root_.AbcTwoNinths.Basic.logCoord s z i) 0
  let Q := ∑ i, max (-_root_.AbcTwoNinths.Basic.logCoord s z i) 0
  have hadd : (∑ i, |_root_.AbcTwoNinths.Basic.logCoord s z i|) = P + Q := by
    dsimp [P,Q]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rcases le_total 0 (_root_.AbcTwoNinths.Basic.logCoord s z i) with h | h <;> simp [abs_of_nonneg, abs_of_nonpos, *]
  have hsub : (∑ i, _root_.AbcTwoNinths.Basic.logCoord s z i) = P - Q := by
    dsimp [P,Q]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rcases le_total 0 (_root_.AbcTwoNinths.Basic.logCoord s z i) with h | h <;> simp [*]
  change 2 * max P Q = _
  rw [hadd, hsub]
  rcases le_total P Q with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- The height of a real linear combination is bounded by the sum of the heights
weighted by the absolute values of the coefficients. -/
theorem heightLinLe (s : _root_.AbcTwoNinths.Basic.Shape n) (a b : ℝ) (x y : _root_.AbcTwoNinths.Basic.Coord) :
    _root_.AbcTwoNinths.Basic.height s (_root_.AbcTwoNinths.Basic.lin a b x y) ≤ |a| * _root_.AbcTwoNinths.Basic.height s x + |b| * _root_.AbcTwoNinths.Basic.height s y := by
  have point (u v : ℝ) : |a*u+b*v| ≤ |a| * |u| + |b| * |v| := by
    simpa only [abs_mul] using abs_add_le (a*u) (b*v)
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin n) _ => point (_root_.AbcTwoNinths.Basic.logCoord s x i) (_root_.AbcTwoNinths.Basic.logCoord s y i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have ht := point (∑ i, _root_.AbcTwoNinths.Basic.logCoord s x i) (∑ i, _root_.AbcTwoNinths.Basic.logCoord s y i)
  have hl := _root_.AbcTwoNinths.Basic.heightAbs s (_root_.AbcTwoNinths.Basic.lin a b x y)
  simp only [_root_.AbcTwoNinths.Basic.logCoordLin] at hl
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hl
  nlinarith only [hl, hs, ht, congrArg (|a| * ·) (_root_.AbcTwoNinths.Basic.heightAbs s x),
    congrArg (|b| * ·) (_root_.AbcTwoNinths.Basic.heightAbs s y)]

end Geometry
end

end AbcTwoNinths.Basic
