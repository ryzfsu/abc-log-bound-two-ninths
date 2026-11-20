/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic

/-!
# Principal Unit Data

A rational principal unit lies at p-adic distance less than one from `1` and has p-adic norm
one.

## Main results
* `AbcTwoNinths.Basic.PrincipalPrincipalUnitData`
* `AbcTwoNinths.Basic.principalNorm`
-/

@[expose] public section
namespace AbcTwoNinths.Basic

section

/--
A rational number is a principal unit at a prime when its p-adic distance from one is less than one.
-/
def PrincipalPrincipalUnitData (p : ℕ) [Fact p.Prime] (u : ℚ) : Prop :=
  ‖(u : ℚ_[p]) - 1‖ < 1

-- The analytic input and the geometric coprimality predicate are separate.

section Sanity

end Sanity

variable {p : ℕ} [Fact p.Prime]

/-- The image of a rational principal unit in the p-adic field has norm one. -/
theorem principalNorm {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p u) : ‖(u : ℚ_[p])‖ = 1 := by
  have h : ‖(u : ℚ_[p]) - 1‖ < ‖(1 : ℚ_[p])‖ := by simpa [_root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData] using hu
  simpa using Padic.norm_eq_of_norm_sub_lt_right h

end

end AbcTwoNinths.Basic
