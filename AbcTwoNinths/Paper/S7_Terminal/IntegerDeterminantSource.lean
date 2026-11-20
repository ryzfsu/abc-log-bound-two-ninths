/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantBounds
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPlaneData

/-!
# Integer Determinant Source

Evaluating a plane character at signed integer sites gives the rational row values. Clearing the
row denominators gives the integer determinant used in Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.rowValues`
* `AbcTwoNinths.Terminal.numerator`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section



open scoped BigOperators

/-- The row. This is used in Section 7 of the paper. -/
abbrev Row (K : ℕ) := Fin K ⊕ Fin K
/-- The plane character. This is used in Section 7 of the paper. -/
abbrev PlaneCharacter := Multiplicative (ℤ × ℤ) →* ℚˣ

/--
Evaluate a plane character at the original signed integer sites. This is used in Section 7 of the paper.
-/
def rowValues {K : ℕ} (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter) (sites : _root_.AbcTwoNinths.Terminal.Row K → ℤ × ℤ) : _root_.AbcTwoNinths.Terminal.Row K → ℚ :=
  fun i => γ (Multiplicative.ofAdd (sites i))

/-- The numerator. This is used in Section 7 of the paper. -/
def numerator {K : ℕ} (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter) (sites : _root_.AbcTwoNinths.Terminal.Row K → ℤ × ℤ) : ℤ :=
  (_root_.AbcTwoNinths.Terminal.integerMinor (fun i => (sites i).2) (_root_.AbcTwoNinths.Terminal.rowValues γ sites)).det

end

end AbcTwoNinths.Terminal
