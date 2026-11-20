/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module
public import AbcTwoNinths.Basic.PlaneDiamond
public import AbcTwoNinths.Basic.CellCount

/-!
# Plane Height Seminorm

The height of a plane vector defines a seminorm by subadditivity and absolute homogeneity.

## Main results
* `AbcTwoNinths.Basic.heightSeminorm`
-/

@[expose] public section
namespace AbcTwoNinths.Basic

noncomputable section Geometry
open Set MeasureTheory


section

variable {n : ℕ}

/-- The height seminorm. -/
def heightSeminorm (s : _root_.AbcTwoNinths.Basic.Shape n) : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane :=
  Seminorm.ofSMulLE (_root_.AbcTwoNinths.Basic.height s)
    (by simp [_root_.AbcTwoNinths.Basic.height, _root_.AbcTwoNinths.Basic.logCoord, _root_.AbcTwoNinths.Basic.exponent])
    (fun x y => by
      rw [show x+y = _root_.AbcTwoNinths.Basic.lin 1 1 x y by ext <;> simp [_root_.AbcTwoNinths.Basic.lin]]
      simpa only [abs_one,one_mul] using _root_.AbcTwoNinths.Basic.heightLinLe s 1 1 x y)
    (fun r x => by
      rw [show r • x = _root_.AbcTwoNinths.Basic.lin r 0 x 0 by ext <;> simp [_root_.AbcTwoNinths.Basic.lin]]
      simpa only [Real.norm_eq_abs, abs_zero, zero_mul, add_zero] using _root_.AbcTwoNinths.Basic.heightLinLe s r 0 x 0)

end
end Geometry

end AbcTwoNinths.Basic
