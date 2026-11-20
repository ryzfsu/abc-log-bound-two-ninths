/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeBudgetBound

/-!
# Composite Interpolation Edges

The module bounds the exponent and height budgets along the edges of a composite interpolation grid. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeEdgeBudgets`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section


/--
The chosen rectangular grids have at least `36` and more than `36 * J` points respectively,
and their combined edges satisfy the weighted degree and height bounds.
-/
theorem compositeEdgeBudgets (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c d : ℕ) :
    let J := _root_.AbcTwoNinths.Basic.order (a*b)
    let R := _root_.AbcTwoNinths.Basic.edge 36 a b
    let S := _root_.AbcTwoNinths.Basic.edge 36 b a
    let R' := _root_.AbcTwoNinths.Basic.edge (J*36) a b
    let S' := _root_.AbcTwoNinths.Basic.edge (J*36) b a
    36 ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S) ∧
    36*J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S') ∧
    ((((R+R')*d+(S+S')*c : ℕ) : ℝ)) ≤ (127*(a*b)) * ((d : ℝ)/b + (c : ℝ)/a) ∧
    ((R+R' : ℕ) : ℝ)*b + ((S+S' : ℕ) : ℝ)*a ≤ 2*(127*(a*b)) := by
  dsimp only
  have h1 := _root_.AbcTwoNinths.Basic.rectCard 36 a b (by linarith) (by linarith)
  have h2 := _root_.AbcTwoNinths.Basic.rectCard (_root_.AbcTwoNinths.Basic.order (a*b)*36) a b (by linarith) (by linarith)
  have hx := _root_.AbcTwoNinths.Basic.maxCoordCost a b ha hb
  have hy := _root_.AbcTwoNinths.Basic.maxCoordCost b a hb ha
  rw [mul_comm b a] at hy
  have hm : _root_.AbcTwoNinths.Basic.maxCoord b a = _root_.AbcTwoNinths.Basic.edge 36 b a + _root_.AbcTwoNinths.Basic.edge (_root_.AbcTwoNinths.Basic.order (a*b)*36) b a := by
    simp only [_root_.AbcTwoNinths.Basic.maxCoord, _root_.AbcTwoNinths.Basic.levels, mul_comm b a]
  have hhx : (_root_.AbcTwoNinths.Basic.maxCoord a b : ℝ) ≤ 127*(a*b)/b :=
    (le_div_iff₀ (by linarith)).2 hx
  have hhy : (_root_.AbcTwoNinths.Basic.maxCoord b a : ℝ) ≤ 127*(a*b)/a :=
    (le_div_iff₀ (by linarith)).2 hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [_root_.AbcTwoNinths.Basic.Rectangle] using h1.le
  · simpa [_root_.AbcTwoNinths.Basic.Rectangle, mul_comm 36 (_root_.AbcTwoNinths.Basic.order (a*b))] using h2
  · rw [← hm]
    change (((_root_.AbcTwoNinths.Basic.maxCoord a b*d+_root_.AbcTwoNinths.Basic.maxCoord b a*c : ℕ) : ℝ)) ≤ _
    push_cast
    calc
      _ ≤ (127*(a*b)/b)*(d : ℝ) + (127*(a*b)/a)*(c : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hhx (by positivity))
          (mul_le_mul_of_nonneg_right hhy (by positivity))
      _ = _ := by ring
  · rw [← hm]
    change (_root_.AbcTwoNinths.Basic.maxCoord a b : ℝ)*b + (_root_.AbcTwoNinths.Basic.maxCoord b a : ℝ)*a ≤ _
    linarith

end

end AbcTwoNinths.ExteriorE2
