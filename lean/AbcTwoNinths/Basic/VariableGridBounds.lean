/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalDepthReduction

/-!
# Variable Grid Bounds

The module bounds duplicate-node valuations and combines the cost terms for variable-size grids.

## Main results
* `AbcTwoNinths.Basic.variableCombinedCosts`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section



/--
A collision of weighted nodes bounds the valuation of the difference of the two principal-unit powers.
-/
theorem variableDuplicateValuation {p L J c d r r' s s' : ℕ} [Fact p.Prime]
    (x y : ℚ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hp : 2 < p) (hx : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p x) (hy : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p y)
    (hxa : _root_.AbcTwoNinths.Basic.padicRationalHeight x ≤ A * Real.log p) (hyb : _root_.AbcTwoNinths.Basic.padicRationalHeight y ≤ B * Real.log p)
    (hc : c.Coprime d) (hc0 : 0 < c) (hd0 : 0 < d) (hxy : x^c ≠ y^d)
    (hr : r ≤ _root_.AbcTwoNinths.Basic.edge (J*L) B A) (hr' : r' ≤ _root_.AbcTwoNinths.Basic.edge (J*L) B A)
    (hs : s ≤ _root_.AbcTwoNinths.Basic.edge (J*L) A B) (hs' : s' ≤ _root_.AbcTwoNinths.Basic.edge (J*L) A B)
    (hne : (r,s) ≠ (r',s')) (he : r*d+s*c = r'*d+s'*c) :
    (padicValRat p (x^c-y^d) : ℝ) < 1+2*Real.sqrt ((J : ℝ)*L*(A*B)) := by
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have h₂ := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) hp'
  have h₁ := _root_.AbcTwoNinths.Basic.rationalDifferenceBound hx hy hxy
  have h₃ := mul_le_mul_of_nonneg_left hxa (Nat.cast_nonneg c)
  have h₄ := mul_le_mul_of_nonneg_left hyb (Nat.cast_nonneg d)
  obtain ⟨hcR, hdS⟩ := _root_.AbcTwoNinths.Basic.duplicateBounds hc hc0 hd0 hr hr' hs hs' hne he
  have hcR' : (c : ℝ) ≤ (_root_.AbcTwoNinths.Basic.edge (J*L) B A : ℝ) := by exact_mod_cast hcR
  have hdS' : (d : ℝ) ≤ (_root_.AbcTwoNinths.Basic.edge (J*L) A B : ℝ) := by exact_mod_cast hdS
  have hcA := (mul_le_mul_of_nonneg_right hcR' hA.le).trans (_root_.AbcTwoNinths.Basic.edgeCost (J*L) B A hB hA)
  have hdB := (mul_le_mul_of_nonneg_right hdS' hB.le).trans (_root_.AbcTwoNinths.Basic.edgeCost (J*L) A B hA hB)
  push_cast at hcA hdB
  rw [mul_comm B A] at hcA
  have hcost : (c : ℝ)*A + (d : ℝ)*B ≤ 2*Real.sqrt ((J : ℝ)*L*(A*B)) := by linarith
  have h₅ := mul_le_mul_of_nonneg_right hcost hl.le
  apply (mul_lt_mul_iff_left₀ hl).mp
  calc
    _ ≤ Real.log 2 + (c : ℝ)*_root_.AbcTwoNinths.Basic.padicRationalHeight x + (d : ℝ)*_root_.AbcTwoNinths.Basic.padicRationalHeight y := by
      linarith only [h₁]
    _ < (1 + 2*Real.sqrt ((J : ℝ)*L*(A*B))) * Real.log p := by
      nlinarith only [h₂, h₃, h₄, h₅]

/-- Bounds the cost of the sum of the two grid edges in one coordinate. -/
theorem variableCombinedEdgeCost (L J : ℕ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ((_root_.AbcTwoNinths.Basic.edge L B A + _root_.AbcTwoNinths.Basic.edge (J*L) B A : ℕ) : ℝ)*A ≤
      (1 + Real.sqrt (J : ℝ))*Real.sqrt ((L : ℝ)*(A*B)) := by
  have h₁ := _root_.AbcTwoNinths.Basic.edgeCost L B A hB hA
  have h₂ := _root_.AbcTwoNinths.Basic.edgeCost (J*L) B A hB hA
  rw [mul_comm B A] at h₁ h₂
  have hs : Real.sqrt ((↑(J*L) : ℝ)*(A*B)) =
      Real.sqrt (J : ℝ) * Real.sqrt ((L : ℝ)*(A*B)) := by
    push_cast
    rw [mul_assoc, Real.sqrt_mul (by positivity)]
  rw [hs] at h₂
  push_cast
  nlinarith only [h₁, h₂]

/-- Bounds both the mean height cost and the largest weighted node of the combined rectangle. -/
theorem variableCombinedCosts (L J c d : ℕ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    let R := _root_.AbcTwoNinths.Basic.edge L B A + _root_.AbcTwoNinths.Basic.edge (J*L) B A
    let S := _root_.AbcTwoNinths.Basic.edge L A B + _root_.AbcTwoNinths.Basic.edge (J*L) A B
    let V := (1 + Real.sqrt (J : ℝ))*Real.sqrt ((L : ℝ)*(A*B))
    ((R : ℝ)*A + (S : ℝ)*B)/2 ≤ V ∧
      ((R*d+S*c : ℕ) : ℝ) ≤ V*((c : ℝ)/B+(d : ℝ)/A) := by
  dsimp only
  have hR := _root_.AbcTwoNinths.Basic.variableCombinedEdgeCost L J A B hA hB
  have hS := _root_.AbcTwoNinths.Basic.variableCombinedEdgeCost L J B A hB hA
  rw [mul_comm B A] at hS
  refine ⟨by linarith only [hR, hS], ?_⟩
  have hx := mul_le_mul_of_nonneg_right hR (show 0 ≤ (d : ℝ)/A by positivity)
  have hy := mul_le_mul_of_nonneg_right hS (show 0 ≤ (c : ℝ)/B by positivity)
  rw [mul_assoc, mul_div_cancel₀ _ hA.ne'] at hx
  rw [mul_assoc, mul_div_cancel₀ _ hB.ne'] at hy
  push_cast at hx hy
  push_cast
  rw [mul_add]
  nlinarith only [hx, hy]

end

end AbcTwoNinths.Basic
