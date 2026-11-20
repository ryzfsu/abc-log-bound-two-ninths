/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import Mathlib.Tactic

/-!
# Join

The module lifts a residue equal to plus or minus one to the signed kernel and identifies the corrected rational quotient. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.join`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section


/--
If `v` represents `n / d` and its residue has the indicated sign modulo an odd prime with
`d` invertible, `v` belongs to the kernel modulo signs and `gammaStar` gives the signed
ratio.
-/
theorem join {p : ℕ} [Fact p.Prime] [Fact (2 < p)] {I : Type*} [Fintype I]
    (r : _root_.AbcTwoNinths.ExteriorE2.Exponents I →* (ZMod p)ˣ) (m : _root_.AbcTwoNinths.ExteriorE2.Exponents I →* ℚˣ)
    (v : _root_.AbcTwoNinths.ExteriorE2.Exponents I) (n d : ℕ) (neg : Bool)
    (hd : (d : ZMod p) ≠ 0)
    (hr : (r v : ZMod p) * d = n)
    (hs : (n : ZMod p) = if neg then -(d : ZMod p) else d)
    (hm : (m v : ℚ) = (n : ℚ) / d) :
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = v ∧
      (_root_.AbcTwoNinths.ExteriorE2.gammaStar r m w : ℚ) = if neg then -((n : ℚ)/d) else (n : ℚ)/d := by
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hs ⊢
    have he : r v = 1 := by
      apply Units.ext
      change (r v : ZMod p) = 1
      exact mul_right_cancel₀ hd (by simpa only [one_mul] using hr.trans hs)
    refine ⟨⟨v, (_root_.AbcTwoNinths.ExteriorE2.memKer r v).2 (Or.inl he)⟩, rfl, ?_⟩
    simpa [_root_.AbcTwoNinths.ExteriorE2.gammaStar, _root_.AbcTwoNinths.ExteriorE2.signUnit, he] using hm
  | true =>
    simp only [↓reduceIte] at hs ⊢
    have he : r v = -1 := by
      apply Units.ext
      change (r v : ZMod p) = -1
      exact mul_right_cancel₀ hd (by simpa only [neg_one_mul] using hr.trans hs)
    refine ⟨⟨v, (_root_.AbcTwoNinths.ExteriorE2.memKer r v).2 (Or.inr he)⟩, rfl, ?_⟩
    simp [_root_.AbcTwoNinths.ExteriorE2.gammaStar, _root_.AbcTwoNinths.ExteriorE2.signUnit, he, _root_.AbcTwoNinths.ExteriorE2.minusNeOne, hm]

end

end AbcTwoNinths.ExteriorE2
