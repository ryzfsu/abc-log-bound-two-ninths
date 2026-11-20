/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.FreshRatio
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Bad Pair Fiber

The module bounds signed fibers and sums the fiber bounds over their image. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.cardSignedFiberLe`
* `AbcTwoNinths.Diamond.cardLeSumSignedFibers`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

section


open Polynomial
open scoped BigOperators

/--
At most twice the positive exponent many reduced pairs with distinct ratios satisfy a fixed signed power congruence. This is used in Section 6 of the paper.
-/
theorem cardSignedFiberLe {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (S : Finset _root_.AbcTwoNinths.Diamond.Pair) (hCross : _root_.AbcTwoNinths.Diamond.CrossBound p (↑S : Set _root_.AbcTwoNinths.Diamond.Pair)) (old : ZMod p)
    (hSigned : ∀ v ∈ S, old * _root_.AbcTwoNinths.Diamond.ratio p v ^ b = 1 ∨ old * _root_.AbcTwoNinths.Diamond.ratio p v ^ b = -1) :
    S.card ≤ 2 * b := by
  classical
  let P : (ZMod p)[X] := X ^ (2 * b) - C (old⁻¹ ^ 2)
  have hpos : 0 < 2 * b := Nat.mul_pos (by decide) hb
  have hP : P ≠ 0 := X_pow_sub_C_ne_zero hpos _
  have hsubset : S.image (_root_.AbcTwoNinths.Diamond.ratio p) ⊆ P.roots.toFinset := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hOld : old ≠ 0 := by
      intro h0
      rcases hSigned v hv with h | h
      · simp [h0] at h
      · simp [h0] at h
    have hSquare : (old * _root_.AbcTwoNinths.Diamond.ratio p v ^ b) ^ 2 = 1 := by
      rcases hSigned v hv with h | h <;> rw [h] <;> simp
    have hPow : _root_.AbcTwoNinths.Diamond.ratio p v ^ (2 * b) = old⁻¹ ^ 2 := by
      have h := congrArg (fun x : ZMod p => old⁻¹ ^ 2 * x) hSquare
      rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hOld, one_pow,
        one_mul, mul_one, ← pow_mul, Nat.mul_comm b 2] at h
      exact h
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hP).mpr
    simp [P, IsRoot, hPow]
  calc
    S.card = (S.image (_root_.AbcTwoNinths.Diamond.ratio p)).card :=
      (Finset.card_image_of_injOn (_root_.AbcTwoNinths.Diamond.injOnRatio hCross)).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ 2 * b := card_roots_X_pow_sub_C hpos _

/--
The number of coded pairs satisfying signed power congruences is bounded by the sum of twice their exponents over the codes. This is used in Section 6 of the paper.
-/
theorem cardLeSumSignedFibers {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (S : Finset _root_.AbcTwoNinths.Diamond.Pair) (hCross : _root_.AbcTwoNinths.Diamond.CrossBound p (↑S : Set _root_.AbcTwoNinths.Diamond.Pair)) (codes : Finset ι)
    (code : _root_.AbcTwoNinths.Diamond.Pair → ι) (exponent : ι → ℕ) (old : ι → ZMod p)
    (hCode : ∀ v ∈ S, code v ∈ codes)
    (hPos : ∀ k ∈ codes, 0 < exponent k)
    (hSigned : ∀ v ∈ S, old (code v) * _root_.AbcTwoNinths.Diamond.ratio p v ^ exponent (code v) = 1 ∨
      old (code v) * _root_.AbcTwoNinths.Diamond.ratio p v ^ exponent (code v) = -1) :
    S.card ≤ ∑ k ∈ codes, 2 * exponent k := by
  rw [Finset.card_eq_sum_card_fiberwise hCode]
  refine Finset.sum_le_sum fun k hk => ?_
  refine _root_.AbcTwoNinths.Diamond.cardSignedFiberLe (hPos k hk) (S.filter (fun v => code v = k)) ?_ (old k) ?_
  · intro v hv w hw
    exact hCross v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1
  · intro v hv
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hv
    simpa only [he] using hSigned v hm

end

end AbcTwoNinths.Diamond
