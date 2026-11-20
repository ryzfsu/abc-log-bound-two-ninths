/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.IntegralInterpolationMinor
public import AbcTwoNinths.Paper.S7_Terminal.NonzeroIntegralMinor

/-!
# Integral Join

The module identifies the integral and rational realizations of a selected minor to combine valuation and numerator bounds. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.mapIntegralMinorEq`
* `AbcTwoNinths.Terminal.sameMinorValuation`
* `AbcTwoNinths.Terminal.selectedNumeratorBounds`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section



/--
The integral and rational interpolation matrices agree entrywise over the p-adic field when their row values agree. This is used in Section 7 of the paper.
-/
theorem mapIntegralMinorEq {p K : ℕ} [Fact p.Prime] (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℤ)
    (w : _root_.AbcTwoNinths.Terminal.Slots K → ℚ) (z a : ℤ_[p]ˣ)
    (hrow : ∀ i, ((↑(z ^ x i * a ^ y i) : ℤ_[p]) : ℚ_[p]) = (w i : ℚ_[p])) :
    (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).map PadicInt.Coe.ringHom =
      (_root_.AbcTwoNinths.Terminal.rationalMinor y w).map (Rat.castHom ℚ_[p]) := by
  have hcast (s : ℤ) : PadicInt.Coe.ringHom (s : ℤ_[p]) = Rat.castHom ℚ_[p] (s : ℚ) := by simp
  ext i j
  cases j with
  | inl k => exact hcast (Ring.choose (y i) k.val)
  | inr k =>
    simp only [Matrix.map_apply, _root_.AbcTwoNinths.Terminal.integralMinor, _root_.AbcTwoNinths.Terminal.rationalMinor, Matrix.of_apply, map_mul]
    rw [hcast]
    congr 1
    exact hrow i

/--
A nonzero rational minor with principal row generators of depths m and one has valuation at least two ninths of the squared row count when four K is at most three m. This is used in Section 7 of the paper.
-/
theorem sameMinorValuation {p K m : ℕ} [Fact p.Prime] (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℤ)
    (w : _root_.AbcTwoNinths.Terminal.Slots K → ℚ) (z a : ℤ_[p]ˣ)
    (hz : (p : ℤ_[p]) ^ m ∣ (z : ℤ_[p]) - 1)
    (ha : (p : ℤ_[p]) ∣ (a : ℤ_[p]) - 1)
    (hrow : ∀ i, ((↑(z ^ x i * a ^ y i) : ℤ_[p]) : ℚ_[p]) = (w i : ℚ_[p]))
    (hnz : (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det ≠ 0) (hm : 4 * K ≤ 3 * m) :
    (2 / 9 : ℝ) * (2 * K : ℝ)^2 ≤ (padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det : ℝ) := by
  have hmat := _root_.AbcTwoNinths.Terminal.mapIntegralMinorEq x y w z a hrow
  have hcast : (((_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det : ℤ_[p]) : ℚ_[p]) =
      ((_root_.AbcTwoNinths.Terminal.rationalMinor y w).det : ℚ_[p]) := by
    change PadicInt.Coe.ringHom (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det =
      Rat.castHom ℚ_[p] (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det
    rw [RingHom.map_det, RingHom.map_det]
    exact congrArg Matrix.det hmat
  have hi : (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det ≠ 0 := by
    intro he
    have hc : ((_root_.AbcTwoNinths.Terminal.rationalMinor y w).det : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hnz
    exact hc (hcast.symm.trans (by rw [he]; norm_cast))
  have hval := _root_.AbcTwoNinths.Terminal.integralMinorValuation m 1 x y z a hz (by simpa using ha) hi
  have hv := _root_.AbcTwoNinths.Terminal.floorTwoNinths (r := 1) (by simpa using hm)
  have hd : ((_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det.valuation : ℤ) =
      padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det := by
    rw [← PadicInt.valuation_coe, hcast, Padic.valuation_ratCast]
  have hvalR : (_root_.AbcTwoNinths.Terminal.floor K m 1 : ℝ) ≤ (padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det : ℝ) := by
    rw [← hd]
    exact_mod_cast hval
  have hvR : (8 : ℝ) * (K : ℝ)^2 ≤ 9 * (_root_.AbcTwoNinths.Terminal.floor K m 1 : ℝ) := by
    exact_mod_cast (show 8 * K ^ 2 ≤ 9 * _root_.AbcTwoNinths.Terminal.floor K m 1 by simpa using hv)
  nlinarith only [hvalR, hvR]

/--
An injection into the sites and their translate selects one nonzero integer determinant satisfying the height bound and the conditional valuation lower bound. This is used in Section 7 of the paper.
-/
theorem selectedNumeratorBounds {p K m : ℕ} [Fact p.Prime] (hK : 0 < K)
    (γ : _root_.AbcTwoNinths.Terminal.Character) (w : _root_.AbcTwoNinths.Terminal.Site) (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1) (sites : Finset _root_.AbcTwoNinths.Terminal.Site)
    (hcount : 2 * K - 1 ≤ sites.card)
    (hlabels : Function.Injective (fun s : sites ↦ (s.1 : _root_.AbcTwoNinths.Terminal.Site).2))
    (hunit : ∀ s ∈ sites ∪ sites.image (fun s ↦ s + w), padicValRat p (_root_.AbcTwoNinths.Terminal.value γ s) = 0)
    (z a : ℤ_[p]ˣ)
    (hz : (p : ℤ_[p]) ^ m ∣ (z : ℤ_[p]) - 1)
    (ha : (p : ℤ_[p]) ∣ (a : ℤ_[p]) - 1)
    (hrow : ∀ s ∈ sites ∪ sites.image (fun s ↦ s + w),
      ((↑(z ^ s.1 * a ^ s.2) : ℤ_[p]) : ℚ_[p]) = (_root_.AbcTwoNinths.Terminal.value γ s : ℚ_[p]))
    {U B : ℝ} (hB : 0 < B)
    (hchoose : ∀ s ∈ sites ∪ sites.image (fun s ↦ s + w),
      ∀ k : Fin K, |((Ring.choose s.2 k.val : ℤ) : ℝ)| ≤ B)
    (hheight : ∀ selected : _root_.AbcTwoNinths.Terminal.Slots K ↪ _root_.AbcTwoNinths.Terminal.Site,
      (∀ i, selected i ∈ sites ∪ sites.image (fun s ↦ s + w)) →
      (∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ (selected i)) : ℝ)) ≤ U) :
    ∃ selected : _root_.AbcTwoNinths.Terminal.Slots K ↪ _root_.AbcTwoNinths.Terminal.Site,
      (∀ i, selected i ∈ sites ∪ sites.image (fun s ↦ s + w)) ∧
      let D := (_root_.AbcTwoNinths.Terminal.integerMinor (fun i ↦ (selected i).2) (fun i ↦ _root_.AbcTwoNinths.Terminal.value γ (selected i))).det
      D ≠ 0 ∧
      Real.log (D.natAbs : ℝ) ≤ U + Real.log ((2 * K).factorial : ℝ) +
        (2 * K : ℝ) * Real.log B ∧
      (4 * K ≤ 3 * m → (2 / 9 : ℝ) * (2 * K : ℝ)^2 * Real.log (p : ℝ) ≤
        Real.log (D.natAbs : ℝ)) := by
  obtain ⟨sel, hmem, hRat, hInt, hval⟩ := _root_.AbcTwoNinths.Terminal.existsSameMinor hK γ w hw sites hcount hlabels hunit
  let x := fun i ↦ (sel i).1
  let y := fun i ↦ (sel i).2
  let v := fun i ↦ _root_.AbcTwoNinths.Terminal.value γ (sel i)
  refine ⟨sel, hmem, hInt, ?_, ?_⟩
  · exact (_root_.AbcTwoNinths.Terminal.sameMinorLogUpper y v hB (fun i k ↦ hchoose _ (hmem i) k) hInt).trans (by
      gcongr
      exact hheight sel hmem)
  · intro hm
    have hfloor := _root_.AbcTwoNinths.Terminal.sameMinorValuation x y v z a hz ha (fun i ↦ hrow _ (hmem i)) hRat hm
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    have hvalR : (padicValInt p (_root_.AbcTwoNinths.Terminal.integerMinor y v).det : ℝ) =
        (padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y v).det : ℝ) := by exact_mod_cast hval
    exact (mul_le_mul_of_nonneg_right (hfloor.trans_eq hvalR.symm) hlog).trans
      (_root_.AbcTwoNinths.Terminal.logNatAbsGeValuation hInt)

end

end AbcTwoNinths.Terminal
