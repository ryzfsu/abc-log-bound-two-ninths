/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice
public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantSource
public import AbcTwoNinths.Paper.S6_Diamond.BadPairCount
public import AbcTwoNinths.Paper.S7_Terminal.InterpolationMinorNonvanishing
public import AbcTwoNinths.Basic.ExactMonomialHeights
public import AbcTwoNinths.Paper.S7_Terminal.ShearedDiamond

/-!
# Old Support Character Height

The module bounds row heights of the old-support character through its signed prime exponent coordinates. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.logRowHeightMaxCharacter`
* `AbcTwoNinths.Terminal.coordinateLogLeLogRowHeightMaxCharacter`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section




open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

private theorem toNatCastEqMax (a : ℤ) : (a.toNat : ℝ) = max (a : ℝ) 0 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left (by exact_mod_cast ha)]
    exact_mod_cast Int.toNat_of_nonneg ha
  · have han : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right (by exact_mod_cast han), Int.toNat_eq_zero.mpr han, Nat.cast_zero]

/--
The logarithmic height of the signed character equals the height of its prime exponents. This is used in Section 7 of the paper.
-/
theorem logRowHeightMaxCharacter (base : ι → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (hi : Function.Injective base) (z : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) :
    Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Diamond.character base prime avoid z : ℚ) : ℝ) =
      _root_.AbcTwoNinths.Diamond.height base z.val.toAdd := by
  classical
  let S := Finset.univ.image base
  let b := Function.extend base z.val.toAdd (fun _ => 0)
  have hb (i : ι) : b (base i) = z.val.toAdd i := hi.extend_apply _ _ _
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact prime i
  have hm : (_root_.AbcTwoNinths.ExteriorE2.monomial base prime z.val : ℚ) = _root_.AbcTwoNinths.Basic.monomial S b 1 := by
    change ((↑(∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime i ^ z.val.toAdd i) : ℚ)) = _
    rw [_root_.AbcTwoNinths.Basic.monomial, one_mul, Finset.prod_image (fun i _ j _ h => hi h)]
    change (Units.coeHom ℚ) (∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime i ^ z.val.toAdd i) = _
    rw [map_prod]
    change (∏ i, ((_root_.AbcTwoNinths.ExteriorE2.ratUnit base prime i ^ z.val.toAdd i : ℚˣ) : ℚ)) = _
    simp only [Units.val_zpow_eq_zpow_val, _root_.AbcTwoNinths.ExteriorE2.ratUnit, Units.val_mk0, hb]
  have hs : Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Diamond.character base prime avoid z : ℚ) : ℝ) =
      _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.Basic.monomial S b 1) := by
    change Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax ((↑(_root_.AbcTwoNinths.ExteriorE2.signUnit
      (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid) z * _root_.AbcTwoNinths.ExteriorE2.monomial base prime z.val) : ℚ)) : ℝ) = _
    rw [Units.val_mul, hm]
    by_cases hsign : _root_.AbcTwoNinths.ExteriorE2.residue base prime avoid z.val = 1 <;>
      simp [_root_.AbcTwoNinths.ExteriorE2.signUnit, hsign, _root_.AbcTwoNinths.Basic.rationalHeight, _root_.AbcTwoNinths.Terminal.rowHeightMax]
  rw [hs, _root_.AbcTwoNinths.Basic.exactLogHeight S b hprime]
  unfold _root_.AbcTwoNinths.Diamond.height _root_.AbcTwoNinths.Diamond.side
  simp only [S, Finset.sum_image (fun i _ j _ h => hi h), hb, toNatCastEqMax,
    Int.cast_neg, Pi.neg_apply]

/--
An absolute exponent times the logarithm of its prime is bounded by the logarithmic character height. This is used in Section 7 of the paper.
-/
theorem coordinateLogLeLogRowHeightMaxCharacter
    (base : ι → ℕ) (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i)
    (hi : Function.Injective base) (z : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (i : ι) :
    |(z.val.toAdd i : ℝ)| * Real.log (base i) ≤
      Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Diamond.character base prime avoid z : ℚ) : ℝ) := by
  rw [_root_.AbcTwoNinths.Terminal.logRowHeightMaxCharacter base prime avoid hi]
  have hterm (e : ι → ℤ) : max (e i : ℝ) 0 * Real.log (base i) ≤ _root_.AbcTwoNinths.Diamond.side base e := by
    unfold _root_.AbcTwoNinths.Diamond.side
    exact Finset.single_le_sum
      (f := fun j => max (e j : ℝ) 0 * Real.log (base j))
      (fun j _ => mul_nonneg (le_max_right _ _) (Real.log_nonneg (by exact_mod_cast (prime j).one_le)))
      (Finset.mem_univ i)
  by_cases h : 0 ≤ (z.val.toAdd i : ℝ)
  · apply le_trans _ (le_max_left (_root_.AbcTwoNinths.Diamond.side base z.val.toAdd) (_root_.AbcTwoNinths.Diamond.side base (-z.val.toAdd)))
    simpa only [abs_of_nonneg h, max_eq_left h] using hterm z.val.toAdd
  · have hn : (z.val.toAdd i : ℝ) < 0 := lt_of_not_ge h
    have hp : 0 ≤ -(z.val.toAdd i : ℝ) := neg_nonneg.mpr hn.le
    apply le_trans _ (le_max_right (_root_.AbcTwoNinths.Diamond.side base z.val.toAdd) (_root_.AbcTwoNinths.Diamond.side base (-z.val.toAdd)))
    simpa only [Pi.neg_apply, Int.cast_neg, abs_of_neg hn, max_eq_left hp]
      using hterm (-z.val.toAdd)

/-- An absolute exponent times log two is bounded by the logarithmic character height. -/
theorem coordinateLogTwoLeLogRowHeightMaxCharacter
    (base : ι → ℕ) (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i)
    (hi : Function.Injective base) (z : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (i : ι) :
    |(z.val.toAdd i : ℝ)| * Real.log 2 ≤
      Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Diamond.character base prime avoid z : ℚ) : ℝ) :=
  (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num) (by exact_mod_cast (prime i).two_le)) (abs_nonneg _)).trans
    (_root_.AbcTwoNinths.Terminal.coordinateLogLeLogRowHeightMaxCharacter base prime avoid hi z i)

end
end

end AbcTwoNinths.Terminal
