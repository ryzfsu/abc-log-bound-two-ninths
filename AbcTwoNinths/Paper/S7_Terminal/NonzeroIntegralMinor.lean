/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic
public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket
public import AbcTwoNinths.Paper.S6_Diamond.BadPairCount
public import AbcTwoNinths.Paper.S4_ExteriorE2.SourceLattice
public import Mathlib
public import AbcTwoNinths.Basic.PlaneDiamond
public import AbcTwoNinths.Basic.RoofCovolume
public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlapCounting
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice
public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import AbcTwoNinths.Paper.S4_ExteriorE2.ProjectedMass
public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlap
public import AbcTwoNinths.Paper.S6_Diamond.MassThreshold
public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantSource
public import AbcTwoNinths.Paper.S1_Statement.Parameters
public import Mathlib.Analysis.Complex.Exponential
public import AbcTwoNinths.Paper.S1_Statement.RadicalScaleAndTail
public import AbcTwoNinths.Paper.S7_Terminal.InterpolationMinorNonvanishing

/-!
# Nonzero Integral Minor

The module combines row selection and the denominator-clearing identity for one nonzero selected minor. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.existsSameMinor`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section



/--
Selects common sites giving nonzero rational and numerator determinants with the same valuation at the chosen prime. This is used in Section 7 of the paper.
-/
theorem existsSameMinor {p K : ℕ} [Fact p.Prime] (hK : 0 < K)
    (γ : _root_.AbcTwoNinths.Terminal.Character) (w : _root_.AbcTwoNinths.Terminal.Site) (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1) (sites : Finset _root_.AbcTwoNinths.Terminal.Site)
    (hcount : 2 * K - 1 ≤ sites.card)
    (hlabels : Function.Injective (fun s : sites ↦ (s.1 : _root_.AbcTwoNinths.Terminal.Site).2))
    (hunit : ∀ s ∈ sites ∪ sites.image (fun s ↦ s + w), padicValRat p (_root_.AbcTwoNinths.Terminal.value γ s) = 0) :
    ∃ selected : (Fin K ⊕ Fin K) ↪ _root_.AbcTwoNinths.Terminal.Site,
      (∀ i, selected i ∈ sites ∪ sites.image (fun s ↦ s + w)) ∧
      let y := fun i ↦ (selected i).2
      let a := fun i ↦ _root_.AbcTwoNinths.Terminal.value γ (selected i)
      (_root_.AbcTwoNinths.Terminal.rationalMinor y a).det ≠ 0 ∧ (_root_.AbcTwoNinths.Terminal.integerMinor y a).det ≠ 0 ∧
      (padicValInt p (_root_.AbcTwoNinths.Terminal.integerMinor y a).det : ℤ) = padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y a).det := by
  obtain ⟨selected, hmem, hdet⟩ := _root_.AbcTwoNinths.Terminal.existsNonzeroMinor hK γ w hw sites hcount hlabels
  let y := fun i ↦ (selected i).2
  let a := fun i ↦ _root_.AbcTwoNinths.Terminal.value γ (selected i)
  have hsame : Matrix.of (fun i ↦ _root_.AbcTwoNinths.Terminal.row K γ (selected i)) = _root_.AbcTwoNinths.Terminal.rationalMinor y a := by
    have hchoose (s : ℤ) (k : ℕ) : ((Ring.choose s k : ℤ) : ℚ) = Ring.choose (s : ℚ) k :=
      Ring.map_choose (Int.castRingHom ℚ) s k
    ext i j
    cases j <;> simp [_root_.AbcTwoNinths.Terminal.row, _root_.AbcTwoNinths.Terminal.rationalMinor, y, a, hchoose]
  have hnz : (_root_.AbcTwoNinths.Terminal.rationalMinor y a).det ≠ 0 := hsame ▸ hdet
  obtain ⟨hnum, hval⟩ := _root_.AbcTwoNinths.Terminal.integerMinorNonzeroAndValuation y a (fun i ↦ hunit _ (hmem i)) hnz
  exact ⟨selected, hmem, hnz, hnum, hval⟩

end

end AbcTwoNinths.Terminal
