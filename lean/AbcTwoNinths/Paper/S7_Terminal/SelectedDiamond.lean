/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.ShellContradiction
public import AbcTwoNinths.Paper.S6_Diamond.RoundedSupportMass
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPrimeData
public import AbcTwoNinths.Paper.S7_Terminal.OldSupportCharacterHeight
public import AbcTwoNinths.Paper.S7_Terminal.DiamondPacket

/-!
# Selected Diamond

The module combines the plane and determinant estimates to provide the selected diamond data. This is Lemma 7.2 of the paper.

## Main results
* `AbcTwoNinths.Terminal.selectedDiamondProvider`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal





section

-- The elaboration of selected diamond needs a larger budget.
set_option maxHeartbeats 1500000 in
/-- Lemma 7.2 of the paper. This is used in Section 7 of the paper. -/
theorem selectedDiamondProvider : _root_.AbcTwoNinths.Terminal.SelectedDiamondProvider := by
  classical
  intro η hη σ κ hσ hκ
  have ηlt : (η : ℝ) < 1/9 := by simpa using (Rat.cast_lt (K := ℝ)).mpr hη.2
  obtain ⟨Z, L, hZ, _, _, close⟩ := _root_.AbcTwoNinths.Terminal.fineShellConflict hη hκ
  obtain ⟨Y, pair⟩ := _root_.AbcTwoNinths.Diamond.diamondSlopeBounds ηlt (by positivity : 0 ≤ 4/(3*Z))
    (_root_.AbcTwoNinths.Terminal.goodDenominator Z (_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)/2))
  obtain ⟨A, hA, native⟩ := _root_.AbcTwoNinths.Diamond.selectedDeterminantInputs hη hσ hκ
  obtain ⟨G, _, grow⟩ := _root_.AbcTwoNinths.Terminal.selectedAxialGrowth hη hσ L L
  let C := max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))) / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)
  let E := Real.exp (4/_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))
  let X := max (max (max A G) Y) (max (max C E) (Real.exp 15))
  have hX : 0 ≤ X := hA.le.trans (((le_max_left _ _).trans (le_max_left _ _)).trans
    (le_max_left _ _))
  refine ⟨X, hX, ?_⟩
  intro t ord high h1 h2
  have hAY := ((le_max_left (max (max A G) Y) _).trans high.1)
  have hAG := (le_max_left (max A G) Y).trans hAY
  have hCY := (le_max_right (max (max A G) Y) _).trans high.1
  have hCE := (le_max_left (max C E) (Real.exp 15)).trans hCY
  obtain ⟨p, hp, hp5, hc, _, more⟩ :=
    native t ord ⟨(le_max_left A G).trans hAG, high.2⟩ h1 h2
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  let : Fact (2 < p) := ⟨by omega⟩
  obtain ⟨j, ⟨d⟩⟩ := more
  obtain ⟨hℓ, hn⟩ := grow t ⟨(le_max_right A G).trans hAG, high.2⟩ p hp hc
  let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
  let old := _root_.AbcTwoNinths.ExteriorE2.base side.n side.d ∘ _root_.AbcTwoNinths.Diamond.roofFirst j
  let v := d.source
  let z := _root_.AbcTwoNinths.Statement.selectedSource t
  let h := Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax z : ℝ)
  let m := padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t))
  have hH : h ≤ t.logHeight := by
    change _ ≤ Real.log (t.c : ℝ)
    exact Real.log_le_log (by exact_mod_cast _root_.AbcTwoNinths.Terminal.rowHeightMaxPos z)
      (by exact_mod_cast _root_.AbcTwoNinths.Statement.mulHeightSelectedSourceLe t)
  have hm : (m : ℤ) ≤ padicValRat p (z-1) := (_root_.AbcTwoNinths.Selection.selectedSourceDepthOfMem t hp).2.ge
  have hroof : |(v.val.toAdd (.inl ()) : ℝ)| * Real.log 2 ≤ h := by
    have hh := _root_.AbcTwoNinths.Terminal.coordinateLogTwoLeLogRowHeightMaxCharacter
      old d.oldPrime d.oldAvoid d.oldInjective v (.inl ())
    have hz : (_root_.AbcTwoNinths.Diamond.character old d.oldPrime d.oldAvoid v : ℚ) = z := d.sourceCharacter
    rw [hz] at hh
    exact hh
  have hweight := (_root_.AbcTwoNinths.Diamond.nativeDimensionWeight t old d.oldPrime d.oldInjective d.oldDvd d.radicalPos).2
  have hvol := _root_.AbcTwoNinths.Diamond.nativeMassFloor t old d.oldPrime d.oldInjective d.oldDvd d.radicalPos
    ((le_max_right _ (Real.exp 15)).trans hCY)
  obtain ⟨q, hf, ht, hlt, pr, av, u, uf, ut, hs, _, hi, ha, hg⟩ :=
    pair d.contactDvd old d.oldPrime d.oldAvoid d.oldInjective d.oldDvd v
      (H := t.logHeight) (x := t.thirdLogRadical) (B := 3*t.thirdLogRadical) (h := h)
      ((le_max_right _ Y).trans hAY) d.radicalPos d.logRadical d.shell
      ((le_max_left C E).trans hCE) d.roofNonzero d.line d.separation
      (mul_pos (by norm_num) d.shell.hx) hweight d.roofBound hroof hvol
  have hbase := (_root_.AbcTwoNinths.Diamond.freshExtendedBaseValid d.contactDvd old d.oldPrime d.oldAvoid
    d.oldInjective d.oldDvd q hf ht hlt).2.2
  have hab := ha.trans d.sourceCharacter
  exact (close old d.oldPrime d.oldAvoid v q pr av hbase u
    d.shell ((le_max_right C E).trans hCE) hf ht d.roofNonzero uf ut hs hi hab hH
    d.depth hm hℓ hn hg).elim

end

end AbcTwoNinths.Terminal
