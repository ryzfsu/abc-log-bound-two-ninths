/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.DiamondPacket
public import AbcTwoNinths.Paper.S7_Terminal.BandExclusion

/-!
# Selected Diamond Exclusion

The determinant contradiction excludes sufficiently large ordered triples in the selected band.
This is Lemma 7.3 of the paper.

## Main results
* `AbcTwoNinths.Terminal.bandEngineOfSelectedDiamond`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

/-- Lemma 7.3 of the paper. This is used in Section 7 of the paper. -/
theorem bandEngineOfSelectedDiamond (produce : _root_.AbcTwoNinths.Terminal.SelectedDiamondProvider) :
    _root_.AbcTwoNinths.Terminal.BandEngine := by
  intro η hη σ κ hσ hκ
  obtain ⟨X, _, select⟩ := produce η hη σ κ hσ hκ
  refine ⟨X, ?_⟩
  intro t hord hhigh h₁ h₂
  obtain ⟨p, _, _, hp, ⟨packet⟩⟩ := select t hord hhigh h₁ h₂
  let _ : Fact p.Prime := ⟨hp⟩
  exact packet.conflict

end AbcTwoNinths.Terminal
