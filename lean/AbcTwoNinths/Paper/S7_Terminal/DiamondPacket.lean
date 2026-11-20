/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.IntegralDeterminantBounds
public import AbcTwoNinths.Paper.S7_Terminal.BandExclusion
public import AbcTwoNinths.Paper.S5_Selection.Selected

/-!
# Diamond Packet

The selected diamond data give a contradiction by comparing p-adic depth with the sum of the
interpolation row heights in Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.DiamondPacket.conflict`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section





/--
Admissible determinant data at a prime and depth include the strict height budget of Section 7.
-/
structure DiamondPacket (p m : ℕ) [Fact p.Prime] where
  K : ℕ
  K_pos : 0 < K
  depth : 4 * K ≤ 3 * m
  γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter
  principal : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s)
  axial : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1)
  shift : _root_.AbcTwoNinths.Terminal.Site
  shift_nontrivial : _root_.AbcTwoNinths.Terminal.value γ shift ≠ 1
  sites : Finset _root_.AbcTwoNinths.Terminal.Site
  count : 2 * K - 1 ≤ sites.card
  labels : Function.Injective (fun s : sites => s.val.2)
  U : ℝ
  B : ℝ
  B_pos : 0 < B
  choose_bound : ∀ s ∈ sites ∪ sites.image (fun s => s + shift), ∀ k : Fin K,
    |((Ring.choose s.2 k.val : ℤ) : ℝ)| ≤ B
  height_bound : ∀ sel : _root_.AbcTwoNinths.Terminal.Row K ↪ _root_.AbcTwoNinths.Terminal.Site,
    (∀ i, sel i ∈ sites ∪ sites.image (fun s => s + shift)) →
    (∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ (sel i)) : ℝ)) ≤ U
  budget : U + Real.log ((2*K).factorial : ℝ) + (2*K : ℝ) * Real.log B <
    (2/9 : ℝ) * (2*K : ℝ)^2 * Real.log (p : ℝ)

/--
The local lower bound and archimedean upper bound contradict the packet's strict height budget. This is used in Section 7 of the paper.
-/
theorem DiamondPacket.conflict {p m : ℕ} [Fact p.Prime] (packet : _root_.AbcTwoNinths.Terminal.DiamondPacket p m) :
    False := by
  obtain ⟨_, _, _, upper, lower⟩ := _root_.AbcTwoNinths.Terminal.terminalBounds packet.K_pos
    packet.γ packet.principal packet.axial packet.shift packet.shift_nontrivial
    packet.sites packet.count packet.labels packet.B_pos packet.choose_bound packet.height_bound
  exact (not_lt_of_ge ((lower packet.depth).trans upper)) packet.budget

/--
Beyond a common threshold every triple in the ordered band has admissible determinant data at a prime above the cutoff. This is used in Section 7 of the paper.
-/
def SelectedDiamondProvider : Prop :=
  ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
    ∀ σ κ : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ → _root_.AbcTwoNinths.Statement.admissibleMargin η κ →
      ∃ X : ℝ, 0 ≤ X ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b →
        _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t →
        ∃ p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
          t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (p : ℝ) ∧
          ∃ hp : p.Prime,
            Nonempty (@_root_.AbcTwoNinths.Terminal.DiamondPacket p
              (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t))) ⟨hp⟩)

end

end AbcTwoNinths.Terminal
