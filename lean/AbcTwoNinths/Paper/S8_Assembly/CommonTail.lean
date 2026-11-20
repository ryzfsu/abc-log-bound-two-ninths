/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.BandExclusion
public import AbcTwoNinths.Paper.S1_Statement.RadicalScaleAndTail

/-!
# Common Tail

The exterior estimates and the band exclusion give one threshold beyond which the high-height
inequality is impossible. This is Proposition 8.1 of the paper.

## Main results
* `AbcTwoNinths.Assembly.commonTailOf`
-/

@[expose] public section

namespace AbcTwoNinths.Assembly

section

/-- Proposition 8.1 of the paper. This is used in Section 8 of the paper. -/
theorem commonTailOf (ext : _root_.AbcTwoNinths.Statement.FixedMarginExterior) (eng : _root_.AbcTwoNinths.Terminal.BandEngine) :
    _root_.AbcTwoNinths.Statement.CommonTailExclusion := by
  intro η hη hηtop
  have hadm : _root_.AbcTwoNinths.Statement.admissibleEta η := ⟨hη, hηtop⟩
  obtain ⟨σ, κ, Xe, hσ, hκ, hXe, he⟩ := ext η hadm
  obtain ⟨Xb, hb⟩ := eng η hadm σ κ hσ hκ
  refine ⟨max Xe Xb, ?_⟩
  have ordered (t : _root_.AbcTwoNinths.Basic.Triple) (ho : t.a ≤ t.b)
      (hx : max Xe Xb ≤ t.thirdLogRadical) (hH : Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) ≤ t.logHeight) :
      False := by
    obtain ⟨h1, h2⟩ := he t ho ⟨(le_max_left Xe Xb).trans hx, hH⟩
    exact hb t ho ⟨(le_max_right Xe Xb).trans hx, hH⟩ h1 h2
  intro a b c ht hx hH
  by_cases hab : a ≤ b
  · let t : _root_.AbcTwoNinths.Basic.Triple := ⟨a, b, c, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    exact ordered t hab hx hH
  · let t : _root_.AbcTwoNinths.Basic.Triple :=
      ⟨b, a, c, ht.2.1, ht.1, (Nat.add_comm b a).trans ht.2.2.1, ht.2.2.2.symm⟩
    have hscale : _root_.AbcTwoNinths.Statement.radicalScale b a c = _root_.AbcTwoNinths.Statement.radicalScale a b c := by
      unfold _root_.AbcTwoNinths.Statement.radicalScale
      rw [Nat.mul_comm b a]
    have htx : t.thirdLogRadical = _root_.AbcTwoNinths.Statement.radicalScale a b c := hscale
    apply ordered t (le_of_lt (lt_of_not_ge hab))
    · rwa [htx]
    · rwa [htx]

end

end AbcTwoNinths.Assembly
