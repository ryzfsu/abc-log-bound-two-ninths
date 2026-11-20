/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.Join
public import AbcTwoNinths.Paper.S4_ExteriorE2.Products
public import AbcTwoNinths.Paper.S2_PolyCap.SideData
public import AbcTwoNinths.Paper.S5_Selection.SelectedDepth

/-!
# Ordered Radical Data

Shows that the selected prime is coprime to the two complementary sides and identifies the
signed-kernel vector of their ratio. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.selectedNative`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section

/-- The chosen prime is absent from the numerator and denominator prime support. -/
theorem avoidOfSide {t : _root_.AbcTwoNinths.Basic.Triple} {p : ℕ} (s : _root_.AbcTwoNinths.PolyCap.SideData t p)
    (i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d) : p ≠ _root_.AbcTwoNinths.ExteriorE2.base s.n s.d i := by
  intro he
  change p = i.val at he
  rcases Finset.mem_union.mp i.property with h | h
  · apply s.avoidN
    exact (congrArg (fun k : ℕ => k ∣ s.n) he).mpr (Nat.dvd_of_mem_primeFactors h)
  · apply s.avoidD
    exact (congrArg (fun k : ℕ => k ∣ s.d) he).mpr (Nat.dvd_of_mem_primeFactors h)

/-- The selected exponent vector gives a kernel element whose rational character is the
selected source and whose character minus one has the valuation of the minimum-radical side. -/
theorem selectedNative (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let r := _root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s)
    let m := _root_.AbcTwoNinths.ExteriorE2.monomial (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d)
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
      (_root_.AbcTwoNinths.ExteriorE2.gammaStar r m w : ℚ) = _root_.AbcTwoNinths.Statement.selectedSource t ∧
      padicValRat p ((_root_.AbcTwoNinths.ExteriorE2.gammaStar r m w : ℚ) - 1) =
        (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) := by
  intro s r m
  obtain ⟨w, hv, hw⟩ := _root_.AbcTwoNinths.ExteriorE2.join r m (_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d) s.n s.d s.neg s.dunit
    (_root_.AbcTwoNinths.ExteriorE2.resEval s.hn s.hd (_root_.AbcTwoNinths.Selection.avoidOfSide s)) s.residue (_root_.AbcTwoNinths.ExteriorE2.ratEval s.hn s.hd)
  have hs := hw.trans s.source.symm
  exact ⟨w, hv, hs, by rw [hs]; exact (_root_.AbcTwoNinths.Selection.selectedSourceDepthOfMem t hp).2⟩

end

end AbcTwoNinths.Selection
