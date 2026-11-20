/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.ResidueKernelPrincipalUnits
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationMonomialHeight

/-!
# Kernel Depth Dichotomy

Dividing the exponent vector by its power index either gives the quadratic bound for `H` or
preserves a lower bound on valuation depth and bounds the resulting monomial height. This supports
Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.kernelDepthOrShallow`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
Either the height parameter is at most 192 times the squared radius or the kernel monomial satisfies the stated depth and height bounds. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem kernelDepthOrShallow {ι : Type*} [Fintype ι] {p k : ℕ} [Fact p.Prime]
    (hop : Odd p) (hk : 0 < k) (q : ι → ℕ) (hq : ∀ i, Nat.Coprime (q i) p)
    (hqpos : ∀ i, 0 < q i) (e w : ι → ℤ)
    (he : k • w = e) (hw : w ∈ (_root_.AbcTwoNinths.Basic.residue q hq).ker)
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (hkH : (k : ℝ) ≤ 6 * H)
    (hne : (∏ i, (q i : ℚ) ^ e i) ≠ 1)
    (hdepth : H / (2 * r) ≤
      (padicValRat p ((∏ i, (q i : ℚ) ^ e i) - 1) : ℝ) * Real.log p)
    (hL : ∑ i, |(w i : ℝ)| * Real.log (q i) ≤ 4 * H) :
    let z := ∏ i, (q i : ℚ) ^ w i
    H ≤ 192 * r ^ 2 ∨
      (H / (4 * r) ≤ (padicValRat p (z - 1) : ℝ) * Real.log p ∧
        H / (4 * r) < _root_.AbcTwoNinths.Basic.padicRationalHeight z ∧ _root_.AbcTwoNinths.Basic.padicRationalHeight z ≤ 4 * H) := by
  let z := ∏ i, (q i : ℚ) ^ w i
  change H ≤ 192 * r ^ 2 ∨ _
  have hz := _root_.AbcTwoNinths.PolyCap.monomialPrincipalOfKernel q hq hqpos w hw
  have hpw : (∏ i, (q i : ℚ) ^ e i) = z ^ k := by
    rw [← he, _root_.AbcTwoNinths.PolyCap.monomialNsmul]
  rw [hpw] at hdepth hne
  have hzne : z ≠ 1 := by
    intro h
    exact hne (by rw [h, one_pow])
  rcases _root_.AbcTwoNinths.PolyCap.depthOrShallow hop hk hz.2 hne hH hr hkH hdepth with hs | hd
  · exact Or.inl hs
  · exact Or.inr ⟨hd, hd.trans_lt (_root_.AbcTwoNinths.PolyCap.depthLtHeight hz.1 hz.2.2.1 hzne),
      (_root_.AbcTwoNinths.PolyCap.monomialHeightLe q w hqpos).trans hL⟩

end

end AbcTwoNinths.PolyCap
