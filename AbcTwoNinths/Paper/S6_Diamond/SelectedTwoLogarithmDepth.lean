/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SelectedPrimeDepth
public import AbcTwoNinths.Paper.S6_Diamond.PrincipalUnitBracket
public import AbcTwoNinths.Paper.S5_Selection.OrderedRadicalData
public import AbcTwoNinths.Paper.S5_Selection.RoofMass
public import AbcTwoNinths.Paper.S2_PolyCap.SideProjection

/-!
# Selected Two Logarithm Depth

The module bounds the selected prime mass and coefficients before applying the two-logarithm depth estimate. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.selectedB1Depth`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond




section

/--
The logarithmically weighted exponent mass of the selected-side ratio of an ordered triple is at most three times its height.
-/
theorem selectedMassLe (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (ho : t.a ≤ t.b) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    (∑ i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d, |(((_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d).toAdd i : ℤ) : ℝ)| *
      Real.log (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d i : ℝ)) ≤ 3 * t.logHeight := by
  intro s
  obtain ⟨hcop, _, _, hdiv⟩ := _root_.AbcTwoNinths.PolyCap.selectedSideProjection t hp ho
  rw [_root_.AbcTwoNinths.Selection.roofMass s.hn s.hd hcop]
  have ha : t.a ≤ t.c := by rw [← t.add]; omega
  have hb : t.b ≤ t.c := by rw [← t.add]; omega
  have hpos : 0 < t.a * t.b * t.c := by
    exact Nat.mul_pos (Nat.mul_pos t.apos t.bpos) (lt_of_lt_of_le t.apos ha)
  have hnd : s.n * s.d ≤ t.c ^ 3 := by
    apply (Nat.le_of_dvd hpos hdiv).trans
    simpa [pow_succ] using Nat.mul_le_mul_right t.c (Nat.mul_le_mul ha hb)
  have hndR : (s.n : ℝ) * s.d ≤ (t.c : ℝ)^3 := by exact_mod_cast hnd
  have hnR : (0 : ℝ) < s.n := by exact_mod_cast Nat.pos_of_ne_zero s.hn
  have hdR : (0 : ℝ) < s.d := by exact_mod_cast Nat.pos_of_ne_zero s.hd
  simpa [Real.log_pow, _root_.AbcTwoNinths.Basic.Triple.logHeight] using Real.log_le_log (mul_pos hnR hdR) hndR

/--
The selected side admits a kernel lift whose independent two-generator representations satisfy the valuation bound under the height and coefficient hypotheses. This is used in Section 6 of the paper.
-/
theorem selectedB1Depth (t : _root_.AbcTwoNinths.Basic.Triple) {η : ℚ} {σ κ : ℝ} {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (hp5 : 5 ≤ p)
    (he : _root_.AbcTwoNinths.Statement.admissibleEta η) (hs : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hk : _root_.AbcTwoNinths.Statement.admissibleMargin η κ)
    (hcut : t.logHeight * Real.exp (-σ * t.thirdLogRadical) < p) (hh : _root_.AbcTwoNinths.Statement.High η 16 t) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let q := _root_.AbcTwoNinths.ExteriorE2.base s.n s.d
    let hq := _root_.AbcTwoNinths.ExteriorE2.prime s.n s.d
    let r := _root_.AbcTwoNinths.ExteriorE2.residue q hq (_root_.AbcTwoNinths.Selection.avoidOfSide s)
    let γ := _root_.AbcTwoNinths.ExteriorE2.gammaStar r (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
      ∀ (u v : _root_.AbcTwoNinths.ExteriorE2.Kernel r) (c d : ℤ) (B₁ B₂ : ℝ),
      Function.Injective (fun z : ℤ × ℤ => fun i =>
        z.1 * u.val.toAdd i + z.2 * v.val.toAdd i) →
      c ≠ 0 → d ≠ 0 → w = u ^ c * v ^ d →
      max (_root_.AbcTwoNinths.Basic.rationalHeight (γ u : ℚ)) (Real.log p) ≤ B₁ →
      max (_root_.AbcTwoNinths.Basic.rationalHeight (γ v : ℚ)) (Real.log p) ≤ B₂ →
      ((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) * Real.log p ≤ 32 * t.logHeight / t.thirdLogRadical →
      (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * (Real.log p)^2 ≤
        9408 * B₁ * B₂ := by
  intro s q hq r γ
  obtain ⟨w, hw, _, hdepth⟩ := _root_.AbcTwoNinths.Selection.selectedNative t hp
  refine ⟨w, hw, ?_⟩
  intro u v c d B₁ B₂ hi hc hd hrep h₁ h₂ hscale
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlog := Real.log_pos hpR
  have hcap := _root_.AbcTwoNinths.Diamond.smNormalizedBracket t he hs hk Fact.out hcut hh
    (hlog.trans_le ((le_max_right _ _).trans h₁))
    (hlog.trans_le ((le_max_right _ _).trans h₂)) hc hscale
  have h := _root_.AbcTwoNinths.Diamond.b1Bracket q hq (_root_.AbcTwoNinths.Selection.avoidOfSide s) hp5
    (fun _ _ e => Subtype.ext e) u v w hi hc hd hrep h₁ h₂
  dsimp only at h
  rw [hdepth, hcap] at h
  simp only [Int.cast_natCast] at h
  convert h using 1
  ring

end

end AbcTwoNinths.Diamond
