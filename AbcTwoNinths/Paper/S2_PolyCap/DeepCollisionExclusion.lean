/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SignedBasisUnits
public import AbcTwoNinths.Paper.S2_PolyCap.CollisionThresholdInequalities
public import AbcTwoNinths.Paper.S2_PolyCap.TwoLogarithmCollisionExclusion

/-!
# Deep Collision Exclusion

Two independent residue-kernel vectors cannot be arbitrarily close to a common line when the first
monomial has sufficient valuation depth and bounded height. This supports Proposition 2.1 of the
paper.

## Main results
* Deep collision exclusion at the polynomial-cap threshold.
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
The height and local depth bounds exclude an independent residue-kernel vector within the weighted collision threshold. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem noCollisionAtW5BThreshold
    {ι : Type*} [Fintype ι] {p r : ℕ} {H : ℝ}
    (hp : p.Prime) (ho : 2 < p) (hr : 1 ≤ r) (hH : 2 < H)
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (haway : ∀ j, ¬ p ∣ q j)
    (e v : ι → ℤ) (lam : ℝ)
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hv : v ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ))
    (hne : _root_.AbcTwoNinths.PolyCap.prodMonomial q e ≠ 1)
    (hh : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) ≤ 4 * H)
    (hdepth : H / (4 * (r : ℝ)) ≤
      (padicValRat p (_root_.AbcTwoNinths.PolyCap.prodMonomial q e - 1) : ℝ) * log (p : ℝ))
    (hclose : ∑ j, |(v j : ℝ) - lam * (e j : ℝ)| * log (q j : ℝ) <
      1 / (1920000 * (r : ℝ) * (1 + log (20 * H)) ^ 2)) : False := by
  have he0 : e ≠ 0 := fun h =>
    hne ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff q hq hinj e).2 (by simp [h]))
  obtain ⟨i, j, hij⟩ := _root_.AbcTwoNinths.PolyCap.existsNonzeroMinorOfInd he0 hind
  have hi := _root_.AbcTwoNinths.PolyCap.planeMapInjectiveOfMinor hij
  obtain ⟨u, m, hu, hd, huMin, hmMin⟩ := _root_.AbcTwoNinths.PolyCap.existsUnimodularMinima q hq he0 hind
  have hd0 : _root_.AbcTwoNinths.PolyCap.det2 u m ≠ 0 := by intro h; simp [h] at hd
  have hm : m ≠ 0 := by intro h; subst m; simp [_root_.AbcTwoNinths.PolyCap.det2] at hd0
  have hp0 : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have floor (z : ℤ × ℤ) (hz : z ≠ 0) :
      log (p : ℝ) < _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair z) := by
    have hk : _root_.AbcTwoNinths.PolyCap.planeMap e v z ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker := by
      change z.1 • e + z.2 • v ∈ _
      exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ he _) (AddSubgroup.zsmul_mem _ hv _)
    have hz0 : _root_.AbcTwoNinths.PolyCap.planeMap e v 0 = 0 := by
      funext j
      change 0 * e j + 0 * v j = 0
      ring
    have hn : _root_.AbcTwoNinths.PolyCap.planeMap e v z ≠ 0 := fun h => hz (hi (h.trans hz0.symm))
    change log (p : ℝ) < _root_.AbcTwoNinths.PolyCap.planeHeight q e v ((z.1 : ℝ), (z.2 : ℝ))
    rw [← _root_.AbcTwoNinths.PolyCap.planeHeightEqRatHeight q hq hinj e v z]
    exact _root_.AbcTwoNinths.PolyCap.logLtRatHeightOfMemKer hp q hq hinj haway hk hn
  have hsource : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) = _root_.AbcTwoNinths.PolyCap.planeHeight q e v (1, 0) := by
    have h : _root_.AbcTwoNinths.PolyCap.planeMap e v (1, 0) = e := by
      funext j
      change 1 * e j + 0 * v j = e j
      ring
    simpa [h, _root_.AbcTwoNinths.PolyCap.realPair] using _root_.AbcTwoNinths.PolyCap.planeHeightEqRatHeight q hq hinj e v (1, 0)
  have hh0 : 0 < _root_.AbcTwoNinths.PolyCap.planeHeight q e v (1, 0) :=
    hsource ▸ hp0.trans (_root_.AbcTwoNinths.PolyCap.logLtRatHeightOfMemKer hp q hq hinj haway he he0)
  have hwidth := (_root_.AbcTwoNinths.PolyCap.heightLeCollisionWidth q hq e v lam).trans_lt hclose
  obtain ⟨hc₁, hc₂, hprod, hline₁, hline₂⟩ :=
    _root_.AbcTwoNinths.PolyCap.cramerProductAndLines q e v hd hmMin (huMin _ hm) hh0 hwidth
  let c₁ := _root_.AbcTwoNinths.PolyCap.cramerA u m (1, 0)
  let c₂ := _root_.AbcTwoNinths.PolyCap.cramerB u m (1, 0)
  let s : ℤ := if 0 ≤ c₁ then 1 else -1
  let t : ℤ := -(if 0 ≤ c₂ then 1 else -1)
  have hs : |s| = 1 := by dsimp [s]; split_ifs <;> decide
  have ht : |t| = 1 := by dsimp [t]; split_ifs <;> decide
  have hsn : (c₁.natAbs : ℤ) * s = c₁ := by dsimp [s]; split_ifs <;> omega
  have htn : (c₂.natAbs : ℤ) * t = -c₂ := by dsimp [t]; split_ifs <;> omega
  obtain ⟨ha, hra⟩ := _root_.AbcTwoNinths.PolyCap.signedBasisUnit hp q hq hinj haway he hv u s hs
  obtain ⟨hb, hrb⟩ := _root_.AbcTwoNinths.PolyCap.signedBasisUnit hp q hq hinj haway he hv m t ht
  have hab := _root_.AbcTwoNinths.PolyCap.signedBasisIndependent q hq hinj hi hd0
    (show s ≠ 0 by intro h; simp [h] at hs) (show t ≠ 0 by intro h; simp [h] at ht)
  obtain ⟨hsrc₁, hsrc₂⟩ := _root_.AbcTwoNinths.PolyCap.cramerCoordinates hd (1, 0)
  have hval := _root_.AbcTwoNinths.PolyCap.differenceDepthOfQuotient hp hb hne
    (_root_.AbcTwoNinths.PolyCap.signedMonomialQuotient q hq e v u m hsn htn hsrc₁ hsrc₂)
  obtain ⟨hHp, hwp, hY, hT, hcoeff, hproduct⟩ :=
    _root_.AbcTwoNinths.PolyCap.numericPremisesForContradiction ho hr hH hh0 (hsource ▸ hh) (floor u hu) (floor m hm) hc₁ hc₂ hprod
  refine _root_.AbcTwoNinths.PolyCap.oddPrimeB1OfCoordinates hp ho ha hb hab (_root_.AbcTwoNinths.PolyCap.cramerUnitDet hd)
    hh0 (floor u hu) (floor m hm) hT hprod hline₁ hline₂
    (max_le hra.le (floor u hu).le) (max_le hrb.le (floor m hm).le)
    hHp hwp hY ?_ hcoeff hproduct
  rw [hval, show (2 : ℝ) * (2 * (r : ℝ)) = 4 * (r : ℝ) by ring]
  exact hdepth

end

end AbcTwoNinths.PolyCap
