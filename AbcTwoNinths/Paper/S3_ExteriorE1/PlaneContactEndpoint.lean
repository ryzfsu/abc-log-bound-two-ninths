/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ActualPlaneContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.OrientedContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.OrderedRealContact

/-!
# Plane Contact Endpoint

The variable-radius real-logarithm estimate supplies a common threshold above which the slab
hypothesis implies the exterior real-contact bound. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.e1OfVariableRadius`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
Explicit threshold in the logarithmic radical scale for the real exterior estimate with parameters eta and kappa. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def bridgeOnset (η : ℚ) (κ : ℝ) : ℝ :=
  let h := _root_.AbcTwoNinths.Statement.highRate η
  let θ := κ / 2
  max (Real.exp 4)
    (max (Real.exp (320000 * 2048 / (θ * h)))
      (max (48 / h)
        (max (320000 * 13824 / (θ * h))
          (max (Real.exp (192 * Real.log (768 / h) / h))
            ((16 / h) * (max 0 (Real.log (9 / κ)) + 2 * Real.log (32 / h)))))))

/--
The variable-radius two-logarithm estimate yields a uniform real exterior bound for ordered high triples. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem e1OfVariableRadius (provider : _root_.AbcTwoNinths.ExteriorE1.variableRadiusRealStatement)
    (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t := by
  refine ⟨_root_.AbcTwoNinths.ExteriorE1.bridgeOnset η κ, (Real.exp_pos _).le.trans (le_max_left _ _), fun t hab hh => ?_⟩
  by_contra hf
  let h := _root_.AbcTwoNinths.Statement.highRate η
  let θ := κ / 2
  let u := Real.log t.logHeight
  have hη' : (η : ℝ) < 1 / 9 := by
    have hc : (η : ℝ) < (((1 : ℚ) / 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hη.2
    simpa using hc
  have hp : 0 < h := by dsimp [h, _root_.AbcTwoNinths.Statement.highRate]; linarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hX := hh.1
  unfold _root_.AbcTwoNinths.ExteriorE1.bridgeOnset at hX
  simp only [max_le_iff] at hX
  obtain ⟨hx, hon, hu₀, hs₀, hon₁, hon₂⟩ := hX
  have hx0 : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le hx
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh.2
  have hHu : Real.exp u = t.logHeight := Real.exp_log hH
  have hlogH : h * t.thirdLogRadical ≤ u := by
    simpa only [u, Real.log_exp] using Real.log_le_log (Real.exp_pos (h * t.thirdLogRadical)) hh.2
  have h48 : 48 ≤ 3 * (h / 3) * t.thirdLogRadical := by
    have hb := (div_le_iff₀ hp).mp hu₀
    nlinarith only [hb]
  have hsmall0 : 320000 * 13824 ≤ θ * (3 * (h / 3) * t.thirdLogRadical) := by
    have hb := (div_le_iff₀ (mul_pos hθ hp)).mp hs₀
    nlinarith only [hb]
  have windows (d : ℝ) (hd : d ≤ t.thirdLogRadical / Real.log t.thirdLogRadical) :=
    _root_.AbcTwoNinths.ExteriorE1.highRadiusWindows (show 0 < h / 3 by positivity) hθ hx0
      (by rw [show 3 * (h / 3) = h by ring]; exact hon)
      (by linarith : 3 * (h / 3) * t.thirdLogRadical ≤ u)
      h48 hsmall0 hd
  obtain ⟨hu, hs, _⟩ := windows (t.thirdLogRadical / Real.log t.thirdLogRadical) le_rfl
  have hpow := Real.pow_div_factorial_le_exp u (by linarith : 0 ≤ u) 2
  norm_num at hpow
  rw [hHu] at hpow
  have hmul : 320000 * 13824 * (u / 2) ≤ θ * t.logHeight := by
    have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ u / 2 by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hpow hθ.le
    nlinarith only [h₁, h₂]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hl2 : Real.log (2 : ℝ) ≤ θ * t.logHeight := by linarith
  have hfail : κ * t.logHeight < Real.log ((t.c : ℝ) / t.a) := lt_of_not_ge hf
  have hcontact := _root_.AbcTwoNinths.ExteriorE1.contactOfOrdered t hab
  have hlt : θ * t.logHeight < -Real.log (Real.log ((t.c : ℝ) / t.b)) := by
    have he : κ = 2 * θ := by dsimp [θ]; ring
    rw [he] at hfail
    nlinarith only [hfail, hcontact.2, hl2]
  have hclose : Real.log ((t.c : ℝ) / t.b) ≤ 1 / t.logHeight := by
    have he : θ * t.logHeight ≥ u := by linarith
    have h := (Real.log_le_iff_le_exp hcontact.1).mp
      (show Real.log (Real.log ((t.c : ℝ) / t.b)) ≤ -u by linarith)
    simpa only [Real.exp_neg, hHu, one_div] using h
  obtain ⟨x, y, a, b, d, ε, hd, hdT, he, hell, hi, hv, hprod, ha, hb, hxlog, hylog⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.actualReducedLogSlab η hη κ hκ t hab hh.2 hf hx hon₁ hon₂ hclose
  obtain ⟨q₁, q₂, c, e, hq₁, hq₂, hqi, hL₁, hL₂, hLp₁, hLp₂, hlo₁, hhi₁, hlo₂, hhi₂,
    hxq, hyq, hc, he', hform⟩ := _root_.AbcTwoNinths.ExteriorE1.orientedBasis t x y a b hi hv
  let ell := -Real.log ε
  have hε : Real.exp (-ell) = ε := by simp [ell, Real.exp_log he]
  have hcp : |(c : ℝ)| = |(a : ℝ)| := by exact_mod_cast hc
  have hep : |(e : ℝ)| = |(b : ℝ)| := by exact_mod_cast he'
  refine _root_.AbcTwoNinths.ExteriorE1.excludeOrientedContact provider hq₁ hq₂ hqi hform.symm hθ hu hs (windows d hdT).2.2
    hell hd hLp₁ hLp₂ ?_ rfl rfl hhi₁ hhi₂ ?_ ?_ hlo₁ hlo₂ ?_ ?_ hcontact.1 ?_
  · rw [hHu, hL₁, hL₂]
    exact hprod.trans (by nlinarith only [mul_nonneg hH.le hd.le])
  · rw [hxq, hL₁, hε]
    exact hxlog
  · rw [hyq, hL₂, hε]
    exact hylog
  · rw [hcp, hL₁, hHu]
    exact ha
  · rw [hep, hL₂, hHu]
    exact hb.trans (by linarith)
  · rwa [hHu]

end

end AbcTwoNinths.ExteriorE1
