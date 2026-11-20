/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RadiusWindows

/-!
# Radius Choice for Contact Exclusion

An admissible choice of radius in the variable-radius bound excludes a logarithmic contact smaller
than `exp(-θ exp u)` under the slab and height hypotheses. This supports Proposition 3.1 of the
paper.

## Main results
* `AbcTwoNinths.ExteriorE1.excludeContactWithRadius`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Consumer: use a source estimate with the selected radius to exclude a
contact below the window. The source estimate itself is an explicit input. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem excludeContactWithRadius
    {u θ ell t L₁ L₂ S₁ S₂ B contact : ℝ}
    (hθ : 0 < θ) (hu : 48 ≤ u) (hsmall : 320000 * 13824 ≤ θ * u)
    (hlarge : 320000 * 2048 * t ≤ θ * u)
    (hell : u / 2 ≤ ell) (ht : 0 < t)
    (hL₁ : (1 : ℝ) / 2 ≤ L₁) (hL₂ : (1 : ℝ) / 2 ≤ L₂)
    (hmass : L₁ * L₂ ≤ 5 * Real.exp u * t)
    (hS₁ : S₁ ≤ L₁) (hS₂ : S₂ ≤ L₂)
    (hslab₁ : S₁ ≤ 7 * L₁ * Real.exp (-ell) / t)
    (hslab₂ : S₂ ≤ 7 * L₂ * Real.exp (-ell) / t)
    (hsep₁ : Real.exp (-L₁) ≤ S₁) (hsep₂ : Real.exp (-L₂) ≤ S₂)
    (hB : Real.log B ≤ 2 * u)
    (source : ∀ radius : ℝ, 1 ≤ radius →
      max (max L₁ (Real.exp radius * S₁)) radius ≤ 4 * L₁ →
      max (max L₂ (Real.exp radius * S₂)) radius ≤ 4 * L₂ →
      -Real.log contact ≤ 4000 * (4 * L₁) * (4 * L₂) * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 / radius)
    (contactTooSmall : θ * Real.exp u < -Real.log contact) : False := by
  obtain ⟨radius, hradius, hs₁, hs₂, hcost⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.realVariableRadiusParametersOfTinyBound hθ hu
      (_root_.AbcTwoNinths.ExteriorE1.tinyRadiusWindow (by linarith) hell hsmall) hlarge hell ht hL₁ hL₂
      hmass hS₁ hS₂ hslab₁ hslab₂ hsep₁ hsep₂ hB
  exact (not_lt_of_ge ((source radius hradius hs₁ hs₂).trans hcost)) contactTooSmall

end

end AbcTwoNinths.ExteriorE1
