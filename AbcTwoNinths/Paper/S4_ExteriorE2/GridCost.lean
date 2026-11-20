/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.BoundedSupportDimension

/-!
# Grid Cost

The module gives an eventual upper bound on the cost of the small-prime residue grid. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.eventualE2GridCost`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

open Filter Asymptotics
open scoped Topology

section

/--
Beyond a common threshold the logarithmic grid cost for every prime support of the triple and every positive scale at most three times x is below the prescribed positive linear budget. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem eventualE2GridCost {θ σ : ℝ} (hσ : 0 < σ) :
    ∃ X : ℝ, ∀ t : _root_.AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical →
      ∀ S : Finset ℕ, S ⊆ (t.a * t.b * t.c).primeFactors →
        ∀ U : ℝ, 0 < U → U ≤ 3 * t.thirdLogRadical →
          Real.log (4 / θ) + Real.log U +
            (S.card : ℝ) * Real.log ((⌈3 * Real.log t.thirdLogRadical⌉₊ + 1 : ℕ) : ℝ) < σ * t.thirdLogRadical := by
  have hlogx : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    hlogx.comp Real.tendsto_log_atTop
  have hconst (c : ℝ) : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcost₁ := (hconst (Real.log (4 / θ) + Real.log 3)).add hlogx
  have hcost₂ := ((hconst (Real.log 5)).comp Real.tendsto_log_atTop).add hloglog
  have hcost := hcost₁.add (tendsto_const_nhds.mul (a := 8) hcost₂)
  have hev := hcost.eventually (gt_mem_nhds
    (show (0 : ℝ) + 0 + 8 * (0 + 0) < σ by simpa using hσ))
  have hsqrt := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hdom : ∀ᶠ x : ℝ in atTop, Real.log x ≤ Real.sqrt x := by
    filter_upwards [hsqrt, eventually_ge_atTop (1 : ℝ)] with x h hx
    simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using h
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨X, hX⟩ := eventually_atTop.1
    (hev.and (hdom.and (hlarge.and (eventually_ge_atTop (2 : ℝ)))))
  refine ⟨X, fun t ht S hS U hU hUhi => ?_⟩
  obtain ⟨hbudget, hs, hlog, hx2⟩ := hX t.thirdLogRadical ht
  have hx : 1 < t.thirdLogRadical := by linarith
  have hxp : 0 < t.thirdLogRadical := by linarith
  have hlogp : 0 < Real.log t.thirdLogRadical := by linarith
  have hdim := _root_.AbcTwoNinths.ExteriorE2.nativeSupportDimension t S hS hx
  have hsx : Real.sqrt t.thirdLogRadical ≤ t.thirdLogRadical / Real.log t.thirdLogRadical := by
    apply (le_div_iff₀ hlogp).2
    have h := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg t.thirdLogRadical)
    simpa [← pow_two, Real.sq_sqrt hxp.le] using h
  have hone : 1 ≤ Real.sqrt t.thirdLogRadical := (Real.le_sqrt (by norm_num) hxp.le).2 (by simpa using hx.le)
  have hdim' : (S.card : ℝ) ≤ 8 * t.thirdLogRadical / Real.log t.thirdLogRadical := by
    linarith [show 6 * t.thirdLogRadical / Real.log t.thirdLogRadical = 6 * (t.thirdLogRadical / Real.log t.thirdLogRadical) by ring,
      show 8 * t.thirdLogRadical / Real.log t.thirdLogRadical = 8 * (t.thirdLogRadical / Real.log t.thirdLogRadical) by ring]
  let Q := ⌈3 * Real.log t.thirdLogRadical⌉₊ + 1
  have hQp : 0 < (Q : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hQ₀ : 0 ≤ Real.log (Q : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hQ : (Q : ℝ) ≤ 5 * Real.log t.thirdLogRadical := by
    dsimp [Q]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * Real.log t.thirdLogRadical)]
  have hQl := Real.log_le_log hQp hQ
  rw [Real.log_mul (by norm_num) hlogp.ne'] at hQl
  have hg := (mul_le_mul_of_nonneg_right hdim' hQ₀).trans
    (mul_le_mul_of_nonneg_left hQl (by positivity))
  have hUl := Real.log_le_log hU hUhi
  rw [Real.log_mul (by norm_num) hxp.ne'] at hUl
  change (Real.log (4 / θ) + Real.log 3) / t.thirdLogRadical + Real.log t.thirdLogRadical / t.thirdLogRadical +
    8 * (Real.log 5 / Real.log t.thirdLogRadical + Real.log (Real.log t.thirdLogRadical) / Real.log t.thirdLogRadical) < σ at hbudget
  have hstrict :
    (Real.log (4 / θ) + Real.log 3 + Real.log t.thirdLogRadical +
      (8 * t.thirdLogRadical / Real.log t.thirdLogRadical) * (Real.log 5 + Real.log (Real.log t.thirdLogRadical))) < σ * t.thirdLogRadical := by
    have hm := mul_lt_mul_of_pos_right hbudget hxp
    convert hm using 1
    field_simp
  change Real.log (4 / θ) + Real.log U + (S.card : ℝ) * Real.log (Q : ℝ) < _
  linarith

end

end AbcTwoNinths.ExteriorE2
