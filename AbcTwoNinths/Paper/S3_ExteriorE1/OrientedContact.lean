/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SameSign
public import AbcTwoNinths.Paper.S3_ExteriorE1.OppositeSignContact

/-!
# Oriented Contact

The module excludes contact for a pair of monomials in oriented exponent coordinates. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.excludeOrientedContact`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
A positive integer linear form in the two logarithms cannot have contact depth greater
than `θ * exp u` under the stated radius, height, and slab bounds.
-/
theorem excludeOrientedContact (provider : _root_.AbcTwoNinths.ExteriorE1.variableRadiusRealStatement)
    {q₁ q₂ : ℚ} {c d : ℤ} {L K u θ ell t contact : ℝ}
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂) (hind : _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent q₁ q₂)
    (hform : contact = (c : ℝ) * Real.log (q₁ : ℝ) + (d : ℝ) * Real.log (q₂ : ℝ))
    (hθ : 0 < θ) (hu : 48 ≤ u) (hsmall : 320000 * 13824 ≤ θ * u)
    (hlarge : 320000 * 2048 * t ≤ θ * u) (hell : u / 2 ≤ ell) (ht : 0 < t)
    (hL : 1 / 2 ≤ L) (hK : 1 / 2 ≤ K) (hmass : L * K ≤ 5 * Real.exp u * t)
    (hH₁ : _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₁ = L) (hH₂ : _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₂ = K)
    (hS₁ : Real.log (q₁ : ℝ) ≤ L) (hS₂ : Real.log (q₂ : ℝ) ≤ K)
    (hslab₁ : Real.log (q₁ : ℝ) ≤ 7 * L * Real.exp (-ell) / t)
    (hslab₂ : Real.log (q₂ : ℝ) ≤ 7 * K * Real.exp (-ell) / t)
    (hsep₁ : Real.exp (-L) ≤ Real.log (q₁ : ℝ))
    (hsep₂ : Real.exp (-K) ≤ Real.log (q₂ : ℝ))
    (hc₁ : |(c : ℝ)| * L ≤ 3 * Real.exp u)
    (hc₂ : |(d : ℝ)| * K ≤ 3 * Real.exp u)
    (hpos : 0 < contact) (hcontact : θ * Real.exp u < -Real.log contact) : False := by
  have hcs : contact < Real.exp (-(θ * Real.exp u)) := by
    apply (Real.log_lt_iff_lt_exp hpos).mp
    linarith
  have hsign := _root_.AbcTwoNinths.ExteriorE1.oppositeContactSigns (Real.exp_pos u) hu ht hL hK hell
    (Real.exp_pos (-ell)) (by rw [Real.log_exp, neg_neg]) hmass hsep₁ hsep₂
    hslab₁ hslab₂ hlarge (fun h => by
      have hp := _root_.AbcTwoNinths.ExteriorE1.tinyRadiusWindow (by linarith : 0 < u) hell hsmall h
      have hf : 10 ≤ 320000 * (6 * u)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hf ht.le]) hpos hcs hform
  rcases hsign with ⟨hc, hd⟩ | ⟨hd, hc⟩
  · have hx : ((-c).toNat : ℝ) = -(c : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr hc.le)
    have hy : (d.toNat : ℝ) = (d : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hd.le
    apply _root_.AbcTwoNinths.ExteriorE1.excludeOpposite provider q₁ q₂ (-c).toNat d.toNat L K u θ ell t contact
      hq₁ hq₂ hind (by omega) (by omega) ?_ hθ hu hsmall hlarge hell ht hL hK hmass
      hH₁ hH₂ hS₁ hS₂ hslab₁ hslab₂ hsep₁ hsep₂ ?_ ?_ hcontact
    · rw [_root_.AbcTwoNinths.ExteriorE1.twoLogForm, hx, hy, show (d : ℝ) * Real.log (q₂ : ℝ) -
        -(c : ℝ) * Real.log (q₁ : ℝ) = contact by linarith]
      exact abs_of_pos hpos
    · rwa [hx, ← abs_of_neg (show (c : ℝ) < 0 by exact_mod_cast hc)]
    · rwa [hy, ← abs_of_pos (show 0 < (d : ℝ) by exact_mod_cast hd)]
  · have hx : ((-d).toNat : ℝ) = -(d : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr hd.le)
    have hy : (c.toNat : ℝ) = (c : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hc.le
    have hi : _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent q₂ q₁ := by
      intro m n h
      exact And.symm (hind n m (by simpa [mul_comm] using h))
    apply _root_.AbcTwoNinths.ExteriorE1.excludeOpposite provider q₂ q₁ (-d).toNat c.toNat K L u θ ell t contact
      hq₂ hq₁ hi (by omega) (by omega) ?_ hθ hu hsmall hlarge hell ht hK hL
      (by rwa [mul_comm K L]) hH₂ hH₁ hS₂ hS₁ hslab₂ hslab₁ hsep₂ hsep₁ ?_ ?_ hcontact
    · rw [_root_.AbcTwoNinths.ExteriorE1.twoLogForm, hx, hy, show (c : ℝ) * Real.log (q₁ : ℝ) -
        -(d : ℝ) * Real.log (q₂ : ℝ) = contact by linarith]
      exact abs_of_pos hpos
    · rwa [hx, ← abs_of_neg (show (d : ℝ) < 0 by exact_mod_cast hd)]
    · rwa [hy, ← abs_of_pos (show 0 < (c : ℝ) by exact_mod_cast hc)]

end

end AbcTwoNinths.ExteriorE1
