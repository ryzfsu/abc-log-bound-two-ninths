/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalDepthReduction

/-!
# Odd Prime Power Lifting

The module bounds the logarithmic power index and derives either adequate local depth or a shallow bound. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.depthOrShallow`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The valuation of a positive index times the logarithm of the prime is at most the logarithm of the index.
-/
theorem logIndexBound {p k : ℕ} [Fact p.Prime] (hk : 0 < k) :
    (padicValNat p k : ℝ) * Real.log p ≤ Real.log k := by
  have hp : p.Prime := Fact.out
  have hle := Nat.le_of_dvd hk (pow_padicValNat_dvd (p := p) (n := k))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log (pow_pos hpR _)
    (by exact_mod_cast hle : (p : ℝ) ^ padicValNat p k ≤ k)
  rwa [Real.log_pow] at hlog

/-- If H/(4r) is at most log(6H) for positive H and r, then H is at most 192 times r squared. -/
theorem shallowOfLogIndex {H r : ℝ} (hH : 0 < H) (hr : 0 < r)
    (hs : H / (4 * r) ≤ Real.log (6 * H)) : H ≤ 192 * r ^ 2 := by
  let y := H / (4 * r)
  have hy : 0 < y := by dsimp [y]; positivity
  have hHy : H = 4 * r * y := by dsimp [y]; field_simp
  have hlogy : Real.log y ≤ y / 2 := by
    have ha := Real.log_le_sub_one_of_pos (show 0 < y / 2 by positivity)
    rw [Real.log_div hy.ne' (by norm_num)] at ha
    have hb := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hc : 0 < 24 * r := by positivity
  change y ≤ Real.log (6 * H) at hs
  rw [show 6 * H = (24 * r) * y by linarith [hHy], Real.log_mul hc.ne' hy.ne'] at hs
  have hd := Real.log_le_sub_one_of_pos hc
  have he : y ≤ 48 * r := by linarith
  have hf := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * r by positivity)
  nlinarith

/--
A deep positive power of a principal unit at an odd prime gives either a quadratic height bound or a depth bound for the unit itself. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem depthOrShallow {p k : ℕ} [Fact p.Prime] (hop : Odd p) (hk : 0 < k)
    {w : ℚ} (hw : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p w) (hne : w ^ k ≠ 1)
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (hkH : (k : ℝ) ≤ 6 * H)
    (hdepth : H / (2 * r) ≤ (padicValRat p (w ^ k - 1) : ℝ) * Real.log p) :
    H ≤ 192 * r ^ 2 ∨ H / (4 * r) ≤ (padicValRat p (w - 1) : ℝ) * Real.log p := by
  have h1 : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p 1 :=
    ⟨one_ne_zero, padicValRat.one, Or.inl rfl⟩
  have hlte := _root_.AbcTwoNinths.Basic.ltePair hop hk hw h1
    (by simpa only [one_pow] using hne)
  rw [one_pow] at hlte
  have he := (_root_.AbcTwoNinths.PolyCap.logIndexBound (p := p) hk).trans
    (Real.log_le_log (by exact_mod_cast hk) hkH)
  by_cases hs : H / (4 * r) ≤ Real.log (6 * H)
  · exact Or.inl (_root_.AbcTwoNinths.PolyCap.shallowOfLogIndex hH hr hs)
  right
  rw [hlte, Int.cast_add, Int.cast_natCast, add_mul] at hdepth
  rw [show H / (2 * r) = 2 * (H / (4 * r)) by field_simp; ring] at hdepth
  linarith

end

end AbcTwoNinths.PolyCap
