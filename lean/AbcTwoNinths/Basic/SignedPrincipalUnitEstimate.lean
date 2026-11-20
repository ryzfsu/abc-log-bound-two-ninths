/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.UnboundedTwoLogarithmEstimate

/-!
# Signed Principal Unit Estimate

The module extends local estimates on squared principal units to signed powers of rational units.

## Main results
* `AbcTwoNinths.Basic.bound`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

variable {p : ℕ} [Fact p.Prime]

/-- A rational is principal at p if its p-adic distance from one is less than one. -/
def Principal (p : ℕ) [Fact p.Prime] (u : ℚ) : Prop := ‖(u : ℚ_[p]) - 1‖ < 1

private theorem primeReal : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem normOne {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) : ‖(u : ℚ_[p])‖ = 1 :=
  by simpa using (Padic.norm_eq_of_norm_sub_lt_right (z1 := (u : ℚ_[p])) (z2 := 1)
    (by simpa [_root_.AbcTwoNinths.Basic.Principal] using hu))

private theorem principalNeZero {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) : u ≠ 0 := by
  intro hz
  simp [_root_.AbcTwoNinths.Basic.Principal, hz] at hu

private theorem ratValZero {u : ℚ} (hu : ‖(u : ℚ_[p])‖ = 1) :
    padicValRat p u = 0 := by
  have hn : (u : ℚ_[p]) ≠ 0 := by intro hz; simp [hz] at hu
  rw [Padic.norm_eq_zpow_neg_valuation hn, Padic.valuation_ratCast, ← zpow_zero (p : ℝ)] at hu
  have hv := (zpow_right_strictMono₀ (primeReal (p := p))).injective hu
  omega

private theorem principalMul {u v : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) (hv : _root_.AbcTwoNinths.Basic.Principal p v) :
    _root_.AbcTwoNinths.Basic.Principal p (u * v) := by
  unfold _root_.AbcTwoNinths.Basic.Principal at *
  rw [Rat.cast_mul, show (u : ℚ_[p]) * v - 1 = (u - 1) + u * (v - 1) by ring]
  apply (Padic.nonarchimedean _ _).trans_lt
  rw [norm_mul, normOne hu, one_mul]
  exact max_lt hu hv

/-- The inverse of a principal rational is principal at the same prime. -/
theorem principalInv {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) : _root_.AbcTwoNinths.Basic.Principal p u⁻¹ := by
  have hn : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast principalNeZero hu
  unfold _root_.AbcTwoNinths.Basic.Principal at *
  rw [Rat.cast_inv, show (u : ℚ_[p])⁻¹ - 1 = -((u : ℚ_[p]) - 1) / u by field_simp; ring,
    norm_div, norm_neg, normOne hu, div_one]
  exact hu

private theorem signedPrincipalPow {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) (n : ℕ) : _root_.AbcTwoNinths.Basic.Principal p (u ^ n) := by
  induction n with
  | zero => simp [_root_.AbcTwoNinths.Basic.Principal]
  | succ n ih => simpa only [pow_succ] using principalMul ih hu

private theorem toSquare {u : ℚ} (hu : _root_.AbcTwoNinths.Basic.Principal p u) : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p (u ^ 2) := by
  have hq := signedPrincipalPow hu 2
  refine ⟨sq_pos_of_ne_zero (principalNeZero hu), principalNeZero hq,
    ratValZero (normOne hq), ?_⟩
  by_cases he : u ^ 2 = 1
  · exact Or.inl he
  right
  have hn : (((u ^ 2 - 1 : ℚ) : ℚ_[p])) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr he
  have h : ‖(((u ^ 2 - 1 : ℚ) : ℚ_[p]))‖ < 1 := by simpa [_root_.AbcTwoNinths.Basic.Principal] using hq
  rw [Padic.norm_eq_zpow_neg_valuation hn, Padic.valuation_ratCast, ← zpow_zero (p : ℝ)] at h
  have hv := (zpow_right_strictMono₀ (primeReal (p := p))).lt_iff_lt.mp h
  omega

private theorem independentSq {u v : ℚ} (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent u v) :
    _root_.AbcTwoNinths.Basic.RatMulIndependent (u ^ 2) (v ^ 2) := by
  intro i j h
  have h' : u ^ (2 * i) * v ^ (2 * j) = 1 := by
    simpa only [zpow_mul, zpow_ofNat] using h
  obtain ⟨hi', hj'⟩ := hi _ _ h'
  exact ⟨by omega, by omega⟩

/-- Inverting a nonzero rational preserves its logarithmic height. -/
theorem heightInv {u : ℚ} (hu : u ≠ 0) : _root_.AbcTwoNinths.Basic.rationalHeight u⁻¹ = _root_.AbcTwoNinths.Basic.rationalHeight u := by
  have hnum : u.num ≠ 0 := by simpa using hu
  have hs : u.num.sign.natAbs = 1 := by
    rcases lt_or_gt_of_ne hnum with hn | hp
    · rw [Int.sign_eq_neg_one_of_neg hn]; decide
    · rw [Int.sign_eq_one_of_pos hp]; decide
  rw [_root_.AbcTwoNinths.Basic.rationalHeight, Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast, Rat.den_inv_of_ne_zero hu]
  simp [hs, _root_.AbcTwoNinths.Basic.rationalHeight, max_comm]

private theorem heightSq (u : ℚ) : _root_.AbcTwoNinths.Basic.rationalHeight (u ^ 2) = 2 * _root_.AbcTwoNinths.Basic.rationalHeight u := by
  unfold _root_.AbcTwoNinths.Basic.rationalHeight
  rw [Rat.num_pow, Rat.den_pow, Int.natAbs_pow]
  have hmax : max (u.num.natAbs ^ 2) (u.den ^ 2) = max u.num.natAbs u.den ^ 2 := by
    rcases le_total u.num.natAbs u.den with h | h
    · rw [max_eq_right h, max_eq_right (Nat.pow_le_pow_left h 2)]
    · rw [max_eq_left h, max_eq_left (Nat.pow_le_pow_left h 2)]
  rw [hmax, Nat.cast_pow, log_pow]
  norm_num

private theorem squareContact (hp : 5 ≤ p) {u v : ℚ}
    (hu : _root_.AbcTwoNinths.Basic.Principal p u) (hv : _root_.AbcTwoNinths.Basic.Principal p v) (r s : ℕ) :
    padicValRat p ((u ^ 2) ^ r - (v ^ 2) ^ s) = padicValRat p (u ^ r / v ^ s - 1) := by
  let a := u ^ r
  let b := v ^ s
  have hb := signedPrincipalPow hv s
  have ha := signedPrincipalPow hu r
  have hb0 := principalNeZero hb
  have hs : ‖((a + b : ℚ) : ℚ_[p])‖ = 1 := by
    have htwo : ‖(2 : ℚ_[p])‖ = 1 := by
      change ‖((2 : ℕ) : ℚ_[p])‖ = 1
      apply Padic.norm_natCast_eq_one_iff.mpr
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        fun h => by have := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) h; omega)
    refine (Padic.norm_eq_of_norm_sub_lt_right (z2 := 2) ?_).trans htwo
    rw [htwo, Rat.cast_add, show (a : ℚ_[p]) + b - 2 = (a - 1) + (b - 1) by ring]
    exact (Padic.nonarchimedean _ _).trans_lt (max_lt ha hb)
  have hs0 : a + b ≠ 0 := by intro hz; simp [hz] at hs
  have hsq : (u ^ 2) ^ r - (v ^ 2) ^ s = (a - b) * (a + b) := by
    dsimp [a, b]
    rw [← pow_mul, ← pow_mul, mul_comm 2 r, mul_comm 2 s, pow_mul, pow_mul]
    ring
  have hratio : a / b - 1 = (a - b) / b := by rw [sub_div, div_self hb0]
  change padicValRat p ((u ^ 2) ^ r - (v ^ 2) ^ s) = padicValRat p (a / b - 1)
  rw [hsq, hratio]
  by_cases h : a - b = 0
  · simp [h]
  rw [padicValRat.mul h hs0, padicValRat.div h hb0, ratValZero hs, ratValZero (normOne hb),
    add_zero, sub_zero]

/--
For p at least five, squaring two independent signed principal units gives the valuation bound with height factor 588.
-/
theorem bound (hp : 5 ≤ p) {u v : ℚ} {r s : ℕ} {B₁ B₂ : ℝ}
    (hu : _root_.AbcTwoNinths.Basic.Principal p u) (hv : _root_.AbcTwoNinths.Basic.Principal p v) (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent u v)
    (hr : 0 < r) (hs : 0 < s)
    (h₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight u) (log (p : ℝ)) ≤ B₁)
    (h₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight v) (log (p : ℝ)) ≤ B₂) :
    let ell := log (p : ℝ)
    let b := (r : ℝ) / B₂ + (s : ℝ) / B₁
    (padicValRat p (u ^ r / v ^ s - 1) : ℝ) * ell ^ 2 ≤
      588 * B₁ * B₂ * (max 4 (log (exp 2 * ell * (b / 2)) / ell)) ^ 2 := by
  dsimp only
  have he : 0 < log (p : ℝ) := log_pos primeReal
  have hh (z : ℚ) (B : ℝ) (h : max (_root_.AbcTwoNinths.Basic.rationalHeight z) (log (p : ℝ)) ≤ B) :
      max (_root_.AbcTwoNinths.Basic.rationalHeight (z ^ 2)) (log (p : ℝ)) ≤ 2 * B := by
    rw [heightSq]
    exact max_le (by linarith [(le_max_left (_root_.AbcTwoNinths.Basic.rationalHeight z) (log (p : ℝ))).trans h])
      (by linarith [(le_max_right (_root_.AbcTwoNinths.Basic.rationalHeight z) (log (p : ℝ))).trans h])
  have h := _root_.AbcTwoNinths.Basic.twoLogUnbounded147 p (u ^ 2) (v ^ 2) r s (2 * B₁) (2 * B₂)
    Fact.out (by omega) (toSquare hu) (toSquare hv) (independentSq hi) hr hs
    (hh _ _ h₁) (hh _ _ h₂)
  rw [squareContact hp hu hv r s,
    show (r : ℝ) / (2 * B₂) + (s : ℝ) / (2 * B₁) =
      ((r : ℝ) / B₂ + (s : ℝ) / B₁) / 2 by simp only [div_mul_eq_div_div, add_div]; ring,
    show (147 : ℝ) * (2 * B₁) * (2 * B₂) = 588 * B₁ * B₂ by ring] at h
  exact h

end

end AbcTwoNinths.Basic
