/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.InterpolationGrid

/-!
# Rational Grid Transport

The module transports rational congruences to the entries of an interpolation matrix.

## Main results
* `AbcTwoNinths.Basic.determinantEntryCongruent`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

set_option autoImplicit false

/-- A rational has nonnegative rational p-adic valuation at the specified place. -/
def IntegralAt (p : ℕ) (x : ℚ) : Prop := 0 ≤ padicValRat p x

/-- The product of two rationals integral at a prime is integral there. -/
theorem integralMul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : _root_.AbcTwoNinths.Basic.IntegralAt p x) (hy : _root_.AbcTwoNinths.Basic.IntegralAt p y) : _root_.AbcTwoNinths.Basic.IntegralAt p (x*y) := by
  by_cases h : x = 0
  · simp [_root_.AbcTwoNinths.Basic.IntegralAt, h]
  by_cases h' : y = 0
  · simp [_root_.AbcTwoNinths.Basic.IntegralAt, h']
  unfold _root_.AbcTwoNinths.Basic.IntegralAt at *
  rw [padicValRat.mul h h']
  omega

/-- Every natural power of a rational integral at a prime is integral there. -/
theorem integralPow {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : _root_.AbcTwoNinths.Basic.IntegralAt p x) (n : ℕ) : _root_.AbcTwoNinths.Basic.IntegralAt p (x^n) := by
  unfold _root_.AbcTwoNinths.Basic.IntegralAt at *
  rw [padicValRat.pow]
  positivity

/-- Rational congruences at a fixed prime-power depth are preserved by addition. -/
theorem congrAdd {p e : ℕ} [Fact p.Prime] {a b c d : ℚ}
    (h₁ : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (h₂ : _root_.AbcTwoNinths.Basic.RatCongruent p e c d) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (a+c) (b+d) := by
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact Or.inl rfl
  · exact Or.inr (by convert h₂ using 2; ring)
  · exact Or.inr (by convert h₁ using 2; ring)
  · by_cases h : a+c = b+d
    · exact Or.inl h
    · right
      rw [show a+c-(b+d) = (a-b)+(c-d) by ring]
      exact (le_min h₁ h₂).trans (padicValRat.min_le_padicValRat_add
        (by rw [show a-b+(c-d) = a+c-(b+d) by ring]; exact sub_ne_zero.mpr h))

/-- Multiplying by a rational integral at the prime preserves congruence depth. -/
theorem congrScale {p e : ℕ} [Fact p.Prime] {a b c : ℚ}
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (hc : _root_.AbcTwoNinths.Basic.IntegralAt p c) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (c*a) (c*b) := by
  by_cases he : c*a = c*b
  · exact Or.inl he
  · have hn : c*(a-b) ≠ 0 := by
      rw [mul_sub]
      exact sub_ne_zero.mpr he
    obtain ⟨hc',hab⟩ := mul_ne_zero_iff.mp hn
    right
    rcases h with h | h
    · exact (hab (sub_eq_zero.mpr h)).elim
    · rw [← mul_sub, padicValRat.mul hc' hab]
      unfold _root_.AbcTwoNinths.Basic.IntegralAt at hc
      omega

/--
Two rational congruences may be multiplied when the first left factor and second right factor are integral at the prime.
-/
theorem congrMul {p e : ℕ} [Fact p.Prime] {a b c d : ℚ}
    (h₁ : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (h₂ : _root_.AbcTwoNinths.Basic.RatCongruent p e c d)
    (ha : _root_.AbcTwoNinths.Basic.IntegralAt p a) (hd : _root_.AbcTwoNinths.Basic.IntegralAt p d) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (a*c) (b*d) := by
  have h := _root_.AbcTwoNinths.Basic.congrAdd (_root_.AbcTwoNinths.Basic.congrScale h₁ hd) (_root_.AbcTwoNinths.Basic.congrScale h₂ ha)
  have hdiff : (d*a + a*c)-(d*b+a*d) = a*c-b*d := by ring
  rcases h with h | h
  · exact Or.inl (sub_eq_zero.mp (hdiff ▸ sub_eq_zero.mpr h))
  · exact Or.inr (hdiff ▸ h)

/-- Taking natural powers preserves congruence between rationals integral at the prime. -/
theorem congrPow {p e : ℕ} [Fact p.Prime] {a b : ℚ}
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (ha : _root_.AbcTwoNinths.Basic.IntegralAt p a) (hb : _root_.AbcTwoNinths.Basic.IntegralAt p b) (n : ℕ) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (a^n) (b^n) := by
  induction n with
  | zero => exact Or.inl (by simp)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact _root_.AbcTwoNinths.Basic.congrMul ih h (_root_.AbcTwoNinths.Basic.integralPow ha n) hb

-- The elaboration of rational grid transport needs a larger budget.
set_option maxHeartbeats 500000 in
/--
Substituting congruent powers of a common natural base for two principal units preserves every interpolation entry modulo the given prime power.
-/
theorem gridEntryTransport (p e c₁ c₂ g : ℕ) (a b : ℚ)
    (hp : p.Prime) (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (ha' : _root_.AbcTwoNinths.Basic.RatCongruent p e a ((g : ℚ)^c₂))
    (hb' : _root_.AbcTwoNinths.Basic.RatCongruent p e b ((g : ℚ)^c₁))
    (kt rs : ℕ × ℕ) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (_root_.AbcTwoNinths.Basic.determinantEntry a b c₁ c₂ kt rs)
      ((Nat.choose (rs.1*c₂ + rs.2*c₁) kt.1 : ℚ) *
        (g : ℚ)^(kt.2*(rs.1*c₂ + rs.2*c₁))) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hi (n : ℕ) : _root_.AbcTwoNinths.Basic.IntegralAt p (n : ℚ) := by
    unfold _root_.AbcTwoNinths.Basic.IntegralAt
    rw [padicValRat.of_nat]
    positivity
  have hia : _root_.AbcTwoNinths.Basic.IntegralAt p a := le_of_eq ha.2.1.symm
  have hib : _root_.AbcTwoNinths.Basic.IntegralAt p b := le_of_eq hb.2.1.symm
  have h₁ := _root_.AbcTwoNinths.Basic.congrPow ha' hia (_root_.AbcTwoNinths.Basic.integralPow (hi g) c₂) (kt.2*rs.1)
  have h₂ := _root_.AbcTwoNinths.Basic.congrPow hb' hib (_root_.AbcTwoNinths.Basic.integralPow (hi g) c₁) (kt.2*rs.2)
  have h := _root_.AbcTwoNinths.Basic.congrScale
    (_root_.AbcTwoNinths.Basic.congrMul h₁ h₂ (_root_.AbcTwoNinths.Basic.integralPow hia (kt.2*rs.1))
      (_root_.AbcTwoNinths.Basic.integralPow (_root_.AbcTwoNinths.Basic.integralPow (hi g) c₁) (kt.2*rs.2)))
    (hi (Nat.choose (rs.1*c₂ + rs.2*c₁) kt.1))
  rw [← pow_mul (g : ℚ) c₂, ← pow_mul (g : ℚ) c₁, ← pow_add] at h
  have he : c₂ * (kt.2 * rs.1) + c₁ * (kt.2 * rs.2) =
      kt.2 * (rs.1*c₂ + rs.2*c₁) := by ring
  simpa only [he, _root_.AbcTwoNinths.Basic.determinantEntry, mul_assoc] using h

/-- Rational congruence at a specified prime-power depth is symmetric. -/
theorem congrSymm {p e : ℕ} {a b : ℚ} (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rwa [show b-a = -(a-b) by ring, padicValRat.neg]

/--
A common base congruent to one modulo the prime whose powers lift both principal units gives a congruent interpolation entry.
-/
theorem determinantEntryCongruent (p e c₁ c₂ g : ℕ) (a b : ℚ)
    (hp : p.Prime) (_hg : g % p = 1)
    (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (ha' : _root_.AbcTwoNinths.Basic.RatCongruent p e ((g : ℚ)^c₂) a)
    (hb' : _root_.AbcTwoNinths.Basic.RatCongruent p e ((g : ℚ)^c₁) b)
    (kt rs : ℕ × ℕ) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (_root_.AbcTwoNinths.Basic.determinantEntry a b c₁ c₂ kt rs)
      ((Nat.choose (rs.1*c₂ + rs.2*c₁) kt.1 : ℚ) *
        (g : ℚ)^(kt.2*(rs.1*c₂ + rs.2*c₁))) :=
  _root_.AbcTwoNinths.Basic.gridEntryTransport p e c₁ c₂ g a b hp ha hb (_root_.AbcTwoNinths.Basic.congrSymm ha') (_root_.AbcTwoNinths.Basic.congrSymm hb') kt rs

end

end AbcTwoNinths.Basic
