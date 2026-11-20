/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.InterpolationGrid
public import AbcTwoNinths.Basic.TwoLogarithmConstants
public import AbcTwoNinths.Basic.RationalGridTransport

/-!
# Rational Depth Reduction

Duplicate labels `r * d + s * c` bound coprime exponents by the rectangle dimensions. At an odd
prime, lifting the difference of principal units by a common exponent adds the valuation of that
exponent.

## Main results
* `AbcTwoNinths.Basic.duplicateBounds`
* `AbcTwoNinths.Basic.rationalDifferenceBound`
* `AbcTwoNinths.Basic.ltePair`
* `AbcTwoNinths.Basic.principalPow`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

set_option autoImplicit false

/--
If distinct points of [0,R] by [0,S] have the same value of rd + sc for positive coprime c and d, then c is at most R and d is at most S.
-/
theorem duplicateBounds {c d R S r r' s s' : ℕ} (hc : c.Coprime d)
    (hc0 : 0 < c) (hd0 : 0 < d) (hr : r ≤ R) (hr' : r' ≤ R)
    (hs : s ≤ S) (hs' : s' ≤ S) (hne : (r,s) ≠ (r',s'))
    (h : r*d+s*c = r'*d+s'*c) : c ≤ R ∧ d ≤ S := by
  wlog hrr : r ≤ r' generalizing r r' s s'
  · exact this hr' hr hs' hs (Ne.symm hne) h.symm (by omega)
  have hss : s' ≤ s := by
    have hd := Nat.mul_le_mul_right d hrr
    nlinarith
  have he : (r'-r)*d = (s-s')*c := by
    rw [Nat.sub_mul, Nat.sub_mul]
    omega
  have hlt : r < r' := by
    by_contra! hn
    have hrr' : r = r' := by omega
    have hss' : s = s' := by
      subst r'
      nlinarith
    exact hne (Prod.ext hrr' hss')
  have hlt' : s' < s := by
    by_contra! hn
    have hz : s-s' = 0 := by omega
    rw [hz, zero_mul] at he
    rcases mul_eq_zero.mp he with h0 | h0 <;> omega
  have hdv : c ∣ r'-r := hc.dvd_of_dvd_mul_right (by rw [he]; exact dvd_mul_left _ _)
  have hdv' : d ∣ s-s' := hc.symm.dvd_of_dvd_mul_right
    (by rw [← he]; exact dvd_mul_left _ _)
  exact ⟨(Nat.le_of_dvd (by omega) hdv).trans (by omega),
    (Nat.le_of_dvd (by omega) hdv').trans (by omega)⟩

/--
The valuation of a nonzero integer times the logarithm of the prime is bounded by the logarithm of its absolute value.
-/
theorem valIntLog {p : ℕ} [Fact p.Prime] {n : ℤ} (hn : n ≠ 0) :
    (padicValInt p n : ℝ) * Real.log p ≤ Real.log n.natAbs := by
  have hd : p ^ padicValInt p n ∣ n.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr (padicValInt_dvd (p := p) n)
  have hh : (p : ℝ)^padicValInt p n ≤ (n.natAbs : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp _) hh

/--
The reduced denominator of a rational of valuation zero has valuation zero at the same prime.
-/
theorem denominatorValZero {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : padicValRat p x = 0) : padicValRat p (x.den : ℚ) = 0 := by
  have hp : p.Prime := Fact.out
  have hd : ¬ p ∣ x.den := by
    intro h
    have hn : ¬ p ∣ x.num.natAbs := fun hn =>
      hp.not_dvd_one (x.reduced.gcd_eq_one ▸ Nat.dvd_gcd hn h)
    have hn' : padicValNat p x.num.natAbs = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hn))
    have hd' : 1 ≤ padicValNat p x.den :=
      (padicValNat_dvd_iff_le x.den_ne_zero).mp (by simpa using h)
    change (padicValNat p x.num.natAbs : ℤ) - (padicValNat p x.den : ℤ) = 0 at hx
    omega
  rw [padicValRat.of_nat]
  exact_mod_cast (padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hd)) : padicValNat p x.den = 0)

/--
The valuation of a nonzero difference of powers of rational principal units, times log p, is at most log 2 plus their exponent-weighted heights.
-/
theorem rationalDifferenceBound {p c d : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p x) (hy : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p y) (hne : x^c ≠ y^d) :
    (padicValRat p (x^c-y^d) : ℝ) * Real.log p ≤
      Real.log 2 + c * _root_.AbcTwoNinths.Basic.padicRationalHeight x + d * _root_.AbcTwoNinths.Basic.padicRationalHeight y := by
  let X := x.num ^ c * (y.den : ℤ) ^ d
  let Y := y.num ^ d * (x.den : ℤ) ^ c
  let D := (x.den : ℚ)^c * (y.den : ℚ)^d
  have hd : D ≠ 0 := by dsimp [D]; positivity
  have hD : padicValRat p D = 0 := by
    rw [show D = (x.den : ℚ)^c * (y.den : ℚ)^d from rfl,
      padicValRat.mul (by positivity) (by positivity)]
    simp [_root_.AbcTwoNinths.Basic.denominatorValZero hx.2.1, _root_.AbcTwoNinths.Basic.denominatorValZero hy.2.1]
  have he : x^c-y^d = ((X-Y : ℤ) : ℚ) / D := by
    conv_lhs => rw [← x.num_div_den, ← y.num_div_den, div_pow, div_pow]
    push_cast [X,Y,D]
    field_simp
  have hxy : X-Y ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp (by simp [he,hz]))
  rw [he, padicValRat.div (by exact_mod_cast hxy) hd, hD, sub_zero,
    padicValRat.of_int, Int.cast_natCast]
  let A : ℕ := max x.num.natAbs x.den
  let B : ℕ := max y.num.natAbs y.den
  have hA : (0 : ℝ) < A := by exact_mod_cast x.pos.trans_le (le_max_right _ _)
  have hB : (0 : ℝ) < B := by exact_mod_cast y.pos.trans_le (le_max_right _ _)
  have hX : X.natAbs ≤ A^c * B^d := by
    simp only [X, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left ..) _) (Nat.pow_le_pow_left (le_max_right ..) _)
  have hY : Y.natAbs ≤ A^c * B^d := by
    simp only [Y, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [mul_comm]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_right ..) _) (Nat.pow_le_pow_left (le_max_left ..) _)
  have hsize : ((X-Y).natAbs : ℝ) ≤ 2*((A : ℝ)^c * (B : ℝ)^d) := by
    have ht : (X-Y).natAbs ≤ X.natAbs+Y.natAbs := by
      simpa [sub_eq_add_neg] using Int.natAbs_add_le X (-Y)
    exact_mod_cast ht.trans (by omega : X.natAbs+Y.natAbs ≤ 2*(A^c*B^d))
  have hlog := Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr hxy) hsize
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  exact (_root_.AbcTwoNinths.Basic.valIntLog hxy).trans (by simpa [_root_.AbcTwoNinths.Basic.padicRationalHeight,A,B,add_assoc] using hlog)

/--
For principal units at an odd prime, the valuation of a nonzero difference of equal-exponent powers equals the valuation of the base difference plus that of the exponent.
-/
theorem ltePair {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 0 < k)
    {x y : ℚ} (hx : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p x) (hy : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p y)
    (hne : x^k ≠ y^k) :
    padicValRat p (x^k-y^k) = padicValRat p (x-y) + padicValNat p k := by

  have h1 (z : ℚ) (hz : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p z) : _root_.AbcTwoNinths.Basic.RatCongruent p 1 z 1 :=
    hz.2.2.imp id (by intro h; norm_num; omega)
  have hxy := _root_.AbcTwoNinths.Basic.congrAdd (h1 x hx)
    (_root_.AbcTwoNinths.Basic.congrScale (h1 y hy) (c := -1) (by simp [_root_.AbcTwoNinths.Basic.IntegralAt]))
  have hdiff : _root_.AbcTwoNinths.Basic.RatCongruent p 1 (x-y) 0 := by simpa [sub_eq_add_neg] using hxy
  have hn : x ≠ y := fun h => hne (congrArg (fun z : ℚ => z^k) h)
  let a := x.num * (y.den : ℤ)
  let b := y.num * (x.den : ℤ)
  let D := (x.den : ℚ) * (y.den : ℚ)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hvD : padicValRat p D = 0 := by
    dsimp [D]
    rw [padicValRat.mul (by positivity) (by positivity),
      _root_.AbcTwoNinths.Basic.denominatorValZero hx.2.1, _root_.AbcTwoNinths.Basic.denominatorValZero hy.2.1, add_zero]
  have hxa : x = (a : ℚ)/D := by
    conv_lhs => rw [← x.num_div_den]
    push_cast [a,D]
    field_simp
  have hyb : y = (b : ℚ)/D := by
    conv_lhs => rw [← y.num_div_den]
    push_cast [b,D]
    field_simp
  have hna : a-b ≠ 0 := fun h => hn (by rw [hxa, hyb, sub_eq_zero.mp h])
  have hnap : a^k-b^k ≠ 0 := fun h => hne (by
    have hc := congrArg (fun z : ℤ => (z : ℚ)) (sub_eq_zero.mp h)
    push_cast at hc
    rw [hxa,hyb,div_pow,div_pow,hc])
  have hbq : (b : ℚ) ≠ 0 := fun h => hy.1 (by simp [hyb,h])
  have havb : padicValInt p b = 0 := by
    have h := hy.2.1
    rw [hyb, padicValRat.div hbq hD, hvD, sub_zero, padicValRat.of_int] at h
    exact_mod_cast h
  have hbd : ¬ (p : ℤ) ∣ b := by
    intro h
    rcases (padicValInt_dvd_iff (p := p) 1 b).mp (by simpa using h) with h | h
    · exact hbq (by simp [h])
    · omega
  have hsub : x-y = ((a-b : ℤ) : ℚ)/D := by rw [hxa,hyb, Int.cast_sub, sub_div]
  have hsubp : x^k-y^k = ((a^k-b^k : ℤ) : ℚ)/D^k := by
    rw [hxa,hyb,div_pow,div_pow, Int.cast_sub, Int.cast_pow, Int.cast_pow, sub_div]
  have hdiv : (p : ℤ) ∣ a-b := by
    have h := hdiff.resolve_left (sub_ne_zero.mpr hn)
    rw [sub_zero, hsub, padicValRat.div (by exact_mod_cast hna) hD, hvD, sub_zero,
      padicValRat.of_int] at h
    simpa using (padicValInt_dvd_iff (p := p) 1 _).mpr (.inr (by exact_mod_cast h))
  have h := Int.emultiplicity_pow_sub_pow (Fact.out : p.Prime) hp
    (show (p : ℤ) ∣ b-a by simpa only [neg_sub] using dvd_neg.mpr hdiv) hbd k
  have hneg₁ : b-a ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hna).symm
  have hneg₂ : b^k-a^k ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hnap).symm
  rw [((padicValRat.finite_int_prime_iff (p := p)).2 hneg₂).emultiplicity_eq_multiplicity,
    ((padicValRat.finite_int_prime_iff (p := p)).2 hneg₁).emultiplicity_eq_multiplicity,
    ← padicValNat_eq_emultiplicity hk.ne', ← padicValInt.of_ne_one_ne_zero,
    ← padicValInt.of_ne_one_ne_zero, ← Nat.cast_add] at h
  have h' := ENat.natCast_inj.mp h
  rw [show b-a = -(a-b) by ring, show b^k-a^k = -(a^k-b^k) by ring] at h'
  simp only [padicValInt, Int.natAbs_neg] at h'
  rw [hsub, hsubp, padicValRat.div (by exact_mod_cast hnap) (pow_ne_zero _ hD),
    padicValRat.div (by exact_mod_cast hna) hD, padicValRat.pow, hvD, mul_zero,
    sub_zero, sub_zero, padicValRat.of_int, padicValRat.of_int]
  exact_mod_cast h'

/-- Every natural power of a rational principal unit is a principal unit at the same prime. -/
theorem principalPow {p : ℕ} [Fact p.Prime] {a : ℚ}
    (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (c : ℕ) : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p (a^c) := by
  have hc : _root_.AbcTwoNinths.Basic.RatCongruent p 1 a 1 := ha.2.2.imp id (by intro h; norm_num; omega)
  have hh := _root_.AbcTwoNinths.Basic.congrPow hc ha.2.1.symm.le (by simp [_root_.AbcTwoNinths.Basic.IntegralAt]) c
  refine ⟨pow_ne_zero _ ha.1, by simp [ha.2.1], ?_⟩
  simpa using hh.imp id (fun h => (show (0 : ℤ) < 1 by decide).trans_le h)

end

end AbcTwoNinths.Basic
