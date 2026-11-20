/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.LocalTwoLogarithmClosure
public import AbcTwoNinths.Basic.RationalDepthReduction
public import AbcTwoNinths.Basic.RationalGridTransport

/-!
# Principal Unit Powers

The module lifts a primitive valuation estimate to arbitrary exponent pairs.

## Main results
* `AbcTwoNinths.Basic.exponentLTE`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section



/--
For multiplicatively independent principal units at an odd prime, a common positive exponent adds its valuation to that of the difference of powers.
-/
theorem exponentLTE : _root_.AbcTwoNinths.Basic.ExponentLTE := by
  intro p c d g a b hp hp' ha hb hi hc hd hg
  let _ : Fact p.Prime := ⟨hp⟩
  have powUnit (x : ℚ) (hx : _root_.AbcTwoNinths.Basic.RatPrincipalUnit p x) (j : ℕ) :
      _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p (x^j) := by
    exact _root_.AbcTwoNinths.Basic.principalPow hx j
  have hn : a^(c*g) ≠ b^(d*g) := by
    intro h
    have hh : a ^ ((c*g : ℕ) : ℤ) * b ^ (-((d*g : ℕ) : ℤ)) = 1 := by
      rw [zpow_neg, zpow_natCast, zpow_natCast, h, mul_inv_cancel₀ (pow_ne_zero _ hb.2.1)]
    have hz := (hi _ _ hh).1
    exact (Nat.mul_ne_zero hc.ne' hg.ne') (by exact_mod_cast hz)
  rw [pow_mul, pow_mul] at hn ⊢
  exact _root_.AbcTwoNinths.Basic.ltePair (hp.odd_of_ne_two (by omega)) hg
    (powUnit a ha.2 c) (powUnit b hb.2 d) hn

end

end AbcTwoNinths.Basic
