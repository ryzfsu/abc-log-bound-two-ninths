/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeHeight
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeCrossDifference

/-!
# Composite Collision Height

The module bounds the absolute value of the cross difference of two rational power monomials. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositePowerCrossBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
The absolute cross-difference of two integer powers is bounded by twice the product of their powered coordinate heights.
-/
theorem crossPowerAbsBound (n m p q : ℤ) (c d : ℕ) :
    (((n ^ c * q ^ d - p ^ d * m ^ c).natAbs : ℕ) : ℝ) ≤
      2 * (max (n.natAbs : ℝ) (m.natAbs : ℝ)) ^ c *
        (max (p.natAbs : ℝ) (q.natAbs : ℝ)) ^ d := by
  have h := Int.natAbs_sub_le (n ^ c * q ^ d) (p ^ d * m ^ c)
  simp only [Int.natAbs_mul, Int.natAbs_pow] at h
  have hh : (((n ^ c * q ^ d - p ^ d * m ^ c).natAbs : ℕ) : ℝ) ≤
      (n.natAbs : ℝ) ^ c * (q.natAbs : ℝ) ^ d + (p.natAbs : ℝ) ^ d * (m.natAbs : ℝ) ^ c := by
    exact_mod_cast h
  have h1 := mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ (n.natAbs : ℝ))
      (le_max_left _ (m.natAbs : ℝ)) c)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (q.natAbs : ℝ))
      (le_max_right (p.natAbs : ℝ) _) d) (by positivity) (by positivity)
  have h2 := mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ (p.natAbs : ℝ))
      (le_max_left _ (q.natAbs : ℝ)) d)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (m.natAbs : ℝ))
      (le_max_right (n.natAbs : ℝ) _) c) (by positivity) (by positivity)
  exact hh.trans (by nlinarith)

/--
A congruence between distinct rational powers modulo a composite modulus power bounds its logarithm by the two input heights and log two. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositePowerCrossBound {B E c d : ℕ} (hB : 0 < B)
    (a b : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B E) (a^c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B E) (b^d))
    (hne : a.val^c ≠ b.val^d) :
    (E : ℝ) * Real.log B ≤ Real.log 2 +
      (c : ℝ) * Real.log (max (a.val.num.natAbs : ℝ) (a.val.den : ℝ)) +
      (d : ℝ) * Real.log (max (b.val.num.natAbs : ℝ) (b.val.den : ℝ)) := by
  let z : ℤ := a.val.num ^ c * (b.val.den : ℤ) ^ d - b.val.num ^ d * (a.val.den : ℤ) ^ c
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    rw [← (a.val^c).num_div_den, ← (b.val^d).num_div_den]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    have he := sub_eq_zero.mp hz
    simpa using (show ((a.val.num ^ c * (b.val.den : ℤ) ^ d : ℤ) : ℚ) =
      ((b.val.num ^ d * (a.val.den : ℤ) ^ c : ℤ) : ℚ) by exact_mod_cast he)
  have hd : (B : ℤ) ^ E ∣ z := by
    simpa [z, Subring.coe_pow] using _root_.AbcTwoNinths.ExteriorE2.compositeCrossDifference (a^c) (b^d) hab
  have hu : (z.natAbs : ℝ) ≤
      2 * (max (a.val.num.natAbs : ℝ) (a.val.den : ℝ)) ^ c *
        (max (b.val.num.natAbs : ℝ) (b.val.den : ℝ)) ^ d := by
    simpa [z] using _root_.AbcTwoNinths.ExteriorE2.crossPowerAbsBound a.val.num a.val.den b.val.num b.val.den c d
  have ha : 0 < max (a.val.num.natAbs : ℝ) (a.val.den : ℝ) :=
    (show (0 : ℝ) < a.val.den by exact_mod_cast a.val.den_pos).trans_le (le_max_right _ _)
  have hb : 0 < max (b.val.num.natAbs : ℝ) (b.val.den : ℝ) :=
    (show (0 : ℝ) < b.val.den by exact_mod_cast b.val.den_pos).trans_le (le_max_right _ _)
  have hlog := Real.log_le_log (show (0 : ℝ) < z.natAbs by
    exact_mod_cast Int.natAbs_pos.mpr hz) hu
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
    (by positivity), Real.log_pow, Real.log_pow] at hlog
  exact (_root_.AbcTwoNinths.ExteriorE2.compositeLogOfDepth hB hz hd).trans hlog

end

end AbcTwoNinths.ExteriorE2
