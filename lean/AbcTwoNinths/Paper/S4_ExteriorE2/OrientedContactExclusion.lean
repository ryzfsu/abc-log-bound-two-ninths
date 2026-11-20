/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.RowsDepth
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeContactBound

/-!
# Oriented Contact Exclusion

The module excludes oriented composite-modulus contact when its height and divisibility satisfy the stated parameters. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.excludeOrientedContact`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real

/--
Excludes deep contact between coprime positive powers of independent principal units at a composite modulus under the area and mass bounds. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem excludeOrientedContact {M c d L G : ℕ} {H x κ Q U Z : ℝ}
    (hM : 3 ≤ M) (hH : 0 ≤ H) (hκ : 0 < κ) (hQ : 44236800 / κ ≤ Q)
    (hx : x ≤ 4 * log (M : ℝ)) (hmass : κ * H / 16 ≤ (L : ℝ) * log (M : ℝ))
    (harea : U * Z ≤ 24 * H * x / Q) (hL : 146 + 2 * (G : ℝ) ≤ L)
    (hu : log (M : ℝ) ≤ U) (hz : log (M : ℝ) ≤ Z)
    (u z : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime M)ˣ)
    (hup : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal M 1) u.val = 1)
    (hzp : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal M 1) z.val = 1)
    (hind : ∀ m n : ℤ, u.val.val ^ m * z.val.val ^ n = 1 → m = 0 ∧ n = 0)
    (hcd : c.Coprime d) (hc : 0 < c) (hd : 0 < d)
    (hlog : log ((d : ℝ) / (U / log (M : ℝ)) + (c : ℝ) / (Z / log (M : ℝ))) + 1 ≤
      15 * log (M : ℝ))
    (hhu : log (max (u.val.val.num.natAbs : ℝ) (u.val.val.den : ℝ)) ≤ U)
    (hhz : log (max (z.val.val.num.natAbs : ℝ) (z.val.val.den : ℝ)) ≤ Z)
    (hcontact : (M : ℤ) ^ (L - G) ∣ (u.val ^ c - z.val ^ d).val.num) :
    False := by
  have hl : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have ha : 1 ≤ Z / log (M : ℝ) := (le_div_iff₀ hl).2 (by simpa using hz)
  have hb : 1 ≤ U / log (M : ℝ) := (le_div_iff₀ hl).2 (by simpa using hu)
  have hrows := _root_.AbcTwoNinths.ExteriorE2.rowsOrderLeDepth hH hκ hQ hx hl
    (mul_nonneg (hl.le.trans hu) (hl.le.trans hz)) hmass harea hL
  have hGL : G ≤ L := by exact_mod_cast (show (G : ℝ) ≤ L by linarith)
  have hdepth : _root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order ((Z / log (M : ℝ)) * (U / log (M : ℝ)))) ≤ L - G := by
    exact_mod_cast (show
      (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order ((Z / log (M : ℝ)) * (U / log (M : ℝ)))) : ℝ) ≤ ((L - G : ℕ) : ℝ) by
        rw [Nat.cast_sub hGL]
        exact hrows)
  apply _root_.AbcTwoNinths.ExteriorE2.compositeContactBoundOfLogBudget hM u z hup hzp hind hcd hc hd _ _ ha hb hlog
  · rwa [div_mul_cancel₀ _ hl.ne']
  · rwa [div_mul_cancel₀ _ hl.ne']
  · exact (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff _ _).2 ((pow_dvd_pow (M : ℤ) hdepth).trans hcontact)

end

end AbcTwoNinths.ExteriorE2
