/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.CoprimeLogBounds

/-!
# Coprime Two Logarithm Estimate

The module instantiates the coprime variable-radius real two-logarithm estimate with its explicit constant. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realVarRadiusLaurent1157`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Laurent's variable-radius lower bound for a linear form in the logarithms of two
multiplicatively independent positive rationals, with positive coprime coefficients
and constant `1157`.
-/
def CoprimeLaurent1157 : Prop :=
  ∀ (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ),
    1 < q₁ → 1 < q₂ →
    (∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0) →
    0 < b₁ → 0 < b₂ → b₁.Coprime b₂ → 1 ≤ radius →
    max (Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₁ : ℝ)|) radius) ≤ η₁ →
    max (Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₂ : ℝ)|) radius) ≤ η₂ →
    let B := (b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁;
    let D₀ := max 4 (Real.log B / radius);
    let form := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ);
    -Real.log |form| ≤ 1157 * η₁ * η₂ * D₀ ^ 2 / radius

/--
The Laurent estimate with constant `1157` extends from coprime to arbitrary positive
coefficients by dividing out their greatest common divisor.
-/
theorem realVarRadiusLaurent1157
    (coprime : _root_.AbcTwoNinths.ExteriorE1.CoprimeLaurent1157)
    (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ)
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (hind : ∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hr : 1 ≤ radius)
    (hη₁ : max (Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₁ : ℝ)|) radius) ≤ η₁)
    (hη₂ : max (Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₂ : ℝ)|) radius) ≤ η₂) :
    let B := (b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁;
    let D₀ := max 4 (Real.log B / radius);
    let form := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ);
    -Real.log |form| ≤ 1157 * η₁ * η₂ * D₀ ^ 2 / radius := by
  have hr' : 0 < radius := lt_of_lt_of_le zero_lt_one hr
  have radius_le (q : ℚ) (η : ℝ)
      (h : max (Real.log ((max q.num.natAbs q.den : ℕ) : ℝ))
        (max (Real.exp radius * |Real.log (q : ℝ)|) radius) ≤ η) : radius ≤ η :=
    ((max_le_iff.mp (max_le_iff.mp h).2).2)
  exact _root_.AbcTwoNinths.ExteriorE1.realVarRadiusLaurent1157OfCoprime q₁ q₂
    (zero_lt_one.trans hq₁) (zero_lt_one.trans hq₂) hind radius η₁ η₂ hr'
    (hr'.trans_le (radius_le q₁ η₁ hη₁)) (hr'.trans_le (radius_le q₂ η₂ hη₂))
    (fun m n hm hn hmn => coprime q₁ q₂ m n radius η₁ η₂
      hq₁ hq₂ hind hm hn hmn hr hη₁ hη₂) b₁ b₂ hb₁ hb₂

end

end AbcTwoNinths.ExteriorE1
