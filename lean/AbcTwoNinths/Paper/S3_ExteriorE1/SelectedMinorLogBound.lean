/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ClearedMinorLogBound
public import AbcTwoNinths.Paper.S3_ExteriorE1.ExactInterpolationWidth
public import AbcTwoNinths.Paper.S3_ExteriorE1.MonomialFactorialSumBound
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusDeterminantBound

/-!
# Selected Minor Log Bound

The module supplies the cleared selected minor's logarithmic inequality using the width and factorial bounds. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.clearedSelectedMinorLogIneq`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section
open scoped BigOperators

/--
A nonzero selected interpolation minor gives a logarithmic bound in terms of the rectangle dimensions and rational heights. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem clearedSelectedMinorLogIneq {J L R S b₁ b₂ : ℕ}
    (hJ : 0 < J) (hL : 2 ≤ L) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hM : 0 < R * b₂ + S * b₁)
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (η₁ η₂ Q₀ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hh₁ : Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ) ≤ η₁)
    (hh₂ : Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ) ≤ η₂)
    (hQ₀ : 2 ≤ Q₀)
    (f : (Fin (J + 1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle R S)
    (hdet : (Matrix.of fun k j : Fin (J + 1) × Fin L =>
      (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
        (q₁ : ℝ) ^ (k.2.val * (f j).1.val) *
        (q₂ : ℝ) ^ (k.2.val * (f j).2.val)).det ≠ 0)
    (hS : 2 * (L - 1) * S ≤ (J + 1) * L)
    (hγM : (Real.log (q₁ : ℝ) / (b₂ : ℝ)) * ((R * b₂ + S * b₁ : ℕ) : ℝ) ≤
      ((J + 1 : ℕ) : ℝ) / Q₀)
    (hΛ : |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤
      ((((J + 1) * L : ℕ) : ℝ) * Q₀ ^ ((J + 1) * L))⁻¹) :
    let K := J + 1
    let N := K * L
    let M : ℝ := (R * b₂ + S * b₁ : ℕ)
    (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log (Q₀ / Real.exp 1) ≤
      2 * Real.log 2 + 2 * Real.log (N : ℝ) + 2 / (N : ℝ) +
        (J : ℝ) * Real.log (Real.exp 2 * M / (J : ℝ)) +
        (1 / 2 : ℝ) * (L : ℝ) * ((R : ℝ) * η₁ + (S : ℝ) * η₂) := by
  exact _root_.AbcTwoNinths.ExteriorE1.clearedSelectedMinorLogIneqFrom hL hM q₁ q₂ hq₁ hq₂ η₁ η₂ Q₀
    hη₁ hη₂ hh₁ hh₂ hQ₀ f hdet (_root_.AbcTwoNinths.ExteriorE1.exactWidthL (J+1) L)
    (fun V₁ V₂ hV₁ hV₂ => _root_.AbcTwoNinths.ExteriorE1.realVarRadiusDetBound (by omega) hL hb₁ hb₂ q₁ q₂
      hq₁ hq₂ f V₁ V₂ hV₁ hV₂ Q₀ hQ₀ hS hγM hΛ)
    (_root_.AbcTwoNinths.ExteriorE1.sumLogMonofactUpper J L hJ (Nat.cast_pos.mpr hM))

end

end AbcTwoNinths.ExteriorE1
