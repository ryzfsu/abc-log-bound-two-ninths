/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing
public import AbcTwoNinths.Paper.S3_ExteriorE1.DeterminantSelectionAndLiouville
public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationGridDimensions
public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialPerturbation
public import AbcTwoNinths.Paper.S3_ExteriorE1.SelectedMinorLogBound
public import AbcTwoNinths.Paper.S3_ExteriorE1.RadiusAndGridInequalities

/-!
# Variable Radius Logarithm Estimate

The module combines determinant selection and radius bounds to derive a real two-logarithm estimate for coprime sources. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.logBoundOfExcludingSmall`
* `AbcTwoNinths.ExteriorE1.phaseLeOfSmall`
* `AbcTwoNinths.ExteriorE1.realVarRadiusLaurentCoprimeOfInputs`
* `AbcTwoNinths.ExteriorE1.realVarRadiusLaurentCoprime`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The rectangle with balanced square-root side bounds contains more than the prescribed number of nodes.
-/
theorem radiusRectangleCard (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    n < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle
      ⌊Real.sqrt ((n : ℝ) * b / a)⌋₊ ⌊Real.sqrt ((n : ℝ) * a / b)⌋₊) := by
  apply _root_.AbcTwoNinths.Basic.rectangleCardGt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Nat.lt_floor_add_one _) (Nat.lt_floor_add_one _)
  rw [← Real.sqrt_mul (by positivity)]
  have h : (n : ℝ) * b / a * ((n : ℝ) * a / b) = (n : ℝ) ^ 2 := by
    field_simp
  rw [h, Real.sqrt_sq (by positivity)]

/--
A scaled absolute-value bound gives the corresponding upper bound with the inverse exponential factor.
-/
theorem radiusLogInput (x η radius : ℝ) (hx : 0 ≤ x)
    (h : Real.exp radius * |x| ≤ η) :
    x ≤ Real.exp (-radius) * η := by
  rw [abs_of_nonneg hx] at h
  rw [Real.exp_neg, ← div_eq_inv_mul]
  apply (le_div_iff₀ (Real.exp_pos _)).2
  simpa [mul_comm] using h

/--
Excluding forms of size at most the reciprocal cap bounds the negative logarithm of the absolute form. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem logBoundOfExcludingSmall (form cap budget : ℝ) (hcap : 0 < cap)
    (hsmall : |form| ≤ cap⁻¹ → False) (hbudget : Real.log cap ≤ budget) :
    -Real.log |form| ≤ budget := by
  have hlt : cap⁻¹ < |form| := lt_of_not_ge hsmall
  have hlog := Real.log_lt_log (inv_pos.mpr hcap) hlt
  rw [Real.log_inv] at hlog
  linarith

/--
A small two-term form and a perturbation budget bound the phase used in the minor estimate. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem phaseLeOfSmall (x y b₁ b₂ R S xMax yMax ε target : ℝ)
    (hb₂ : 1 ≤ b₂) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hx : x ≤ xMax) (hy : y ≤ yMax)
    (hsmall : |b₂ * y - b₁ * x| ≤ ε)
    (hcert : R * xMax + S * yMax + S * ε ≤ target) :
    (x / b₂) * (R * b₂ + S * b₁) ≤ target := by
  have hb₂' : 0 < b₂ := by linarith
  have ht : -(b₂ * y - b₁ * x) / b₂ ≤ ε := by
    apply (div_le_iff₀ hb₂').2
    have hε : 0 ≤ ε := (abs_nonneg _).trans hsmall
    have hl := (abs_le.mp hsmall).1
    nlinarith
  calc
    (x / b₂) * (R * b₂ + S * b₁) =
        R * x + S * y + S * (-(b₂ * y - b₁ * x) / b₂) := by
      field_simp
      ring
    _ ≤ R * xMax + S * yMax + S * ε :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hx hR) (mul_le_mul_of_nonneg_left hy hS))
        (mul_le_mul_of_nonneg_left ht hS)
    _ ≤ target := hcert

/--
The Liouville and selected-minor alternatives give the variable-radius bound with constant 1157 under the stated estimates. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realVarRadiusLaurentCoprimeOfInputs
    (x y η₁ η₂ radius D Q : ℝ) (b₁ b₂ R S R₂ S₂ N K L : ℕ)
    (hr : 0 < radius) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hb₂ : 0 < b₂) (hN : 0 < N) (hQ : 0 < Q)
    (hx : x ≤ Real.exp (-radius) * η₁)
    (hy : y ≤ Real.exp (-radius) * η₂)
    (hperturb : (R : ℝ) * (Real.exp (-radius) * η₁) +
      (S : ℝ) * (Real.exp (-radius) * η₂) +
      (S : ℝ) * ((N : ℝ) * Q ^ N)⁻¹ ≤ (K : ℝ) / Q)
    (hheight : (R₂ : ℝ) * η₁ + (S₂ : ℝ) * η₂ ≤ 12 * η₁ * η₂ * D ^ 2 / radius)
    (liouville : -Real.log |(b₂ : ℝ) * y - (b₁ : ℝ) * x| ≤
      (b₁ : ℝ) * η₁ + (b₂ : ℝ) * η₂)
    (rhs : ℝ)
    (hselect : (b₁ ≤ R₂ ∧ b₂ ≤ S₂) ∨
      ((x / (b₂ : ℝ)) * ((R : ℝ) * b₂ + (S : ℝ) * b₁) ≤ (K : ℝ) / Q →
        |(b₂ : ℝ) * y - (b₁ : ℝ) * x| ≤ ((N : ℝ) * Q ^ N)⁻¹ →
        (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log (Q / Real.exp 1) ≤ rhs))
    (hcontradiction : rhs < (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log (Q / Real.exp 1))
    (hfinal : Real.log ((N : ℝ) * Q ^ N) ≤ 1157 * η₁ * η₂ * D ^ 2 / radius) :
    -Real.log |(b₂ : ℝ) * y - (b₁ : ℝ) * x| ≤ 1157 * η₁ * η₂ * D ^ 2 / radius := by
  rcases hselect with ⟨hb₁R₂, hb₂S₂⟩ | hminor
  · refine liouville.trans ((add_le_add ?_ ?_).trans (hheight.trans ?_))
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb₁R₂) hη₁
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb₂S₂) hη₂
    · have hnonneg : 0 ≤ η₁ * η₂ * D ^ 2 / radius := by positivity
      convert mul_le_mul_of_nonneg_right (show (12 : ℝ) ≤ 1157 by norm_num) hnonneg using 1
      <;> ring
  · refine _root_.AbcTwoNinths.ExteriorE1.logBoundOfExcludingSmall _ _ _ (by positivity) ?_ hfinal
    intro hsmall
    have hb₂r : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb₂
    have hphase := _root_.AbcTwoNinths.ExteriorE1.phaseLeOfSmall x y b₁ b₂ R S _ _ _ _ hb₂r
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hx hy hsmall hperturb
    exact (not_le_of_gt hcontradiction) (hminor hphase hsmall)



/-- The laurent radius parameters. This is used in the proof of Proposition 3.1 of the paper. -/
structure LaurentRadiusParameters (radius η₁ η₂ D : ℝ) where
  L : ℕ := ⌊3 * D⌋₊ + 1
  J : ℕ := ⌊160 * η₁ * η₂ * D / radius ^ 2⌋₊
  R₁ : ℕ := ⌊Real.sqrt ((L : ℝ) * η₂ / η₁)⌋₊
  S₁ : ℕ := ⌊Real.sqrt ((L : ℝ) * η₁ / η₂)⌋₊
  R₂ : ℕ := ⌊Real.sqrt ((L : ℝ) * J * η₂ / η₁)⌋₊
  S₂ : ℕ := ⌊Real.sqrt ((L : ℝ) * J * η₁ / η₂)⌋₊

section

variable {radius η₁ η₂ D : ℝ}

/--
The number of degree indices is one more than the degree parameter. This is used in the proof of Proposition 3.1 of the paper.
-/
def LaurentRadiusParameters.k (p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D) := p.J + 1
/--
The size of the selected minor is the degree count times the number of levels. This is used in the proof of Proposition 3.1 of the paper.
-/
def LaurentRadiusParameters.n (p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D) := p.k * p.L
/--
The combined first coordinate bound is the sum of the two rectangle bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
def LaurentRadiusParameters.r (p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D) := p.R₁ + p.R₂
/--
The combined second coordinate bound is the sum of the two rectangle bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
def LaurentRadiusParameters.s (p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D) := p.S₁ + p.S₂

end

/--
The default grid has positive size and its scale controls the logarithm of the weighted exponent sum.
-/
theorem radiusParameterCore (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ)
    (hb₂ : 0 < b₂) (hr : 0 < radius) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) :
    let B := (b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁
    let D := max 4 (Real.log B / radius)
    let p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D := {}
    0 < B ∧ 4 ≤ D ∧ Real.log B ≤ radius * D ∧ 0 < p.n := by
  dsimp only
  constructor
  · positivity
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · rw [mul_comm]
    exact (div_le_iff₀ hr).1 (le_max_right _ _)
  · simp [_root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters.n, _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters.k]

/--
For two multiplicatively independent rational bases and positive coprime coefficients,
the variable-radius Laurent bound holds with constant `1157`.
-/
theorem realVarRadiusLaurentCoprime
    (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ)
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (hind : ∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hcop : b₁.Coprime b₂) (hr : 1 ≤ radius)
    (hη₁ : max (Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₁ : ℝ)|) radius) ≤ η₁)
    (hη₂ : max (Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ))
      (max (Real.exp radius * |Real.log (q₂ : ℝ)|) radius) ≤ η₂) :
    let D := max 4 (Real.log ((b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁) / radius);
    -Real.log |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤
      1157 * η₁ * η₂ * D ^ 2 / radius := by
  let D := max 4 (Real.log ((b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁) / radius)
  let p : _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters radius η₁ η₂ D := {}
  let Q := (10 / 3 : ℝ) * Real.exp radius / radius
  change -Real.log |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤ _
  have hr' : 0 < radius := zero_lt_one.trans_le hr
  obtain ⟨hh₁, h₁, h₁r⟩ := (max_le_iff.mp hη₁).imp_right max_le_iff.mp
  obtain ⟨hh₂, h₂, h₂r⟩ := (max_le_iff.mp hη₂).imp_right max_le_iff.mp
  have h₁p := hr'.trans_le h₁r
  have h₂p := hr'.trans_le h₂r
  obtain ⟨_, hD, hlogB, hN⟩ := _root_.AbcTwoNinths.ExteriorE1.radiusParameterCore b₁ b₂ radius η₁ η₂ hb₂ hr' h₁p h₂p
  obtain ⟨hL, _, _, _, _, hJ, hK, _, _, _, _, _, hR₂, _, _, hgrid, hheight, hS, hdim⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.certParamBounds hr h₁r h₂r hD
  have hSK : p.s ≤ p.k := by
    have hSr : (p.s : ℝ) ≤ (3 / 20 : ℝ) * p.k := hS
    have hK0 : (0 : ℝ) ≤ p.k := Nat.cast_nonneg _
    exact_mod_cast (show (p.s : ℝ) ≤ p.k by linarith)
  have hL' : 1 ≤ p.L := (by decide : 1 ≤ 13).trans hL
  obtain ⟨hQ, _, _, _, _, _, hp, _⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.certQ0AndPerturbationOfGrid hr' hK hL' hSK hdim hgrid
  have hperturb : (p.r : ℝ) * (Real.exp (-radius) * η₁) +
      (p.s : ℝ) * (Real.exp (-radius) * η₂) +
      (p.s : ℝ) * ((p.n : ℝ) * Q ^ p.n)⁻¹ ≤ (p.k : ℝ) / Q := by
    change (p.r : ℝ) * Real.exp (-radius) * η₁ +
      (p.s : ℝ) * Real.exp (-radius) * η₂ +
      (p.s : ℝ) * ((p.n : ℝ) * Q ^ p.n)⁻¹ ≤ (p.k : ℝ) / Q at hp
    rw [mul_assoc (p.r : ℝ), mul_assoc (p.s : ℝ)] at hp
    exact hp
  have hliouv := _root_.AbcTwoNinths.ExteriorE1.liouvilleTwoLogBound q₁ q₂ b₁ b₂ η₁ η₂ hq₁ hq₂ hind hb₁ hb₂ hh₁ hh₂
  have card₁ : p.L ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle p.R₁ p.S₁) :=
    (_root_.AbcTwoNinths.ExteriorE1.radiusRectangleCard p.L η₁ η₂ h₁p h₂p).le
  have card₂ : p.L * p.J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle p.R₂ p.S₂) := by
    simpa only [Nat.cast_mul] using _root_.AbcTwoNinths.ExteriorE1.radiusRectangleCard (p.L * p.J) η₁ η₂ h₁p h₂p
  let M := (p.r : ℝ) * b₂ + (p.s : ℝ) * b₁
  let rhs := 2 * Real.log 2 + 2 * Real.log (p.n : ℝ) + 2 / (p.n : ℝ) +
    (p.J : ℝ) * Real.log (Real.exp 2 * M / (p.J : ℝ)) +
    (1 / 2 : ℝ) * (p.L : ℝ) * ((p.r : ℝ) * η₁ + (p.s : ℝ) * η₂)
  have hcontra : rhs < (p.k : ℝ) * ((p.L - 1 : ℕ) : ℝ) * Real.log (Q / Real.exp 1) := by
    have hc := (_root_.AbcTwoNinths.ExteriorE1.certRhsContradiction hr h₁r h₂r hD hb₁ hb₂ hlogB).2
    change (2 * Real.log 2 + 2 / (p.n : ℝ) + 2 * Real.log (p.n : ℝ)) +
      (p.J : ℝ) * Real.log (Real.exp 2 * M / (p.J : ℝ)) +
      (1 / 2 : ℝ) * (p.L : ℝ) * ((p.r : ℝ) * η₁ + (p.s : ℝ) * η₂) <
        (p.k : ℝ) * ((p.L : ℝ) - 1) * Real.log (Q / Real.exp 1) at hc
    rw [Nat.cast_sub hL']
    push_cast
    dsimp [rhs]
    linarith only [hc]
  have hfinal : Real.log ((p.n : ℝ) * Q ^ p.n) ≤ 1157 * η₁ * η₂ * D ^ 2 / radius := by
    have hc := (_root_.AbcTwoNinths.ExteriorE1.certRadiusFinal1157Le4000 hr h₁r h₂r hD).1
    change Real.log ((p.n : ℝ) * Q ^ p.n) ≤ 1157 * (η₁ * η₂ * D ^ 2 / radius) at hc
    simpa only [mul_div_assoc, mul_assoc] using hc
  apply _root_.AbcTwoNinths.ExteriorE1.realVarRadiusLaurentCoprimeOfInputs _ _ η₁ η₂ radius D Q b₁ b₂
    p.r p.s p.R₂ p.S₂ p.n p.k p.L hr' h₁p.le h₂p.le hb₂ hN (by dsimp [Q]; positivity)
    (_root_.AbcTwoNinths.ExteriorE1.radiusLogInput _ _ _ (Real.log_nonneg (by exact_mod_cast hq₁.le)) h₁)
    (_root_.AbcTwoNinths.ExteriorE1.radiusLogInput _ _ _ (Real.log_nonneg (by exact_mod_cast hq₂.le)) h₂)
    hperturb hheight hliouv rhs ?_ hcontra hfinal
  rcases _root_.AbcTwoNinths.ExteriorE1.selectOrLiouville q₁ q₂ hq₁ hq₂ hind hb₁ hb₂ hcop card₁ card₂ with h | ⟨f, hf⟩
  · exact Or.inl h
  · apply Or.inr
    intro hphase hsmall
    have hR₂' : 91 ≤ p.R₂ := hR₂
    have hRp : 0 < p.r := by
      simp only [_root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters.r]
      omega
    have hMp : 0 < p.r * b₂ + p.s * b₁ := by positivity
    have hL₂ : 2 ≤ p.L := (by decide : 2 ≤ 13).trans hL
    have hJ' : 0 < p.J := (by decide : 0 < 640).trans_le hJ
    have hphase' : (Real.log (q₁ : ℝ) / (b₂ : ℝ)) * ((p.r * b₂ + p.s * b₁ : ℕ) : ℝ) ≤
      (p.k : ℝ) / Q := by simpa only [Nat.cast_add, Nat.cast_mul] using hphase
    have hu := _root_.AbcTwoNinths.ExteriorE1.clearedSelectedMinorLogIneq hJ' hL₂ hb₁ hb₂ hMp q₁ q₂ hq₁ hq₂
      η₁ η₂ Q h₁p.le h₂p.le hh₁ hh₂ hQ f hf hdim hphase' hsmall
    simpa only [rhs, M, _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters.k, _root_.AbcTwoNinths.ExteriorE1.LaurentRadiusParameters.n, Nat.cast_add, Nat.cast_mul] using hu

end

end AbcTwoNinths.ExteriorE1
