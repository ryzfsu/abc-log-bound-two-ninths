/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalPowerClearing

/-!
# Rational Binomial Minor

The module expands a selected rational minor and bounds its coefficients and exponent interval.

## Main results
* `AbcTwoNinths.Basic.attainedExponentInterval`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open scoped BigOperators

set_option autoImplicit false

/--
The rational interpolation matrix has binomial coefficients weighted by powers of two rational numbers.
-/
noncomputable def actualEntry {I : Type*} (a b : ℚ) (k t r s : I → ℕ) (c d : ℕ) :
    Matrix I I ℚ := fun i j => (Nat.choose (r j*d+s j*c) (k i) : ℚ) *
      a^(t i*r j) * b^(t i*s j)

/--
The integer coefficient of a permutation is its sign times the product of its binomial factors.
-/
noncomputable def actualCoeff {I : Type*} [Fintype I] [DecidableEq I]
    (k r s : I → ℕ) (c d : ℕ) (σ : Equiv.Perm I) : ℤ :=
  (↑(Equiv.Perm.sign σ) : ℤ) * ∏ j, (Nat.choose (r j*d+s j*c) (k (σ j)) : ℤ)

/--
Expand the rational binomial determinant as a sum of signed integer coefficients times two rational powers.
-/
theorem actualLeibniz {I : Type*} [Fintype I] [DecidableEq I]
    (a b : ℚ) (k t r s : I → ℕ) (c d : ℕ) :
    (_root_.AbcTwoNinths.Basic.actualEntry a b k t r s c d).det =
      ∑ σ : Equiv.Perm I, (_root_.AbcTwoNinths.Basic.actualCoeff k r s c d σ : ℚ) *
        a^(∑ j, t (σ j)*r j) * b^(∑ j, t (σ j)*s j) := by
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [_root_.AbcTwoNinths.Basic.actualEntry, _root_.AbcTwoNinths.Basic.actualCoeff, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Units.smul_def, zsmul_eq_mul, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
  ac_rfl

/--
A common upper bound on the nodes bounds each absolute coefficient by a product of powers divided by factorials.
-/
theorem actualCoeffBound {I : Type*} [Fintype I] [DecidableEq I]
    (k r s : I → ℕ) (c d M : ℕ) (σ : Equiv.Perm I)
    (hM : ∀ j, r j*d+s j*c ≤ M) :
    ((_root_.AbcTwoNinths.Basic.actualCoeff k r s c d σ).natAbs : ℝ) ≤
      ∏ j, (M : ℝ)^(k j) / ((k j).factorial : ℝ) := by
  have hs : (↑(Equiv.Perm.sign σ) : ℤ).natAbs = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  calc
    _ = ∏ j, (Nat.choose (r j*d+s j*c) (k (σ j)) : ℝ) := by
      unfold _root_.AbcTwoNinths.Basic.actualCoeff
      rw [Int.natAbs_mul, hs, one_mul, ← Nat.cast_prod]
      simp
      positivity
    _ ≤ ∏ j, (M : ℝ)^(k (σ j)) / ((k (σ j)).factorial : ℝ) := by
      apply Finset.prod_le_prod₀ (fun j _ => by positivity)
      intro j _
      calc
        _ ≤ (M.choose (k (σ j)) : ℝ) := by exact_mod_cast Nat.choose_le_choose (k (σ j)) (hM j)
        _ ≤ _ := Nat.choose_le_pow_div _ _
    _ = _ := Equiv.prod_comp σ (fun j => (M : ℝ)^(k j) / ((k j).factorial : ℝ))

/--
Clearing both rational powers gives an integer equal to an explicit multiple of the determinant with a height bound.
-/
theorem selectedMinorBound {I : Type*} [Fintype I] [DecidableEq I]
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (k t r s : I → ℕ) (c d R S la ua lb ub : ℕ)
    (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (he : ∀ σ : Equiv.Perm I, la ≤ ∑ j, t (σ j)*r j ∧ (∑ j, t (σ j)*r j) ≤ ua)
    (hf : ∀ σ : Equiv.Perm I, lb ≤ ∑ j, t (σ j)*s j ∧ (∑ j, t (σ j)*s j) ≤ ub) :
    ∃ Z : ℤ, (Z : ℚ) = ((a^la)⁻¹ * (a.den : ℚ)^(ua-la)) *
        ((b^lb)⁻¹ * (b.den : ℚ)^(ub-lb)) * (_root_.AbcTwoNinths.Basic.actualEntry a b k t r s c d).det ∧
      (Z.natAbs : ℝ) ≤ (Fintype.card I).factorial *
        (∏ j, ((R*d+S*c : ℕ) : ℝ)^(k j) / ((k j).factorial : ℝ)) *
        Real.exp ((ua-la : ℕ) * Real.log (max (a.num.natAbs : ℝ) (a.den : ℝ)) +
          (ub-lb : ℕ) * Real.log (max (b.num.natAbs : ℝ) (b.den : ℝ))) := by
  rw [_root_.AbcTwoNinths.Basic.actualLeibniz]
  simpa only [Finset.card_univ, Fintype.card_perm] using
    _root_.AbcTwoNinths.Basic.clearTwoPowerSum Finset.univ a b ha hb la ua lb ub
      (fun σ : Equiv.Perm I => ∑ j, t (σ j)*r j)
      (fun σ : Equiv.Perm I => ∑ j, t (σ j)*s j)
      (_root_.AbcTwoNinths.Basic.actualCoeff k r s c d)
      (∏ j, ((R*d+S*c : ℕ) : ℝ)^(k j) / ((k j).factorial : ℝ))
      (fun σ _ => he σ) (fun σ _ => hf σ)
      (fun σ _ => _root_.AbcTwoNinths.Basic.actualCoeffBound k r s c d _ σ
        (fun j => Nat.add_le_add (Nat.mul_le_mul_right _ (hr j)) (Nat.mul_le_mul_right _ (hs j))))
      (Finset.prod_nonneg (fun j _ => by positivity))

/--
Pairwise differences bounded above by a common width place all permutation exponents in a natural interval of that width or less.
-/
theorem attainedExponentInterval {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I → ℕ) (W : ℕ)
    (hw : ∀ σ τ, e σ ≤ e τ + W) :
    ∃ l u : ℕ, (∀ σ, l ≤ e σ ∧ e σ ≤ u) ∧ u-l ≤ W := by
  let T := Finset.univ.image e
  have hT : T.Nonempty := ⟨e (Equiv.refl I), Finset.mem_image.mpr
    ⟨Equiv.refl I, Finset.mem_univ _, rfl⟩⟩
  have hmem (σ : Equiv.Perm I) : e σ ∈ T :=
    Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp (Finset.max'_mem T hT)
  obtain ⟨τ, _, hτ⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  refine ⟨T.min' hT, T.max' hT, fun ρ => ⟨Finset.min'_le T _ (hmem ρ),
    Finset.le_max' T _ (hmem ρ)⟩, ?_⟩
  rw [← hσ, ← hτ]
  exact Nat.sub_le_iff_le_add.mpr (by simpa only [Nat.add_comm W] using hw σ τ)

end

end AbcTwoNinths.Basic
