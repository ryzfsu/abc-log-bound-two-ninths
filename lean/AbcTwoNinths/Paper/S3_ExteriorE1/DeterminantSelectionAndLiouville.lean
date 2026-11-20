/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RealInterpolationDeterminant
public import AbcTwoNinths.Basic.RationalDepthReduction

/-!
# Determinant Selection And Liouville

The module either selects a nonzero interpolation determinant or obtains an elementary Liouville bound for the linear form. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.selectOrLiouville`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE1

section



private theorem invLeAbsLogDiv (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hne : n ≠ d) : (max n d : ℝ)⁻¹ ≤ |Real.log ((n : ℝ) / d)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have step (a b : ℕ) (ha : (0 : ℝ) < a) (hb : (0 : ℝ) < b) (hab : a < b) :
      (b : ℝ)⁻¹ ≤ -Real.log ((a : ℝ) / b) := by
    have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    have hdiv : (1 : ℝ) / b ≤ 1 - (a : ℝ) / b := by
      rw [le_sub_iff_add_le, ← add_div]
      exact (div_le_one hb).2 (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [← one_div]
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_right (show (n : ℝ) ≤ d by exact_mod_cast h.le)]
    exact (step n d hn' hd' h).trans (neg_le_abs _)
  · rw [max_eq_left (show (d : ℝ) ≤ n by exact_mod_cast h.le)]
    have hs := step d n hd' hn' h
    rw [Real.log_div hd'.ne' hn'.ne'] at hs
    rw [Real.log_div hn'.ne' hd'.ne']
    exact hs.trans (by rw [neg_sub]; exact le_abs_self _)

/--
Bounds the negative logarithm of a nonzero real two-logarithm form by the weighted input heights.
-/
theorem liouvilleTwoLogBound (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (η₁ η₂ : ℝ)
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (hind : ∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hh₁ : Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ) ≤ η₁)
    (hh₂ : Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ) ≤ η₂) :
    -Real.log |(b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)| ≤
      (b₁ : ℝ) * η₁ + (b₂ : ℝ) * η₂ := by
  have hq₁' : (0 : ℚ) < q₁ := zero_lt_one.trans hq₁
  have hq₂' : (0 : ℚ) < q₂ := zero_lt_one.trans hq₂
  have ratRep (q : ℚ) (hq : 0 < q) :
      0 < q.num.natAbs ∧ 0 < q.den ∧ (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have hcast : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum.le]
    exact ⟨by omega, q.den_pos, by rw [hcast, Rat.cast_def]⟩
  obtain ⟨hn₁, hd₁, hr₁⟩ := ratRep q₁ hq₁'
  obtain ⟨hn₂, hd₂, hr₂⟩ := ratRep q₂ hq₂'
  let n := q₂.num.natAbs ^ b₂ * q₁.den ^ b₁
  let d := q₂.den ^ b₂ * q₁.num.natAbs ^ b₁
  have hn : 0 < n := by dsimp [n]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have heq : (q₂ : ℝ) ^ b₂ / (q₁ : ℝ) ^ b₁ = (n : ℝ) / d := by
    simp only [n, d, Nat.cast_mul, Nat.cast_pow, hr₁, hr₂, div_pow, div_div_eq_mul_div]
    rw [div_mul_eq_mul_div, div_div]
  have hne : n ≠ d := by
    intro e
    have he : (q₂ : ℝ) ^ b₂ = (q₁ : ℝ) ^ b₁ := by
      apply (div_eq_one_iff_eq (pow_ne_zero _ (by exact_mod_cast hq₁'.ne'))).mp
      rw [heq, e, div_self (by exact_mod_cast hd.ne')]
    have he' : q₂ ^ b₂ = q₁ ^ b₁ := by exact_mod_cast he
    have hrel : q₁ ^ (-(b₁ : ℤ)) * q₂ ^ (b₂ : ℤ) = 1 := by
      rw [zpow_neg, zpow_natCast, zpow_natCast, he', inv_mul_cancel₀ (pow_ne_zero _ hq₁'.ne')]
    obtain ⟨hzero₁, hzero₂⟩ := hind _ _ hrel
    have hb₁' : (0 : ℤ) < b₁ := by exact_mod_cast hb₁
    have hb₂' : (0 : ℤ) < b₂ := by exact_mod_cast hb₂
    have hsum := add_pos hb₁' hb₂'
    rw [neg_eq_zero.mp hzero₁, hzero₂, add_zero] at hsum
    exact (lt_irrefl 0) hsum
  have hlog : (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ) =
      Real.log ((n : ℝ) / d) := by
    rw [← heq, Real.log_div (pow_ne_zero _ (by exact_mod_cast hq₂'.ne'))
      (pow_ne_zero _ (by exact_mod_cast hq₁'.ne')), Real.log_pow, Real.log_pow]
  have expBound (a b : ℕ) (ha : 0 < a) (t : ℝ)
      (h : Real.log ((max a b : ℕ) : ℝ) ≤ t) :
      (a : ℝ) ≤ Real.exp t ∧ (b : ℝ) ≤ Real.exp t := by
    have hp : (0 : ℝ) < (max a b : ℕ) := by exact_mod_cast ha.trans_le (le_max_left a b)
    have hm := Real.exp_le_exp.mpr h
    rw [Real.exp_log hp] at hm
    exact ⟨(by exact_mod_cast le_max_left a b : (a : ℝ) ≤ (max a b : ℕ)).trans hm,
      (by exact_mod_cast le_max_right a b : (b : ℝ) ≤ (max a b : ℕ)).trans hm⟩
  obtain ⟨hN₁, hD₁⟩ := expBound _ _ hn₁ _ hh₁
  obtain ⟨hN₂, hD₂⟩ := expBound _ _ hn₂ _ hh₂
  have prodBound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (ha' : a ≤ Real.exp η₂) (hb' : b ≤ Real.exp η₁) :
      a ^ b₂ * b ^ b₁ ≤ Real.exp ((b₁ : ℝ) * η₁ + (b₂ : ℝ) * η₂) := by
    rw [add_comm, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
    gcongr
  have hm : (max n d : ℝ) ≤ Real.exp ((b₁ : ℝ) * η₁ + (b₂ : ℝ) * η₂) := by
    rw [max_le_iff]
    constructor
    · simp only [n, Nat.cast_mul, Nat.cast_pow]
      exact prodBound _ _ (by positivity) (by positivity) hN₂ hD₁
    · simp only [d, Nat.cast_mul, Nat.cast_pow]
      exact prodBound _ _ (by positivity) (by positivity) hD₂ hN₁
  have hmpos : (0 : ℝ) < max (n : ℝ) (d : ℝ) :=
    (show (0 : ℝ) < n by exact_mod_cast hn).trans_le (le_max_left _ _)
  have hlow := (inv_anti₀ hmpos hm).trans (invLeAbsLogDiv n d hn hd hne)
  rw [← Real.exp_neg] at hlow
  have hloglow := Real.log_le_log (Real.exp_pos _) hlow
  rw [Real.log_exp] at hloglow
  rw [hlog]
  linarith

/--
Either the coprime exponents fit the second rectangle or the combined rectangle supports a nonzero interpolation determinant. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem selectOrLiouville {L J R₁ S₁ R₂ S₂ b₁ b₂ : ℕ}
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (hind : ∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hcop : b₁.Coprime b₂)
    (hcard₁ : L ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R₁ S₁))
    (hcard₂ : L * J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R₂ S₂)) :
    (b₁ ≤ R₂ ∧ b₂ ≤ S₂) ∨
    ∃ f : (Fin (J + 1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle (R₁ + R₂) (S₁ + S₂),
      (Matrix.of fun k j : Fin (J + 1) × Fin L =>
        (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
          (q₁ : ℝ) ^ (k.2.val * (f j).1.val) *
          (q₂ : ℝ) ^ (k.2.val * (f j).2.val)).det ≠ 0 := by
  classical
  have hn₁ : q₁ ≠ 0 := (zero_lt_one.trans hq₁).ne'
  have hn₂ : q₂ ≠ 0 := (zero_lt_one.trans hq₂).ne'
  by_cases hz : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R₂) (S := S₂) b₁ b₂)
  · apply Or.inr
    apply _root_.AbcTwoNinths.ExteriorE1.realInterpolationDeterminant q₁ q₂ hn₁ hn₂
    · rwa [Finset.card_image_of_injective _ (_root_.AbcTwoNinths.Basic.nodeWInjective hn₁ hn₂ hind), Finset.card_univ]
    · rwa [Finset.card_image_of_injective _ hz, Finset.card_univ]
  · unfold Function.Injective at hz
    push Not at hz
    obtain ⟨i, j, h, hne⟩ := hz
    apply Or.inl
    refine _root_.AbcTwoNinths.Basic.duplicateBounds hcop hb₁ hb₂
      (Nat.le_of_lt_succ i.1.isLt) (Nat.le_of_lt_succ j.1.isLt)
      (Nat.le_of_lt_succ i.2.isLt) (Nat.le_of_lt_succ j.2.isLt) ?_ h
    intro e
    exact hne (Prod.ext (Fin.ext (congrArg Prod.fst e)) (Fin.ext (congrArg Prod.snd e)))

end

end AbcTwoNinths.ExteriorE1
