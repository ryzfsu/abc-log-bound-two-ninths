/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic

/-!
# Integer Determinant Bounds

The module clears row denominators and proves nonvanishing and valuation bounds for the resulting integer determinant. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.sameMinorLogUpper`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section

open scoped BigOperators

private theorem notDvdDenOfValZero {p : ℕ} [hp : Fact p.Prime] {w : ℚ}
    (hw : padicValRat p w = 0) : ¬ p ∣ w.den := by
  intro hd
  have hc : w.num.natAbs.Coprime w.den := w.reduced
  have hn : ¬ p ∣ w.num.natAbs := by
    intro h
    have hg := Nat.dvd_gcd h hd
    rw [hc.gcd_eq_one] at hg
    exact hp.out.not_dvd_one hg
  have hv : padicValNat p w.den ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero w.den_ne_zero).mp hd
  simp only [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hn,
    Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero] at hw
  exact hv hw

private theorem valProdDen {p : ℕ} [hp : Fact p.Prime]
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, padicValRat p (w i) = 0) :
    padicValRat p (∏ i, ((w i).den : ℚ)) = 0 := by
  classical
  have hunit (i : ι) : padicValRat p ((w i).den : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (notDvdDenOfValZero (hw i)),
      Nat.cast_zero]
  suffices h : ∀ s : Finset ι, padicValRat p (∏ i ∈ s, ((w i).den : ℚ)) = 0 by
    exact h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, padicValRat.mul (by exact_mod_cast (w i).den_ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_ne_zero),
      hunit, ih, add_zero]

/--
Forms the two binomial column blocks at the selected rows, weighting the second block by the row value. This is used in Section 7 of the paper.
-/
def rationalMinor {K : ℕ} (y : Fin K ⊕ Fin K → ℤ) (w : Fin K ⊕ Fin K → ℚ) :
    Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℚ :=
  Matrix.of fun i j =>
    match j with
    | .inl k => ((Ring.choose (y i) k.val : ℤ) : ℚ)
    | .inr k => ((Ring.choose (y i) k.val : ℤ) : ℚ) * w i

/--
Clears the reduced denominator of the rational row value in each row of the minor. This is used in Section 7 of the paper.
-/
def integerMinor {K : ℕ} (y : Fin K ⊕ Fin K → ℤ) (w : Fin K ⊕ Fin K → ℚ) :
    Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℤ :=
  Matrix.of fun i j =>
    match j with
    | .inl k => (w i).den * Ring.choose (y i) k.val
    | .inr k => (w i).num * Ring.choose (y i) k.val

/-- Each cleared entry equals its rational entry multiplied by the row denominator. -/
theorem castIntegerMinorEntry {K : ℕ} (y : Fin K ⊕ Fin K → ℤ)
    (w : Fin K ⊕ Fin K → ℚ) (i j : Fin K ⊕ Fin K) :
    ((_root_.AbcTwoNinths.Terminal.integerMinor y w i j : ℤ) : ℚ) = (w i).den * _root_.AbcTwoNinths.Terminal.rationalMinor y w i j := by
  cases j with
  | inl k => simp [_root_.AbcTwoNinths.Terminal.integerMinor, _root_.AbcTwoNinths.Terminal.rationalMinor]
  | inr k =>
    change ((w i).num * Ring.choose (y i) k.val : ℤ) =
      ((w i).den : ℚ) * ((Ring.choose (y i) k.val : ℤ) * w i)
    push_cast
    rw [mul_comm ((Ring.choose (y i) k.val : ℤ) : ℚ) (w i),
      ← mul_assoc, Rat.den_mul_eq_num]

/--
Casting the cleared determinant gives the rational determinant times the product of row denominators.
-/
theorem castIntegerMinorDet {K : ℕ} (y : Fin K ⊕ Fin K → ℤ)
    (w : Fin K ⊕ Fin K → ℚ) :
    ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det : ℚ) = (∏ i, ((w i).den : ℚ)) * (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det := by
  classical
  rw [show ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det : ℚ) = _ from
    (Int.castRingHom ℚ).map_det (_root_.AbcTwoNinths.Terminal.integerMinor y w), ← Matrix.det_mul_column]
  congr 1
  ext i j
  exact _root_.AbcTwoNinths.Terminal.castIntegerMinorEntry y w i j

/-- Clearing rows of valuation zero preserves nonvanishing and the valuation of the determinant. -/
theorem integerMinorNonzeroAndValuation {p K : ℕ} [Fact p.Prime]
    (y : Fin K ⊕ Fin K → ℤ) (w : Fin K ⊕ Fin K → ℚ)
    (hw : ∀ i, padicValRat p (w i) = 0) (hM : (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det ≠ 0) :
    (_root_.AbcTwoNinths.Terminal.integerMinor y w).det ≠ 0 ∧
      (padicValInt p (_root_.AbcTwoNinths.Terminal.integerMinor y w).det : ℤ) = padicValRat p (_root_.AbcTwoNinths.Terminal.rationalMinor y w).det := by
  classical
  have hprod : (∏ i, ((w i).den : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (w i).den_ne_zero
  have hnz : ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det : ℚ) ≠ 0 := by
    rw [_root_.AbcTwoNinths.Terminal.castIntegerMinorDet]
    exact mul_ne_zero hprod hM
  refine ⟨by exact_mod_cast hnz, ?_⟩
  rw [← padicValRat.of_int, _root_.AbcTwoNinths.Terminal.castIntegerMinorDet, padicValRat.mul hprod hM,
    valProdDen w hw, zero_add]

/--
For a nonzero integer its valuation times the logarithm of the prime bounds its logarithmic absolute value from below.
-/
theorem logNatAbsGeValuation {p : ℕ} [Fact p.Prime] {D : ℤ} (hD : D ≠ 0) :
    (padicValInt p D : ℝ) * Real.log (p : ℝ) ≤ Real.log (D.natAbs : ℝ) := by
  have hn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hpos : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpow : p ^ padicValInt p D ≤ D.natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have hpowR : (p : ℝ) ^ padicValInt p D ≤ (D.natAbs : ℝ) := by exact_mod_cast hpow
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hpos _) hpowR

/--
The multiplicative height of a rational is the maximum of its absolute reduced numerator and its reduced denominator. This is used in Section 7 of the paper.
-/
def rowHeightMax (w : ℚ) : ℕ := max w.num.natAbs w.den

/-- The multiplicative height of a rational is positive. -/
theorem rowHeightMaxPos (w : ℚ) : 0 < _root_.AbcTwoNinths.Terminal.rowHeightMax w :=
  w.den_pos.trans_le (le_max_right _ _)

/-- Bounds each cleared entry by its row height times the uniform binomial envelope. -/
theorem integerMinorEntryBound {K : ℕ} (y : Fin K ⊕ Fin K → ℤ)
    (w : Fin K ⊕ Fin K → ℚ) {B : ℝ}
    (hb : ∀ i (k : Fin K), |((Ring.choose (y i) k.val : ℤ) : ℝ)| ≤ B)
    (i j : Fin K ⊕ Fin K) :
    |(_root_.AbcTwoNinths.Terminal.integerMinor y w i j : ℝ)| ≤ (_root_.AbcTwoNinths.Terminal.rowHeightMax (w i) : ℝ) * B := by
  have hd : (w i).den ≤ _root_.AbcTwoNinths.Terminal.rowHeightMax (w i) := le_max_right _ _
  have hn : (w i).num.natAbs ≤ _root_.AbcTwoNinths.Terminal.rowHeightMax (w i) := le_max_left _ _
  cases j with
  | inl k =>
    change |((((w i).den : ℤ) * Ring.choose (y i) k.val : ℤ) : ℝ)| ≤ _
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((w i).den : ℝ))]
    exact mul_le_mul (by exact_mod_cast hd) (hb i k) (abs_nonneg _) (by positivity)
  | inr k =>
    change |(((w i).num * Ring.choose (y i) k.val : ℤ) : ℝ)| ≤ _
    push_cast
    rw [abs_mul, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact mul_le_mul (by exact_mod_cast hn) (hb i k) (abs_nonneg _) (by positivity)

/--
Bounds the logarithm of the absolute cleared determinant by the row log heights, the log factorial and the binomial contribution. This is used in Section 7 of the paper.
-/
theorem sameMinorLogUpper {K : ℕ} (y : Fin K ⊕ Fin K → ℤ)
    (w : Fin K ⊕ Fin K → ℚ) {B : ℝ} (hB : 0 < B)
    (hb : ∀ i (k : Fin K), |((Ring.choose (y i) k.val : ℤ) : ℝ)| ≤ B)
    (hD : (_root_.AbcTwoNinths.Terminal.integerMinor y w).det ≠ 0) :
    Real.log ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det.natAbs : ℝ) ≤
      (∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (w i) : ℝ)) +
        Real.log ((2 * K).factorial : ℝ) + (2 * K : ℝ) * Real.log B := by
  classical
  let M := (_root_.AbcTwoNinths.Terminal.integerMinor y w).map (Int.castRingHom ℝ)
  let R : ℝ := ∏ i, (_root_.AbcTwoNinths.Terminal.rowHeightMax (w i) : ℝ)
  let N := 2 * K
  have hcard : Fintype.card (Fin K ⊕ Fin K) = N := by simp [N, two_mul]
  have hperms : Fintype.card (Equiv.Perm (Fin K ⊕ Fin K)) = N.factorial := by
    rw [← Nat.card_eq_fintype_card, Nat.card_perm, Nat.card_eq_fintype_card, hcard]
  have hprod (σ : Equiv.Perm (Fin K ⊕ Fin K)) :
      |∏ i, M i (σ i)| ≤ R * B ^ N := by
    calc
      |∏ i, M i (σ i)| = ∏ i, |M i (σ i)| := Finset.abs_prod _ _
      _ ≤ ∏ i, (_root_.AbcTwoNinths.Terminal.rowHeightMax (w i) : ℝ) * B :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => _root_.AbcTwoNinths.Terminal.integerMinorEntryBound y w hb i (σ i))
      _ = R * B ^ N := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  have hsum : |M.det| ≤ (N.factorial : ℝ) * (R * B ^ N) := by
    rw [← Matrix.det_transpose M, Matrix.det_apply]
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin K ⊕ Fin K),
          |Equiv.Perm.sign σ • ∏ i, M i (σ i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Equiv.Perm (Fin K ⊕ Fin K), R * B ^ N := by
        apply Finset.sum_le_sum
        intro σ _
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · simpa [h] using hprod σ
        · simpa [h] using hprod σ
      _ = _ := by simp [hperms]
  have hcast : M.det = ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [hcast, ← Int.cast_abs, ← Nat.cast_natAbs] at hsum
  have hR : 0 < R := Finset.prod_pos fun i _ => by exact_mod_cast _root_.AbcTwoNinths.Terminal.rowHeightMaxPos (w i)
  have hfac : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hlog := Real.log_le_log (show 0 < ((_root_.AbcTwoNinths.Terminal.integerMinor y w).det.natAbs : ℝ) from by
    exact_mod_cast Int.natAbs_pos.mpr hD) hsum
  rw [Real.log_mul hfac.ne' (mul_pos hR (pow_pos hB _)).ne',
      Real.log_mul hR.ne' (pow_pos hB _).ne', Real.log_pow] at hlog
  have hlogR : Real.log R = ∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (w i) : ℝ) :=
    Real.log_prod fun i _ => by exact_mod_cast (_root_.AbcTwoNinths.Terminal.rowHeightMaxPos (w i)).ne'
  rw [hlogR] at hlog
  simpa [N, add_left_comm, add_comm, add_assoc, Nat.cast_mul] using hlog

end

end AbcTwoNinths.Terminal
