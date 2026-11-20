/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PowerLiftingValuation
public import AbcTwoNinths.Basic.TwoLogarithmDeterminantBound

/-!
# Normalized Two Logarithm Estimate

The module derives the normalized two-logarithm estimate from the grid estimate.

## Main results
* `AbcTwoNinths.Basic.normalizedFromGrid`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section
open Real

/--
The uniform grid alternative for coprime exponents and positive grid dimensions at an odd prime.
-/
def NativeGrid : Prop :=
  ∀ (p c d L J : ℕ) (a b : ℚ) (A B : ℝ), p.Prime → 2 < p →
    _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a → _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b → _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b → c.Coprime d → 0 < c → 0 < d →
    0 < L → 0 < J → 1 ≤ A → 1 ≤ B →
    _root_.AbcTwoNinths.Basic.padicRationalHeight a ≤ A * log p → _root_.AbcTwoNinths.Basic.padicRationalHeight b ≤ B * log p →
    let m0 := (padicValRat p (a^c-b^d) : ℝ)
    let N := ((J : ℝ)+1)*L
    m0 < 1+2*sqrt ((J : ℝ)*L*(A*B)) ∨
      (N ≤ m0 → ∃ M C : ℝ, 0 < M ∧
        M ≤ (1+sqrt J)*sqrt ((L : ℝ)*(A*B))*((c : ℝ)/B+(d : ℝ)/A) ∧
        C ≤ (1+sqrt J)*sqrt ((L : ℝ)*(A*B)) ∧
        ((J : ℝ)+1)*((L : ℝ)-1) <
          2*log N/log p+(J : ℝ)*(log (exp 2*M/J)/log p)+(L : ℝ)*C)

/--
The primitive grid bound implies the valuation estimate with constant 147 for arbitrary positive exponents.
-/
theorem normalizedFromGrid (native : _root_.AbcTwoNinths.Basic.NativeGrid)
    (p m n : ℕ) (a b : ℚ) (A B : ℝ)
    (hp : p.Prime) (hp' : 2 < p) (ha : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b)
    (hi : _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b) (hm : 0 < m) (hn : 0 < n)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hha : _root_.AbcTwoNinths.Basic.padicRationalHeight a ≤ A*log p)
    (hhb : _root_.AbcTwoNinths.Basic.padicRationalHeight b ≤ B*log p) :
    (padicValRat p (a^m-b^n) : ℝ) ≤ 147*(_root_.AbcTwoNinths.Basic.unboundedD p m n A B ^ 2*(A*B)) := by
  let D := _root_.AbcTwoNinths.Basic.unboundedD p m n A B
  let U := (m : ℝ)/B+(n : ℝ)/A
  have hD : 4 ≤ D := le_max_left _ _
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hAB : 1 ≤ A*B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hDA : 4 ≤ D*(A*B) := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hAB)]
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  have hell : 1 ≤ log (p : ℝ) := ((lt_log_iff_exp_lt (by linarith : (0:ℝ)<p)).2
    (exp_one_lt_three.trans_le hp3)).le
  have hU : 0 < U := by dsimp [U]; positivity
  have hlog : log (exp 2*U)/log p ≤ D := by
    rw [log_mul (exp_ne_zero _) hU.ne', log_exp]
    exact le_max_right _ _
  let L : ℕ := ⌈4*D⌉₊
  let J : ℕ := ⌈32*D*(A*B)⌉₊
  have hLl : 4*D ≤ (L : ℝ) := Nat.le_ceil _
  have hLu : (L : ℝ) ≤ 17/4*D := by
    have h : (L : ℝ) < 4*D+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hJl : 32*D*(A*B) ≤ (J : ℝ) := Nat.le_ceil _
  have hJu : (J : ℝ) ≤ 33*D*(A*B) := by
    have h : (J : ℝ) < 32*D*(A*B)+1 := Nat.ceil_lt_add_one (by nlinarith)
    nlinarith
  have hL : 0<L := by exact_mod_cast (show (0:ℝ)<L by linarith)
  have hJ : 0<J := by exact_mod_cast (show (0:ℝ)<J by nlinarith)
  obtain ⟨c,d,hc,hd,hcd,hcm,hdn,hred⟩ :=
    _root_.AbcTwoNinths.Basic.unboundedLteReduce p m n a b A B hp hp' ha hb hi hm hn hA hB
  have hmono : (c:ℝ)/B+(d:ℝ)/A ≤ U := add_le_add
    (div_le_div_of_nonneg_right (by exact_mod_cast hcm) hBp.le)
    (div_le_div_of_nonneg_right (by exact_mod_cast hdn) hAp.le)
  apply hred.trans
  apply _root_.AbcTwoNinths.Basic.depthBoundOfGridAndMinor D (A*B) (log p) U L J _ _ _
    hD hAB hell hU hlog hLl hLu hJl hJu rfl (by dsimp [D]; ring_nf; rfl)
  rcases native p c d L J a b A B hp hp' ha hb hi hcd hc hd hL hJ hA hB hha hhb with h | h
  · exact Or.inl h
  · right
    intro hh
    obtain ⟨M,C,hM,hMu,hCu,hdet⟩ := h hh
    exact ⟨M,C,hM,hMu.trans (mul_le_mul_of_nonneg_left hmono (by positivity)),hCu,hdet⟩

end

end AbcTwoNinths.Basic
