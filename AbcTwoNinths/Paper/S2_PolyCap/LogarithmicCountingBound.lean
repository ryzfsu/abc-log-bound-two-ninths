/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Logarithmic Counting Bound

The module turns the ceiling bound for the counting parameter into the logarithmic inequality for the polynomial cap. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.masterRow`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

/--
Bound each rounded counting factor by the product of an exponential constant, the cube of the support scale, and the square of the log parameter.
-/
theorem ceilingBound {r s : ℕ} {W Z L : ℝ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hrW : (r : ℝ) ≤ 2 * W) (hsW : (s : ℝ) ≤ 2 * W)
    (hW : 1 < W) (hZ : 1 ≤ Z) (hL : 1/2 ≤ L) (hLW : L ≤ W) :
    (⌈1920000 * (r : ℝ) * Z^2 * (s : ℝ) * L⌉₊ : ℝ) ≤ exp 24 * W^3 * Z^2 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  let x : ℝ := 1920000 * r * Z^2 * s * L
  have h1 : 1 ≤ x := by
    have hh : (1920000 : ℝ) * 1 * 1^2 * 1 * (1/2) ≤ x := by
      dsimp [x]
      gcongr
    linarith
  have h24 : (15360000 : ℝ) ≤ exp 24 := by
    calc
      _ ≤ (2:ℝ)^24 := by norm_num
      _ ≤ exp 1 ^ (24:ℕ) := by
        gcongr
        linarith [add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
      _ = _ := by rw [← exp_nat_mul]; norm_num
  calc
    _ ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
    _ ≤ 2 * x := by linarith
    _ = 3840000 * (r : ℝ) * Z^2 * s * L := by dsimp [x]; ring
    _ ≤ 3840000 * (2 * W) * Z^2 * (2 * W) * W := by gcongr
    _ = 15360000 * W^3 * Z^2 := by ring
    _ ≤ _ := by gcongr

/--
A product estimate for the pivot exponent implies the logarithmic counting inequality for the polynomial cap. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem masterRow {ι : Type*} [Fintype ι] {E H W p : ℝ} (r : ℕ)
    (hH : 2 < H) (hW : 1 < W) (hr : (r : ℝ) ≤ 2 * W) (hr0 : 1 ≤ r)
    (hE : 0 < E) (_hp0 : 0 ≤ p) (hp : p ≤ exp W) (hsize : H < 4 * r * W * E)
    (L : ι → ℝ) (hL : ∀ j, 1/2 ≤ L j) (hLW : ∀ j, L j ≤ W)
    (hupper : E ≤ p * ∏ j, (⌈1920000 * (r : ℝ) * (1 + log (20 * H))^2 *
      (Fintype.card ι : ℝ) * L j⌉₊ : ℝ))
    (hs : 1 ≤ Fintype.card ι) (hsW : (Fintype.card ι : ℝ) ≤ 2 * W) :
    let Z := 1 + log (20 * H)
    Z - 2 * (Fintype.card ι : ℝ) * log Z ≤
      9 + 2 * log W + W + (Fintype.card ι : ℝ) * (24 + 3 * log W) := by
  let Z := 1 + log (20 * H)
  let s := Fintype.card ι
  have hZ : 1 ≤ Z := by
    dsimp [Z]
    linarith [log_nonneg (by linarith : 1 ≤ 20*H)]
  have hE' : E ≤ exp W * (exp 24 * W^3 * Z^2)^s := by
    refine hupper.trans ?_
    refine mul_le_mul hp ?_ (by positivity) (exp_pos _).le
    calc
      _ ≤ ∏ _ : ι, exp 24 * W^3 * Z^2 :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ =>
          _root_.AbcTwoNinths.PolyCap.ceilingBound hr0 hs hr hsW hW hZ (hL j) (hLW j))
      _ = _ := by simp [s]
  have h8 : (160 : ℝ) ≤ exp 8 := by
    calc
      _ ≤ (2:ℝ)^8 := by norm_num
      _ ≤ exp 1 ^ (8:ℕ) := by
        gcongr
        linarith [add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
      _ = _ := by rw [← exp_nat_mul]; norm_num
  have hzexp : exp Z ≤ exp 9 * W^2 * E := by
    dsimp [Z]
    rw [exp_add, exp_log (by linarith : 0 < 20*H)]
    have hc : (r : ℝ) * W * E ≤ (2*W)*W*E := by gcongr
    have hh : 20*H ≤ 160 * W^2 * E := by nlinarith
    calc
      _ ≤ exp 1 * (160 * W^2 * E) := by gcongr
      _ ≤ exp 1 * (exp 8 * W^2 * E) := by gcongr
      _ = _ := by rw [show (9:ℝ) = 1 + 8 by norm_num, exp_add]; ring
  have ht := hzexp.trans (mul_le_mul_of_nonneg_left hE' (by positivity))
  have hln := log_le_log (exp_pos Z) ht
  have hZ0 : 0 < Z := by linarith
  have hW0 : 0 < W := by linarith
  rw [log_exp, log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_exp, log_pow,
    log_mul (by positivity) (by positivity), log_exp, log_pow,
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_exp, log_pow, log_pow] at hln
  change Z - 2 * (s : ℝ) * log Z ≤ 9 + 2*log W + W + s*(24+3*log W)
  norm_num at hln
  nlinarith

end

end AbcTwoNinths.PolyCap
