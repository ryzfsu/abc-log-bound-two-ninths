/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Diamond Row Height Sum

The module bounds the sum of interpolation row heights for sites in the lattice ball. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.ballRowSum`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

open Finset

section

/--
Quadratic counting bounds on nested balls bound the total height of any selected subset by a finite layer sum. This is used in Section 7 of the paper.
-/
theorem ballRowSum {ι : Type*} (ball : ℝ → Finset ι) (g : ι → ℝ)
    {A δ S : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ δ) (hS : 0 < S)
    (mono : Monotone ball) (height : ∀ r i, i ∈ ball r → g i ≤ r)
    (nonneg : ∀ i ∈ ball S, 0 ≤ g i)
    (lower : ∀ r ≥ 0, A * (max (r-δ) 0)^2 ≤ ((ball r).card : ℝ))
    (upper : ((ball S).card : ℝ) ≤ A * (S+δ)^2)
    (J : ℕ) (hJ : 0 < J) (F : Finset ι) (hF : F ⊆ ball S) :
    ∑ i ∈ F, g i ≤ A * (S*(S+δ)^2 - S^3/3 + S^3/(2*J) + δ*S^2) := by
  classical
  let d := S / J
  have jpos : 0 < (J : ℝ) := by exact_mod_cast hJ
  have dp : 0 ≤ d := (div_pos hS jpos).le
  have endpt : (J : ℝ)*d = S := by dsimp [d]; field_simp
  let P := fun r : ℝ => ∑ i ∈ ball S, max (r - g i) 0
  have step (r : ℝ) (hr : r ≤ S) :
      ((ball r).card : ℝ)*d ≤ P (r+d) - P r := by
    have sub := mono hr
    have b : ∑ i ∈ ball r, d ≤ ∑ i ∈ ball S,
        (max (r+d-g i) 0 - max (r-g i) 0) := by
      apply le_trans (Finset.sum_le_sum (f := fun _ => d)
        (g := fun i => max (r+d-g i) 0 - max (r-g i) 0) ?_)
      · apply Finset.sum_le_sum_of_subset_of_nonneg sub
        intro i _ _
        exact sub_nonneg.mpr (max_le_max (by linarith : r-g i ≤ r+d-g i) le_rfl)
      · intro i hi
        have hh := height r i hi
        rw [max_eq_left (by linarith : 0 ≤ r+d-g i), max_eq_left (by linarith : 0 ≤ r-g i)]
        linarith
    simpa [P, Finset.sum_sub_distrib] using b
  have aux (k : ℕ) (hk : k ≤ J) :
      A * (d^3*((k:ℝ)^3/3-(k:ℝ)^2/2) - δ*d^2*(k:ℝ)^2) ≤ P (k*d) := by
    induction k with
    | zero => simpa [P] using (Finset.sum_nonneg (s := ball S)
          (f := fun i => max (0-g i) 0) (fun i _ => le_max_right _ _))
    | succ k ih =>
      have kj := Nat.le_of_succ_le hk
      have pre := ih kj
      have rle : (k:ℝ)*d ≤ S := endpt ▸ mul_le_mul_of_nonneg_right (by exact_mod_cast kj) dp
      have st := step ((k:ℝ)*d) rle
      have rr : 0 ≤ (k:ℝ)*d := by positivity
      have lo := lower ((k:ℝ)*d) rr
      have sq : ((k:ℝ)*d)^2 - 2*δ*((k:ℝ)*d) ≤ (max ((k:ℝ)*d-δ) 0)^2 := by
        rcases le_total δ ((k:ℝ)*d) with h | h
        · rw [max_eq_left (by linarith)]; nlinarith [sq_nonneg δ]
        · rw [max_eq_right (by linarith)]; nlinarith [mul_nonneg rr (sub_nonneg.mpr h), sq_nonneg ((k:ℝ)*d)]
      have inc := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left sq hA).trans lo) dp
      push_cast
      rw [add_mul, one_mul]
      nlinarith [mul_nonneg hA (pow_nonneg dp 3), mul_nonneg (mul_nonneg hA hd) (sq_nonneg d)]
  have total := aux J le_rfl
  rw [endpt] at total
  have pe : P S = ((ball S).card : ℝ)*S - ∑ i ∈ ball S, g i := by
    simp only [P, Finset.sum_congr rfl (fun i hi => max_eq_left (sub_nonneg.mpr (height S i hi))),
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [pe] at total
  have ext := Finset.sum_le_sum_of_subset_of_nonneg hF (fun i hi _ => nonneg i hi)
  apply ext.trans
  have u := mul_le_mul_of_nonneg_right upper hS.le
  have ident : d^3*((J:ℝ)^3/3-(J:ℝ)^2/2) - δ*d^2*(J:ℝ)^2 =
      S^3/3 - S^3/(2*J) - δ*S^2 := by
    dsimp [d]; field_simp
  rw [ident] at total
  linarith only [total, u]

end

end AbcTwoNinths.Terminal
