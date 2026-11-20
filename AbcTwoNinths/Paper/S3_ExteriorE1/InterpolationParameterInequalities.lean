/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Interpolation Parameter Inequalities

The module proves the logarithm, grid cardinality, and radius inequalities used to make the real estimate explicit. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.certRhsContradictionFromGrid`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- Seven tenths of the radius is at most the logarithm of the interpolation base divided by e. -/
theorem certLogQ0DivE {r : ℝ} (hr : 0 < r) :
    (7 / 10 : ℝ) * r ≤ Real.log (((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1) := by
  have hpos : (0 : ℝ) < 3 * r / 10 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  have heq : ((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1 =
      Real.exp (r - 1) / (3 * r / 10) := by
    rw [Real.exp_sub]
    field_simp
  rw [heq, Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  linarith

/-- Bounds e, its square root, and the two logarithms used to estimate the interpolation grid. -/
theorem certElementaryTranscendentals :
    (625 / 256 : ℝ) ≤ Real.exp 1 ∧
    Real.exp 1 ≤ (46656 / 15625 : ℝ) ∧
    Real.exp (1 / 2 : ℝ) ≤ (16 / 9 : ℝ) ∧
    Real.log (10 / 3 : ℝ) ≤ (121 / 100 : ℝ) ∧
    Real.log (8333 : ℝ) ≤ (903 / 100 : ℝ) := by
  have hexpinv {x a : ℝ} (ha : 0 < a) (hx : a ≤ 1 - x) :
      Real.exp x ≤ a⁻¹ := by
    have h := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at h
    apply (le_inv_comm₀ (Real.exp_pos _) ha).mpr
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : (5 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
      linarith [Real.add_one_le_exp (1 / 4 : ℝ)]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 4) h 4
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  · have h := hexpinv (x := 1 / 6) (a := 5 / 6) (by norm_num) (by norm_num)
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 6
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  · have h := hexpinv (x := 1 / 4) (a := 3 / 4) (by norm_num) (by norm_num)
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 2
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  · have h := congrArg Real.log (show (10 / 3 : ℝ) ^ 4 = 2 ^ 7 * (625 / 648) by norm_num)
    rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
    linarith [Real.log_two_lt_d9,
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 625 / 648 by norm_num)]
  · have heq : (8333 : ℝ) = 2 ^ 13 * (8333 / 8192) := by norm_num
    have h := congrArg Real.log heq
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
    linarith [Real.log_two_lt_d9,
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8333 / 8192 by norm_num)]

/--
The dimension and radius bounds give an upper bound of 1157 times the scale for the logarithmic interpolation weight.
-/
theorem certFinal1157 {r U : ℝ} {N : ℕ}
    (hr : 1 ≤ r) (hN : 8333 ≤ N)
    (hNU : (N : ℝ) * r ≤ (8333 / 16 : ℝ) * U) :
    Real.log ((N : ℝ) * ((10 / 3 : ℝ) * Real.exp r / r) ^ N) ≤ 1157 * U := by
  have hr0 : 0 < r := by linarith
  have hnr : (8333 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  let q := (10 / 3 : ℝ) * Real.exp r / r
  have hq : 0 < q := by dsimp [q]; positivity
  have hlq : Real.log q ≤ (221 / 100 : ℝ) * r := by
    dsimp [q]
    rw [Real.log_div (by positivity) hr0.ne', Real.log_mul (by norm_num)
      (Real.exp_pos _).ne', Real.log_exp]
    linarith [_root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.2.2.2.1, Real.log_nonneg hr]
  have hln : Real.log (N : ℝ) ≤ (1 / 100 : ℝ) * (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / 8333 by positivity)
    rw [Real.log_div hn0.ne' (by norm_num)] at h
    linarith [_root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.2.2.2.2]
  have hnr' : (N : ℝ) ≤ (N : ℝ) * r := by nlinarith
  have hU : 0 ≤ U := by nlinarith [mul_nonneg hn0.le hr0.le]
  change Real.log ((N : ℝ) * q ^ N) ≤ _
  rw [Real.log_mul hn0.ne' (pow_ne_zero _ hq.ne'), Real.log_pow]
  calc
    _ ≤ (222 / 100 : ℝ) * ((N : ℝ) * r) := by
      nlinarith [mul_le_mul_of_nonneg_left hlq hn0.le]
    _ ≤ (222 / 100 : ℝ) * ((8333 / 16 : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hNU (by norm_num)
    _ ≤ _ := by linarith

/--
Bounds the weighted logarithm of the moment parameter using its ratio to the row index and the base height.
-/
theorem certRhsLog {r D B M j K : ℝ}
    (hr : 0 < r) (hD : 4 ≤ D) (hB : 0 < B) (hM : 0 < M) (hj : 0 < j)
    (hjK : j ≤ K) (hlogB : Real.log B ≤ r * D)
    (hMbound : M / (j * B) ≤ (3 / 20 : ℝ) * r) :
    j * Real.log (Real.exp 2 * M / j) ≤ K * (r * D + (9 / 20 : ℝ) * r) := by
  let t := Real.exp 1 * (M / (j * B))
  have ht : 0 < t := by dsimp [t]; positivity
  have heq : Real.exp 2 * M / j = (Real.exp 1 * t) * B := by
    dsimp [t]
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    field_simp
  have hlog := Real.log_le_sub_one_of_pos ht
  have htbound : t ≤ (9 / 20 : ℝ) * r := by
    calc
      t ≤ Real.exp 1 * ((3 / 20 : ℝ) * r) :=
        mul_le_mul_of_nonneg_left hMbound (Real.exp_pos _).le
      _ ≤ 3 * ((3 / 20 : ℝ) * r) :=
        mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by positivity)
      _ = _ := by ring
  have hlog' : Real.log (Real.exp 2 * M / j) ≤ r * D + (9 / 20 : ℝ) * r := by
    rw [heq, Real.log_mul (by positivity) hB.ne',
      Real.log_mul (Real.exp_pos _).ne' ht.ne', Real.log_exp]
    linarith
  have hU : 0 ≤ r * D + (9 / 20 : ℝ) * r := by positivity
  exact (mul_le_mul_of_nonneg_left hlog' hj.le).trans
    (mul_le_mul_of_nonneg_right hjK hU)

/-- Bounds the two rounded grid dimensions and their product from the real size parameters. -/
theorem certFloorDimensions {D X : ℝ} (hD : 4 ≤ D) (hX : 640 ≤ X) :
    let L := ⌊3 * D⌋₊ + 1
    let J := ⌊X⌋₊
    let K := J + 1
    let N := K * L
    13 ≤ L ∧ 640 ≤ J ∧ 8333 ≤ N ∧
    (11 / 4 : ℝ) * D ≤ (⌊3 * D⌋₊ : ℕ) ∧
    (L : ℝ) ≤ (13 / 12 : ℝ) * (⌊3 * D⌋₊ : ℕ) ∧
    (L : ℝ) ≤ (13 / 4 : ℝ) * D ∧
    X ≤ (641 / 640 : ℝ) * J ∧
    (N : ℝ) ≤ (8333 / 2560 : ℝ) * X * D := by
  dsimp
  have hD0 : 0 ≤ 3 * D := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hfl := Nat.floor_le hD0
  have hful := Nat.lt_floor_add_one (3 * D)
  have hfj := Nat.floor_le hX0
  have hfuj := Nat.lt_floor_add_one X
  have h12 : 12 ≤ ⌊3 * D⌋₊ := (Nat.le_floor_iff hD0).mpr (by norm_num; linarith)
  have h640 : 640 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0).mpr (by exact hX)
  have h12r : (12 : ℝ) ≤ (⌊3 * D⌋₊ : ℕ) := by exact_mod_cast h12
  have h640r : (640 : ℝ) ≤ (⌊X⌋₊ : ℕ) := by exact_mod_cast h640
  refine ⟨by omega, h640, ?_, by linarith, ?_, ?_, by linarith, ?_⟩
  · exact Nat.mul_le_mul (show 641 ≤ ⌊X⌋₊ + 1 by omega)
      (show 13 ≤ ⌊3 * D⌋₊ + 1 by omega)
  · push_cast
    linarith
  · push_cast
    linarith
  · push_cast
    have hK : (⌊X⌋₊ : ℝ) + 1 ≤ (641 / 640 : ℝ) * X := by linarith
    have hL : (⌊3 * D⌋₊ : ℝ) + 1 ≤ (13 / 4 : ℝ) * D := by linarith
    have hmul := mul_le_mul hK hL (by positivity) (by positivity)
    nlinarith

/--
Rounding each balanced side length down and adding one gives a rectangle with cardinality strictly above the prescribed area.
-/
theorem certRectangleCard {A a b : ℝ} (hA : 0 ≤ A)
    (ha : 0 < a) (hb : 0 < b) :
    A < (((⌊Real.sqrt (A * b / a)⌋₊ + 1 : ℕ) : ℝ) *
      ((⌊Real.sqrt (A * a / b)⌋₊ + 1 : ℕ) : ℝ)) := by
  have h₁ := Nat.lt_floor_add_one (Real.sqrt (A * b / a))
  have h₂ := Nat.lt_floor_add_one (Real.sqrt (A * a / b))
  push_cast
  have ha' : 0 ≤ A * b / a := by positivity
  have heq : Real.sqrt (A * b / a) * Real.sqrt (A * a / b) = A := by
    rw [← Real.sqrt_mul ha']
    rw [show A * b / a * (A * a / b) = A ^ 2 by field_simp]
    exact Real.sqrt_sq hA
  calc
    A = Real.sqrt (A * b / a) * Real.sqrt (A * a / b) := heq.symm
    _ ≤ (↑⌊Real.sqrt (A * b / a)⌋₊ + 1) * Real.sqrt (A * a / b) :=
      mul_le_mul_of_nonneg_right h₁.le (Real.sqrt_nonneg _)
    _ < _ := mul_lt_mul_of_pos_left h₂ (by positivity)

/--
The variable-radius grid has at least 8333 entries and satisfies the required upper bound on dimension times radius.
-/
theorem certRadiusDimensions {r a b D : ℝ}
    (hr : 1 ≤ r) (ha : r ≤ a) (hb : r ≤ b) (hD : 4 ≤ D) :
    let X := 160 * a * b * D / r ^ 2
    let N := (⌊X⌋₊ + 1) * (⌊3 * D⌋₊ + 1)
    8333 ≤ N ∧
      (N : ℝ) * r ≤ (8333 / 16 : ℝ) * (a * b * D ^ 2 / r) := by
  dsimp
  have hr0 : 0 < r := by linarith
  have hab : r ^ 2 ≤ a * b := by
    rw [sq]
    exact mul_le_mul ha hb hr0.le (hr0.le.trans ha)
  have hX : 640 ≤ 160 * a * b * D / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr0)).mpr
    have h := mul_le_mul (show 4 ≤ D from hD) hab (sq_nonneg r) (by linarith)
    nlinarith
  obtain ⟨_, _, hN, _, _, _, _, hNu⟩ := _root_.AbcTwoNinths.ExteriorE1.certFloorDimensions hD hX
  refine ⟨hN, (mul_le_mul_of_nonneg_right hNu hr0.le).trans ?_⟩
  apply le_of_eq
  field_simp; ring

/--
The variable-radius grid has logarithmic interpolation weight at most 1157 times its height scale.
-/
theorem certRadiusFinal1157 {r a b D : ℝ}
    (hr : 1 ≤ r) (ha : r ≤ a) (hb : r ≤ b) (hD : 4 ≤ D) :
    let X := 160 * a * b * D / r ^ 2
    let N := (⌊X⌋₊ + 1) * (⌊3 * D⌋₊ + 1)
    Real.log ((N : ℝ) * ((10 / 3 : ℝ) * Real.exp r / r) ^ N) ≤
      1157 * (a * b * D ^ 2 / r) := by
  obtain ⟨hN, hNU⟩ := _root_.AbcTwoNinths.ExteriorE1.certRadiusDimensions hr ha hb hD
  exact _root_.AbcTwoNinths.ExteriorE1.certFinal1157 hr hN hNU

/--
For a real argument of absolute value at most one half, the exponential differs from one by at most twice its absolute value.
-/
theorem certExpPerturbation {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.exp z - 1| ≤ 2 * |z| := by
  have he : Real.exp z ≤ 2 := by
    calc
      Real.exp z ≤ Real.exp (1 / 2 : ℝ) :=
        Real.exp_le_exp.mpr ((le_abs_self _).trans hz)
      _ ≤ 16 / 9 := _root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.2.2.1
      _ ≤ 2 := by norm_num
  have he0 := Real.exp_pos z
  have hneg := Real.add_one_le_exp (-z)
  rw [Real.exp_neg] at hneg
  have hmul := mul_le_mul_of_nonneg_right hneg he0.le
  rw [inv_mul_cancel₀ he0.ne'] at hmul
  rw [abs_le]
  constructor
  · linarith [Real.add_one_le_exp z, neg_abs_le z, abs_nonneg z]
  · nlinarith [mul_le_mul_of_nonneg_right (le_abs_self z) he0.le,
      mul_le_mul_of_nonneg_left he (abs_nonneg z)]

/--
Three terms satisfying their respective rational bounds sum to less than the scaled logarithm of the interpolation base divided by e.
-/
theorem certRhsBudget {r scale A B C : ℝ}
    (hr : 0 < r) (hs : 0 < scale)
    (hA : A ≤ (89 / 220 : ℝ) * r * scale)
    (hB : B ≤ (77077 / 480000 : ℝ) * r * scale)
    (hC : C ≤ (260 / 99996 : ℝ) * r * scale) :
    A + B + C <
      scale * Real.log (((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1) := by
  have htotal : (89 / 220 : ℝ) + 77077 / 480000 + 260 / 99996 < 7 / 10 := by
    norm_num
  have hm := mul_lt_mul_of_pos_right htotal (mul_pos hr hs)
  have hlog := mul_le_mul_of_nonneg_left (_root_.AbcTwoNinths.ExteriorE1.certLogQ0DivE hr) hs.le
  linarith only [hA, hB, hC, hm, hlog]

/--
Bounds the logarithmic majorant and half the weighted grid height in terms of the same grid scale.
-/
theorem certRhsGridTerms {r D J K L G : ℝ}
    (hr : 0 < r) (hD : 4 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hDL : (11 / 4 : ℝ) * D ≤ J) (hLJ : L ≤ (13 / 12 : ℝ) * J)
    (hG : G ≤ (5929 / 20000 : ℝ) * r * K) :
    K * (r * D + (9 / 20 : ℝ) * r) ≤ (89 / 220 : ℝ) * r * (K * J) ∧
      (1 / 2 : ℝ) * L * G ≤ (77077 / 480000 : ℝ) * r * (K * J) := by
  constructor
  · have h : D + (9 / 20 : ℝ) ≤ (89 / 220 : ℝ) * J := by linarith
    have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hK hr.le)
    linarith only [hm]
  · have h₁ := mul_le_mul_of_nonneg_left hG hL
    have h₂ := mul_le_mul_of_nonneg_right hLJ
      (show 0 ≤ (5929 / 20000 : ℝ) * r * K by positivity)
    linarith only [h₁, h₂]

/-- Bounds the logarithmic remainder for a grid of dimension at least 8333. -/
theorem certRhsRemainder {r N scale : ℝ}
    (hr : 1 ≤ r) (hN : 8333 ≤ N) (hs : N ≤ (13 / 12 : ℝ) * scale) :
    2 * Real.log 2 + 2 / N + 2 * Real.log N ≤ (260 / 99996 : ℝ) * r * scale := by
  have hN0 : 0 < N := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < N / 8333 by positivity)
  rw [Real.log_div hN0.ne' (by norm_num)] at hlog
  have hdiv : (2 : ℝ) / N ≤ 1 / 100 := by
    apply (div_le_iff₀ hN0).mpr
    linarith
  have hlogN : Real.log N ≤ (903 / 100 : ℝ) + N / 8333 - 1 := by
    linarith [_root_.AbcTwoNinths.ExteriorE1.certElementaryTranscendentals.2.2.2.2]
  have hs0 : 0 ≤ scale := by linarith
  have hsr : scale ≤ r * scale := by nlinarith
  calc
    _ ≤ (20 / 8333 : ℝ) * N := by linarith [Real.log_two_lt_d9]
    _ ≤ (20 / 8333 : ℝ) * ((13 / 12 : ℝ) * scale) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := by linarith

/--
The logarithmic remainder, weighted logarithm and grid-height term together lie strictly below the grid logarithmic bound. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem certRhsContradictionFromGrid {r D B M j K L G : ℝ}
    (hr : 1 ≤ r) (hD : 4 ≤ D) (hB : 0 < B) (hM : 0 < M)
    (hj : 0 < j) (hjK : j ≤ K) (hN : 8333 ≤ K * L)
    (hDL : (11 / 4 : ℝ) * D ≤ L - 1)
    (hL : L ≤ (13 / 12 : ℝ) * (L - 1))
    (hG : G ≤ (5929 / 20000 : ℝ) * r * K)
    (hlogB : Real.log B ≤ r * D)
    (hMbound : M / (j * B) ≤ (3 / 20 : ℝ) * r) :
    (2 * Real.log 2 + 2 / (K * L) + 2 * Real.log (K * L)) +
      j * Real.log (Real.exp 2 * M / j) + (1 / 2 : ℝ) * L * G <
        (K * (L - 1)) * Real.log (((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1) := by
  have hr' : 0 < r := by linarith
  have hK : 0 < K := hj.trans_le hjK
  have hL' : 0 < L - 1 := by linarith
  have hprod : 0 < K * (L - 1) := mul_pos hK hL'
  have hLN : K * L ≤ (13 / 12 : ℝ) * (K * (L - 1)) := by
    linarith only [mul_le_mul_of_nonneg_left hL hK.le]
  obtain ⟨h₁, h₂⟩ := _root_.AbcTwoNinths.ExteriorE1.certRhsGridTerms hr' hD hK.le (by linarith) hDL hL hG
  have h₁' := (_root_.AbcTwoNinths.ExteriorE1.certRhsLog hr' hD hB hM hj hjK hlogB hMbound).trans h₁
  have h₃ := _root_.AbcTwoNinths.ExteriorE1.certRhsRemainder hr hN hLN
  linarith only [_root_.AbcTwoNinths.ExteriorE1.certRhsBudget hr' hprod h₁' h₂ h₃]

end

end AbcTwoNinths.ExteriorE1
