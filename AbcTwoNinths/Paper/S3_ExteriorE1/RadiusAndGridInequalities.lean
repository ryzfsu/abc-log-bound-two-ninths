/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.InterpolationParameterInequalities

/-!
# Radius And Grid Inequalities

The module verifies the grid side and radius inequalities that force the final real-estimate contradiction. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.certRhsContradiction`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Bounds the logarithmic grid term and proves the strict determinant inequality from separate weighted side bounds.
-/
theorem certRhsContradictionOfSideBounds
    {r a b D j K L R S m n : ℝ}
    (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hD : 4 ≤ D) (hj : 640 ≤ j) (hK : K = j + 1)
    (hN : 8333 ≤ K * L) (hDL : (11 / 4 : ℝ) * D ≤ L - 1)
    (hL : L ≤ (13 / 12 : ℝ) * (L - 1))
    (hR : R * a ≤ (5929 / 40000 : ℝ) * r * K)
    (hS : S * b ≤ (5929 / 40000 : ℝ) * r * K)
    (hm : 0 < m) (hn : 0 < n) (hM : 0 < R * n + S * m)
    (hlogB : Real.log (m / b + n / a) ≤ r * D) :
    j * Real.log (Real.exp 2 * (R * n + S * m) / j) ≤
      K * (r * D + (9 / 20 : ℝ) * r) ∧
    (2 * Real.log 2 + 2 / (K * L) + 2 * Real.log (K * L)) +
      j * Real.log (Real.exp 2 * (R * n + S * m) / j) +
      (1 / 2 : ℝ) * L * (R * a + S * b) <
        (K * (L - 1)) * Real.log (((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1) := by
  have hr0 : 0 < r := by linarith
  have hj0 : 0 < j := by linarith
  have hjK : j ≤ K := by linarith
  have hB : 0 < m / b + n / a := by positivity
  have hG : R * a + S * b ≤ (5929 / 20000 : ℝ) * r * K :=
    by linarith only [hR, hS]
  have hKj : K ≤ (641 / 640 : ℝ) * j := by linarith
  have hcoeff : (5929 / 40000 : ℝ) * r * K ≤ (3 / 20 : ℝ) * r * j := by
    have h := mul_le_mul_of_nonneg_left hKj
      (show 0 ≤ (5929 / 40000 : ℝ) * r by positivity)
    have hc := mul_le_mul_of_nonneg_right
      (by norm_num : (5929 / 40000 : ℝ) * (641 / 640) ≤ 3 / 20)
      (show 0 ≤ r * j by positivity)
    linarith only [h, hc]
  have hMbound : (R * n + S * m) / (j * (m / b + n / a)) ≤ (3 / 20 : ℝ) * r := by
    apply (div_le_iff₀ (mul_pos hj0 hB)).mpr
    have h₁ := mul_le_mul_of_nonneg_right (hR.trans hcoeff) (div_pos hn ha).le
    have h₂ := mul_le_mul_of_nonneg_right (hS.trans hcoeff) (div_pos hm hb).le
    have e₁ : R * a * (n / a) = R * n := by field_simp
    have e₂ : S * b * (m / b) = S * m := by field_simp
    rw [e₁] at h₁
    rw [e₂] at h₂
    linarith only [h₁, h₂]
  exact ⟨_root_.AbcTwoNinths.ExteriorE1.certRhsLog hr0 hD hB hM hj0 hjK hlogB hMbound,
    _root_.AbcTwoNinths.ExteriorE1.certRhsContradictionFromGrid hr hD hB hM hj0 hjK hN hDL hL
      hG hlogB hMbound⟩

/-- Bounds the logarithmic grid size with constant 1157 and weakens this bound to constant 4000. -/
theorem certRadiusFinal1157Le4000 {r a b D : ℝ}
    (hr : 1 ≤ r) (ha : r ≤ a) (hb : r ≤ b) (hD : 4 ≤ D) :
    let N : ℕ := (⌊160 * a * b * D / r ^ 2⌋₊ + 1) * (⌊3 * D⌋₊ + 1)
    Real.log ((N : ℝ) * ((10 / 3 : ℝ) * Real.exp r / r) ^ N) ≤
      1157 * (a * b * D ^ 2 / r) ∧
      1157 * (a * b * D ^ 2 / r) ≤ 4000 * (a * b * D ^ 2 / r) := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := hr0.trans_le ha
  have hb0 : 0 < b := hr0.trans_le hb
  exact ⟨_root_.AbcTwoNinths.ExteriorE1.certRadiusFinal1157 hr ha hb hD,
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)⟩

/--
Bounds the sum of the two floored side lengths times the corresponding height by a multiple of the radius and column count.
-/
theorem certGridSide {r a b D L j K : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hL0 : 0 ≤ L) (hL : L ≤ (13 / 4 : ℝ) * D)
    (hj : 640 ≤ j) (hJ : j ≤ 160 * a * b * D / r ^ 2)
    (hK : 160 * a * b * D / r ^ 2 ≤ K) :
    ((⌊Real.sqrt (L * b / a)⌋₊ : ℝ) +
      (⌊Real.sqrt (L * j * b / a)⌋₊ : ℝ)) * a ≤
        (5929 / 40000 : ℝ) * r * K := by
  have hj0 : 0 < j := by linarith
  have hsJ : (25 : ℝ) ≤ Real.sqrt j := by
    rw [Real.le_sqrt (by norm_num) hj0.le]
    linarith
  have hJ' : j * r ^ 2 ≤ 160 * a * b * D := (le_div_iff₀ (by positivity)).mp hJ
  have hK' : 160 * a * b * D ≤ K * r ^ 2 := (div_le_iff₀ (by positivity)).mp hK
  have hprod : L * j * a * b ≤ 520 * (a * b * D / r) ^ 2 := by
    have hJmul := mul_le_mul_of_nonneg_left hJ' (show 0 ≤ L * a * b by positivity)
    have hLmul := mul_le_mul_of_nonneg_right hL
      (show 0 ≤ 160 * a * b * D * (a * b) by positivity)
    have h : (L * j * a * b) * r ^ 2 ≤ 520 * (a * b * D) ^ 2 := by
      linarith only [hJmul, hLmul]
    rw [div_pow]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr h
  have hroot : Real.sqrt (L * j * a * b) ≤ (5929 / 260 : ℝ) * (a * b * D / r) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, hprod.trans ?_⟩
    have h := mul_le_mul_of_nonneg_right
      (by norm_num : (520 : ℝ) ≤ (5929 / 260) ^ 2) (sq_nonneg (a * b * D / r))
    linarith only [h]
  have hs₁ : Real.sqrt (L * b / a) * a = Real.sqrt (L * a * b) := by
    rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_sq ha.le]
    field_simp
  have hs₂ : Real.sqrt (L * j * b / a) * a = Real.sqrt (L * j * a * b) := by
    rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha.le).symm,
      ← Real.sqrt_mul (by positivity)]
    simp only [Real.sqrt_sq ha.le]
    congr 1
    field_simp
  have hs₃ : Real.sqrt (L * j * a * b) = Real.sqrt j * Real.sqrt (L * a * b) := by
    rw [← Real.sqrt_mul hj0.le]
    congr 1
    ring
  have hs₄ : Real.sqrt (L * a * b) ≤ Real.sqrt (L * j * a * b) / 25 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 25)).mpr
    rw [hs₃]
    linarith only [mul_le_mul_of_nonneg_right hsJ (Real.sqrt_nonneg (L * a * b))]
  have hKdiv : a * b * D / r ≤ r * K / 160 := by
    apply (div_le_iff₀ hr).mpr
    linarith only [hK']
  calc
    _ ≤ (Real.sqrt (L * b / a) + Real.sqrt (L * j * b / a)) * a :=
      mul_le_mul_of_nonneg_right
        (add_le_add (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.floor_le (Real.sqrt_nonneg _))) ha.le
    _ ≤ (26 / 25 : ℝ) * Real.sqrt (L * j * a * b) := by
      rw [add_mul, hs₁, hs₂]
      linarith only [hs₄]
    _ ≤ (26 / 25 : ℝ) * ((5929 / 260 : ℝ) * (r * K / 160)) :=
      mul_le_mul_of_nonneg_left
        (hroot.trans (mul_le_mul_of_nonneg_left hKdiv (by norm_num))) (by norm_num)
    _ = _ := by ring

/--
The rounded interpolation grid satisfies the logarithmic term bound and the strict determinant inequality. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem certRhsContradiction {r a b D : ℝ} {m n : ℕ}
    (hr : 1 ≤ r) (ha : r ≤ a) (hb : r ≤ b) (hD : 4 ≤ D)
    (hm : 0 < m) (hn : 0 < n)
    (hlogB : Real.log ((m : ℝ) / b + (n : ℝ) / a) ≤ r * D) :
    let L : ℕ := ⌊3 * D⌋₊ + 1
    let J : ℕ := ⌊160 * a * b * D / r ^ 2⌋₊
    let K : ℕ := J + 1
    let N : ℕ := K * L
    let R : ℕ := ⌊Real.sqrt ((L : ℝ) * b / a)⌋₊ + ⌊Real.sqrt ((L : ℝ) * J * b / a)⌋₊
    let S : ℕ := ⌊Real.sqrt ((L : ℝ) * a / b)⌋₊ + ⌊Real.sqrt ((L : ℝ) * J * a / b)⌋₊
    let M : ℝ := (R : ℝ) * n + (S : ℝ) * m
    (J : ℝ) * Real.log (Real.exp 2 * M / J) ≤
      (K : ℝ) * (r * D + (9 / 20 : ℝ) * r) ∧
    (2 * Real.log 2 + 2 / (N : ℝ) + 2 * Real.log (N : ℝ)) +
      (J : ℝ) * Real.log (Real.exp 2 * M / J) +
      (1 / 2 : ℝ) * L * ((R : ℝ) * a + (S : ℝ) * b) <
        ((K : ℝ) * ((L : ℝ) - 1)) * Real.log (((10 / 3 : ℝ) * Real.exp r / r) / Real.exp 1) := by
  dsimp only
  let X := 160 * a * b * D / r ^ 2
  let L : ℕ := ⌊3 * D⌋₊ + 1
  let J : ℕ := ⌊X⌋₊
  let K : ℕ := J + 1
  let R : ℕ := ⌊Real.sqrt ((L : ℝ) * b / a)⌋₊ + ⌊Real.sqrt ((L : ℝ) * J * b / a)⌋₊
  let S : ℕ := ⌊Real.sqrt ((L : ℝ) * a / b)⌋₊ + ⌊Real.sqrt ((L : ℝ) * J * a / b)⌋₊
  have hr0 : 0 < r := by linarith
  have ha0 := hr0.trans_le ha
  have hb0 := hr0.trans_le hb
  have hD0 : 0 < D := by linarith
  have hX : 640 ≤ X := by
    apply (le_div_iff₀ (sq_pos_of_pos hr0)).mpr
    have hab : r ^ 2 ≤ a * b := by rw [sq]; gcongr
    have h := mul_le_mul hD hab (sq_nonneg r) hD0.le
    nlinarith only [h]
  obtain ⟨hL13, hJ640, hN, hDL, hLJ, hLD, _, _⟩ := _root_.AbcTwoNinths.ExteriorE1.certFloorDimensions hD hX
  have hj640 : (640 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ640
  have hk : (K : ℝ) = (J : ℝ) + 1 := by simp [K]
  have hJ : (J : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hK : X ≤ (K : ℝ) := by rw [hk]; exact (Nat.lt_floor_add_one X).le
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
  have floor_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      0 < ⌊Real.sqrt ((L : ℝ) * y / x)⌋₊ := by
    have h : (1 : ℝ) ≤ (L : ℝ) * y / x := by
      apply (le_div_iff₀ hx).mpr
      have hy := hx.trans_le hxy
      linarith only [hxy, mul_le_mul_of_nonneg_right hL' hy.le]
    have hs : (1 : ℝ) ≤ Real.sqrt ((L : ℝ) * y / x) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      simpa using h
    exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by exact_mod_cast hs)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < (R : ℝ) * n + (S : ℝ) * m := by
    rcases le_total a b with hab | hba
    · have hR0 : 0 < R := Nat.add_pos_left (floor_pos ha0 hab) _
      have hr' : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR0
      positivity
    · have hS0 : 0 < S := Nat.add_pos_left (floor_pos hb0 hba) _
      have hs' : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS0
      positivity
  have hR : (R : ℝ) * a ≤ (5929 / 40000 : ℝ) * r * K := by
    simpa only [R, Nat.cast_add] using
      _root_.AbcTwoNinths.ExteriorE1.certGridSide hr0 ha0 hb0 hD0 (by positivity : 0 ≤ (L : ℝ)) hLD hj640 hJ hK
  have hS : (S : ℝ) * b ≤ (5929 / 40000 : ℝ) * r * K := by
    have hJ' : (J : ℝ) ≤ 160 * b * a * D / r ^ 2 := by
      convert hJ using 1
      dsimp [X]
      ring
    have hK' : 160 * b * a * D / r ^ 2 ≤ (K : ℝ) := by
      convert hK using 1
      dsimp [X]
      ring
    simpa only [S, Nat.cast_add] using
      _root_.AbcTwoNinths.ExteriorE1.certGridSide hr0 hb0 ha0 hD0 (by positivity : 0 ≤ (L : ℝ)) hLD hj640 hJ' hK'
  have hLe : (L : ℝ) - 1 = (⌊3 * D⌋₊ : ℝ) := by push_cast [L]; ring
  have hDL' : (11 / 4 : ℝ) * D ≤ (L : ℝ) - 1 := by rwa [hLe]
  have hLJ' : (L : ℝ) ≤ (13 / 12 : ℝ) * ((L : ℝ) - 1) := by rwa [hLe]
  simpa only [L, J, K, X, R, S, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    _root_.AbcTwoNinths.ExteriorE1.certRhsContradictionOfSideBounds hr ha0 hb0 hD hj640 hk
      (by exact_mod_cast hN) hDL' hLJ'
      hR hS hm0 hn0 hM hlogB

end

end AbcTwoNinths.ExteriorE1
