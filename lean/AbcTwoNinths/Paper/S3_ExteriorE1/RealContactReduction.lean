/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Successive Minima of the Exponent Plane

The coordinate height makes bounded subsets of the integer exponent plane finite and yields a
unimodular basis attaining the successive minima. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.planeHeightBoxBound`
* `AbcTwoNinths.ExteriorE1.existsUnimodularMinima`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

open Real

/--
The oriented determinant of two integer pairs. This is used in the proof of Proposition 3.1 of the paper.
-/
def det2 (u w : ℤ × ℤ) : ℤ := u.1 * w.2 - u.2 * w.1

/--
Map an integer coefficient pair to its linear combination of the two exponent vectors. This is used in the proof of Proposition 3.1 of the paper.
-/
def planeMap {ι : Type*} (e v : ι → ℤ) (x : ℤ × ℤ) : ι → ℤ :=
  fun j => x.1 * e j + x.2 * v j

/--
The exponent at one coordinate of the real plane, weighted by the logarithm of its base. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def planeCoord {ι : Type*} (q : ι → ℕ) (e v : ι → ℤ)
    (j : ι) (z : ℝ × ℝ) : ℝ :=
  (z.1 * (e j : ℝ) + z.2 * (v j : ℝ)) * log (q j : ℝ)

/--
The larger of the total positive and total negative logarithmic coordinate masses. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def planeHeight {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e v : ι → ℤ) (z : ℝ × ℝ) : ℝ :=
  max (∑ j, max (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0)
      (∑ j, max (-(_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z)) 0)

variable {ι : Type*} [Fintype ι] (q : ι → ℕ) (e v : ι → ℤ)

/--
The plane height is half the sum of the absolute coordinate masses and the absolute total mass.
-/
theorem planeHeightEqAbs (z : ℝ × ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z =
      ((∑ j, |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z|) + |∑ j, _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z|) / 2 := by
  classical
  have hsum : (∑ j, |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z|) =
      (∑ j, max (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) + (∑ j, max (-_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    generalize _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z = x
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]
      ring
  have hdiff : (∑ j, _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) =
      (∑ j, max (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) - (∑ j, max (-_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    generalize _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z = x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  rw [_root_.AbcTwoNinths.ExteriorE1.planeHeight, hsum, hdiff]
  generalize (∑ j, max (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) = A
  generalize (∑ j, max (-_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) 0) = B
  rcases le_total A B with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The exponent-plane height is nonnegative. -/
theorem planeHeightNonneg (z : ℝ × ℝ) : 0 ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z := by
  rw [_root_.AbcTwoNinths.ExteriorE1.planeHeightEqAbs]
  positivity

/-- Scaling a real coefficient pair multiplies its height by the absolute value of the scalar. -/
theorem planeHeightSmul (a : ℝ) (z : ℝ × ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (a • z) = |a| * _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z := by
  have h (j : ι) : _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j (a • z) = a * _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z := by
    simp only [_root_.AbcTwoNinths.ExteriorE1.planeCoord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  simp_rw [_root_.AbcTwoNinths.ExteriorE1.planeHeightEqAbs, h, abs_mul, ← Finset.mul_sum]
  rw [abs_mul]
  ring

/-- The height of a sum is bounded by the sum of the two heights. -/
theorem planeHeightAdd (x y : ℝ × ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (x + y) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v x + _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v y := by
  have h (j : ι) : _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j (x + y) =
      _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j x + _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j y := by
    simp only [_root_.AbcTwoNinths.ExteriorE1.planeCoord, Prod.fst_add, Prod.snd_add]
    ring
  simp_rw [_root_.AbcTwoNinths.ExteriorE1.planeHeightEqAbs, h, Finset.sum_add_distrib]
  have h₁ := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    abs_add_le (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j x) (_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j y)
  rw [Finset.sum_add_distrib] at h₁
  linarith [abs_add_le (∑ j, _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j x) (∑ j, _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j y)]

/--
Bound the height of a two-term real linear combination by the absolute coefficients times the heights.
-/
theorem planeHeightCombination (a b : ℝ) (x y : ℝ × ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (a • x + b • y) ≤ |a| * _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v x + |b| * _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v y := by
  simpa only [_root_.AbcTwoNinths.ExteriorE1.planeHeightSmul] using _root_.AbcTwoNinths.ExteriorE1.planeHeightAdd q e v (a • x) (b • y)

/-- The height lies between one half and the whole sum of the absolute weighted coordinates. -/
theorem planeHeightAbsBounds (z : ℝ × ℝ) :
    (1 / 2 : ℝ) * ∑ j, |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z| ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z ∧
    _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z ≤ ∑ j, |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z| := by
  rw [_root_.AbcTwoNinths.ExteriorE1.planeHeightEqAbs]
  constructor
  · linarith [abs_nonneg (∑ j, _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z)]
  · linarith [Finset.abs_sum_le_sum_abs (fun j => _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z) Finset.univ]

/--
Embed an integer coefficient pair in the real plane coordinatewise. This is used in the proof of Proposition 3.1 of the paper.
-/
def realPair (x : ℤ × ℤ) : ℝ × ℝ := ((x.1 : ℝ), (x.2 : ℝ))

set_option linter.unusedSectionVars false in
/--
At an integer pair the weighted coordinate equals the integer exponent times the logarithm of its base.
-/
theorem planeCoordRealPair (j : ι) (x : ℤ × ℤ) :
    _root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j (_root_.AbcTwoNinths.ExteriorE1.realPair x) = (_root_.AbcTwoNinths.ExteriorE1.planeMap e v x j : ℝ) * log (q j : ℝ) := by
  simp only [_root_.AbcTwoNinths.ExteriorE1.planeCoord, _root_.AbcTwoNinths.ExteriorE1.planeMap, _root_.AbcTwoNinths.ExteriorE1.realPair, Int.cast_add, Int.cast_mul]

/--
A nonzero first exponent vector and a second outside its rational span have a nonzero coordinate minor.
-/
theorem existsMinor {e v : ι → ℤ} (he : e ≠ 0)
    (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ)) :
    ∃ i j, e i * v j - e j * v i ≠ 0 := by
  classical
  have ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! h
    exact he (funext h)
  by_contra! h
  apply hind
  refine ⟨(v i : ℚ) / (e i : ℚ), fun j => ?_⟩
  have hi' : (e i : ℚ) ≠ 0 := by exact_mod_cast hi
  have hj : (e i : ℚ) * v j - (e j : ℚ) * v i = 0 := by exact_mod_cast h i j
  field_simp
  linarith

omit [Fintype ι] in
/-- A nonzero coordinate minor makes the integer exponent-plane map injective. -/
theorem planeMapInjective {i j : ι} (h : e i * v j - e j * v i ≠ 0) :
    Function.Injective (_root_.AbcTwoNinths.ExteriorE1.planeMap e v) := by
  intro x y hxy
  have hi := congrFun hxy i
  have hj := congrFun hxy j
  simp only [_root_.AbcTwoNinths.ExteriorE1.planeMap] at hi hj
  apply Prod.ext
  · have hz : (e i * v j - e j * v i) * (x.1 - y.1) = 0 := by
      linear_combination (v j) * hi - (v i) * hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h)
  · have hz : (e i * v j - e j * v i) * (x.2 - y.2) = 0 := by
      linear_combination (e i) * hj - (e j) * hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h)

/-- Each absolute weighted coordinate is at most twice the exponent-plane height. -/
theorem absCoordLe (j : ι) (z : ℝ × ℝ) :
    |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z| ≤ 2 * _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v z := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => |_root_.AbcTwoNinths.ExteriorE1.planeCoord q e v j z|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [(_root_.AbcTwoNinths.ExteriorE1.planeHeightAbsBounds q e v z).1]

/--
Independent exponent vectors with prime bases give a nonzero minor, an injective plane map, and positive height on nonzero lattice points.
-/
theorem existsNonzeroMinorOfInd (hq : ∀ j, (q j).Prime)
    (he : e ≠ 0) (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ)) :
    (∃ i j, e i * v j - e j * v i ≠ 0) ∧ Function.Injective (_root_.AbcTwoNinths.ExteriorE1.planeMap e v) ∧
    (∀ x : ℤ × ℤ, x ≠ 0 → 0 < _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)) := by
  obtain ⟨i, j, h⟩ := _root_.AbcTwoNinths.ExteriorE1.existsMinor he hind
  have hinj := _root_.AbcTwoNinths.ExteriorE1.planeMapInjective e v h
  refine ⟨⟨i, j, h⟩, hinj, fun x hx => ?_⟩
  have hne : _root_.AbcTwoNinths.ExteriorE1.planeMap e v x ≠ _root_.AbcTwoNinths.ExteriorE1.planeMap e v 0 := fun hh => hx (hinj hh)
  classical
  have ⟨k, hk⟩ : ∃ k, _root_.AbcTwoNinths.ExteriorE1.planeMap e v x k ≠ 0 := by
    by_contra! hh
    apply hne
    ext k
    simpa [_root_.AbcTwoNinths.ExteriorE1.planeMap] using hh k
  have hk' : (_root_.AbcTwoNinths.ExteriorE1.planeMap e v x k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hl : 0 < log (q k : ℝ) := log_pos (by exact_mod_cast (hq k).one_lt)
  have ha := abs_pos.mpr (mul_ne_zero hk' hl.ne')
  have hb := _root_.AbcTwoNinths.ExteriorE1.absCoordLe q e v k (_root_.AbcTwoNinths.ExteriorE1.realPair x)
  rw [_root_.AbcTwoNinths.ExteriorE1.planeCoordRealPair] at hb
  linarith

/--
With prime bases and a nonzero minor, every nonnegative height sublevel on integer pairs lies in a finite square.
-/
theorem planeHeightBoxBound (hq : ∀ j, (q j).Prime)
    {i j : ι} (h : e i * v j - e j * v i ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ x : ℤ × ℤ, _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x) ≤ B →
      x ∈ (Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M) := by
  let D : ℝ := (e i : ℝ) * v j - (e j : ℝ) * v i
  have hD : 1 ≤ |D| := by
    have hi : (1 : ℤ) ≤ |e i * v j - e j * v i| := by
      have := abs_pos.mpr h
      omega
    dsimp [D]
    exact_mod_cast hi
  let C : ℝ := 4 * B * (|(v i : ℝ)| + |(v j : ℝ)| + |(e i : ℝ)| + |(e j : ℝ)|)
  let M : ℤ := ⌈C⌉
  have hCM : C ≤ (M : ℝ) := Int.le_ceil _
  have hM : 0 ≤ M := by
    exact_mod_cast (show (0 : ℝ) ≤ (M : ℝ) from le_trans (by dsimp [C]; positivity) hCM)
  refine ⟨M, hM, fun x hx => ?_⟩
  let U (k : ι) : ℝ := (x.1 : ℝ) * e k + (x.2 : ℝ) * v k
  have hu (k : ι) : |U k| ≤ 4 * B := by
    have hlog : (1 / 2 : ℝ) ≤ log (q k : ℝ) := by
      have hl : log 2 ≤ log (q k : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (hq k).two_le)
      linarith [Real.log_two_gt_d9]
    have hcoord := (_root_.AbcTwoNinths.ExteriorE1.absCoordLe q e v k (_root_.AbcTwoNinths.ExteriorE1.realPair x)).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
    change |U k * log (q k : ℝ)| ≤ 2 * B at hcoord
    rw [abs_mul, abs_of_nonneg (show 0 ≤ log (q k : ℝ) by linarith)] at hcoord
    nlinarith [mul_le_mul_of_nonneg_left hlog (abs_nonneg (U k))]
  have hxprod (x : ℝ) : |x| ≤ |D * x| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hD (abs_nonneg x)
  have h1 : |(x.1 : ℝ)| ≤ C := calc
    _ ≤ |D * (x.1 : ℝ)| := hxprod _
    _ = |U i * (v j : ℝ) - U j * (v i : ℝ)| := by
      congr 1
      dsimp [D, U]
      ring
    _ ≤ |U i * (v j : ℝ)| + |U j * (v i : ℝ)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (U i * (v j : ℝ)) (-(U j * (v i : ℝ)))
    _ ≤ C := by
      simp only [abs_mul]
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right (hu i) (abs_nonneg (v j : ℝ)),
        mul_le_mul_of_nonneg_right (hu j) (abs_nonneg (v i : ℝ)),
        mul_nonneg hB (abs_nonneg (e i : ℝ)), mul_nonneg hB (abs_nonneg (e j : ℝ))]
  have h2 : |(x.2 : ℝ)| ≤ C := calc
    _ ≤ |D * (x.2 : ℝ)| := hxprod _
    _ = |U j * (e i : ℝ) - U i * (e j : ℝ)| := by
      congr 1
      dsimp [D, U]
      ring
    _ ≤ |U j * (e i : ℝ)| + |U i * (e j : ℝ)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (U j * (e i : ℝ)) (-(U i * (e j : ℝ)))
    _ ≤ C := by
      simp only [abs_mul]
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right (hu j) (abs_nonneg (e i : ℝ)),
        mul_le_mul_of_nonneg_right (hu i) (abs_nonneg (e j : ℝ)),
        mul_nonneg hB (abs_nonneg (v i : ℝ)), mul_nonneg hB (abs_nonneg (v j : ℝ))]
  have h1' : |x.1| ≤ M := by exact_mod_cast h1.trans hCM
  have h2' : |x.2| ≤ M := by exact_mod_cast h2.trans hCM
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h1'),
    Finset.mem_Icc.mpr (abs_le.mp h2')⟩

private theorem existsMinimal (H : ℤ × ℤ → ℝ)
    (hbox : ∀ B, 0 ≤ B → ∃ s : Finset (ℤ × ℤ), ∀ x, H x ≤ B → x ∈ s)
    (hn : ∀ x, 0 ≤ H x) (P : ℤ × ℤ → Prop) (x₀ : ℤ × ℤ) (hx₀ : P x₀) :
    ∃ w, P w ∧ ∀ x, P x → H w ≤ H x := by
  classical
  obtain ⟨s, hs⟩ := hbox (H x₀) (hn x₀)
  let t := s.filter fun x => P x ∧ H x ≤ H x₀
  have ht : x₀ ∈ t := Finset.mem_filter.mpr ⟨hs x₀ le_rfl, hx₀, le_rfl⟩
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image t H ⟨x₀, ht⟩
  obtain ⟨_, hwP, hwH⟩ := Finset.mem_filter.mp hw
  refine ⟨w, hwP, fun x hx => ?_⟩
  by_cases hxH : H x ≤ H x₀
  · exact hmin x (Finset.mem_filter.mpr ⟨hs x hxH, hx, hxH⟩)
  · exact hwH.trans (le_of_not_ge hxH)

private theorem roundBound (t : ℝ) : |(⌊t + 1 / 2⌋ : ℤ) - t| ≤ 1 / 2 := by
  have h₁ := Int.floor_le (t + 1 / 2)
  have h₂ := Int.lt_floor_add_one (t + 1 / 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem primitiveCompanion {w : ℤ × ℤ} (hw : w ≠ 0)
    (hp : ∀ x : ℤ × ℤ, x ≠ 0 → 0 < _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x))
    (hm : ∀ x : ℤ × ℤ, x ≠ 0 → _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair w) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)) :
    ∃ b, _root_.AbcTwoNinths.ExteriorE1.det2 w b = 1 := by
  let g := Int.gcd w.1 w.2
  have hg : g ≠ 0 := by
    intro hg
    have hz := Int.gcd_eq_zero_iff.mp hg
    exact hw (Prod.ext hz.1 hz.2)
  let u : ℤ × ℤ := (w.1 / (g : ℤ), w.2 / (g : ℤ))
  have h₁ : u.1 * (g : ℤ) = w.1 := Int.ediv_mul_cancel (Int.gcd_dvd_left w.1 w.2)
  have h₂ : u.2 * (g : ℤ) = w.2 := Int.ediv_mul_cancel (Int.gcd_dvd_right w.1 w.2)
  have hu : u ≠ 0 := by
    intro hu
    apply hw
    rw [hu] at h₁ h₂
    exact Prod.ext (by simpa using h₁.symm) (by simpa using h₂.symm)
  have hsm : _root_.AbcTwoNinths.ExteriorE1.realPair w = (g : ℝ) • _root_.AbcTwoNinths.ExteriorE1.realPair u := by
    apply Prod.ext
    · change (w.1 : ℝ) = (g : ℝ) * (u.1 : ℝ)
      exact_mod_cast (by rw [mul_comm, h₁] : w.1 = (g : ℤ) * u.1)
    · change (w.2 : ℝ) = (g : ℝ) * (u.2 : ℝ)
      exact_mod_cast (by rw [mul_comm, h₂] : w.2 = (g : ℤ) * u.2)
  have hh := hm u hu
  rw [hsm, _root_.AbcTwoNinths.ExteriorE1.planeHeightSmul, abs_of_nonneg (Nat.cast_nonneg _)] at hh
  have hg' : (g : ℝ) ≤ 1 := by
    have := hp u hu
    nlinarith
  have hg1 : g = 1 := by
    have hgLe : g ≤ 1 := by exact_mod_cast hg'
    omega
  refine ⟨(-Int.gcdB w.1 w.2, Int.gcdA w.1 w.2), ?_⟩
  have hb := Int.gcd_eq_gcd_ab w.1 w.2
  change (g : ℤ) = _ at hb
  rw [hg1] at hb
  simp only [_root_.AbcTwoNinths.ExteriorE1.det2, mul_neg, sub_neg_eq_add]
  exact hb.symm

private theorem minimumTransverse {w b x : ℤ × ℤ} (hb : _root_.AbcTwoNinths.ExteriorE1.det2 w b = 1)
    (hx : _root_.AbcTwoNinths.ExteriorE1.det2 w x ≠ 0) (hu : |_root_.AbcTwoNinths.ExteriorE1.det2 w x| ≠ 1)
    (hm : _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair w) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)) :
    ∃ z, _root_.AbcTwoNinths.ExteriorE1.det2 w z = 1 ∧ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair z) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x) := by
  let d := _root_.AbcTwoNinths.ExteriorE1.det2 w x
  let a := _root_.AbcTwoNinths.ExteriorE1.det2 x b
  have hdi : (d : ℝ) ≠ 0 := by exact_mod_cast hx
  have hd₂ : (2 : ℝ) ≤ |(d : ℝ)| := by
    have hd₂' : (2 : ℤ) ≤ |d| := by
      have := abs_pos.mpr hx
      change 0 < |d| at this
      change |d| ≠ 1 at hu
      omega
    exact_mod_cast hd₂'
  let k : ℤ := ⌊(a : ℝ) / (d : ℝ) + 1 / 2⌋
  let z : ℤ × ℤ := (b.1 + k * w.1, b.2 + k * w.2)
  refine ⟨z, ?_, ?_⟩
  · dsimp [z, _root_.AbcTwoNinths.ExteriorE1.det2] at *
    linear_combination hb
  have hb₁ : x.1 = a * w.1 + d * b.1 := by
    dsimp [a, d, _root_.AbcTwoNinths.ExteriorE1.det2] at *
    linear_combination -x.1 * hb
  have hb₂ : x.2 = a * w.2 + d * b.2 := by
    dsimp [a, d, _root_.AbcTwoNinths.ExteriorE1.det2] at *
    linear_combination -x.2 * hb
  have hr : _root_.AbcTwoNinths.ExteriorE1.realPair z = ((k : ℝ) - (a : ℝ) / (d : ℝ)) • _root_.AbcTwoNinths.ExteriorE1.realPair w +
      (1 / (d : ℝ)) • _root_.AbcTwoNinths.ExteriorE1.realPair x := by
    apply Prod.ext
    · have hf : (x.1 : ℝ) = (a : ℝ) * w.1 + (d : ℝ) * b.1 := by exact_mod_cast hb₁
      simp only [_root_.AbcTwoNinths.ExteriorE1.realPair, z, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Int.cast_add, Int.cast_mul]
      field_simp
      linear_combination -hf
    · have hf : (x.2 : ℝ) = (a : ℝ) * w.2 + (d : ℝ) * b.2 := by exact_mod_cast hb₂
      simp only [_root_.AbcTwoNinths.ExteriorE1.realPair, z, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Int.cast_add, Int.cast_mul]
      field_simp
      linear_combination -hf
  rw [hr]
  have hbound := _root_.AbcTwoNinths.ExteriorE1.planeHeightCombination q e v ((k : ℝ) - (a : ℝ) / (d : ℝ))
    (1 / (d : ℝ)) (_root_.AbcTwoNinths.ExteriorE1.realPair w) (_root_.AbcTwoNinths.ExteriorE1.realPair x)
  have habs : |1 / (d : ℝ)| ≤ 1 / 2 := by
    rw [abs_div, abs_one]
    apply (div_le_iff₀ (abs_pos.mpr hdi)).2
    linarith
  have h₁ := mul_le_mul_of_nonneg_right (roundBound ((a : ℝ) / (d : ℝ)))
    (_root_.AbcTwoNinths.ExteriorE1.planeHeightNonneg q e v (_root_.AbcTwoNinths.ExteriorE1.realPair w))
  have h₂ := mul_le_mul_of_nonneg_right habs (_root_.AbcTwoNinths.ExteriorE1.planeHeightNonneg q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x))
  linarith

/--
A unimodular pair attains the minimum nonzero lattice height and the minimum height transverse to its first vector. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem existsUnimodularMinima (hq : ∀ j, (q j).Prime)
    (he : e ≠ 0) (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ)) :
    ∃ w₁ w₂ : ℤ × ℤ, w₁ ≠ 0 ∧ |_root_.AbcTwoNinths.ExteriorE1.det2 w₁ w₂| = 1 ∧
      (∀ x : ℤ × ℤ, x ≠ 0 → _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair w₁) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)) ∧
      (∀ x : ℤ × ℤ, _root_.AbcTwoNinths.ExteriorE1.det2 w₁ x ≠ 0 →
        _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair w₂) ≤ _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)) := by
  classical
  obtain ⟨⟨i, j, hh⟩, _, hp⟩ := _root_.AbcTwoNinths.ExteriorE1.existsNonzeroMinorOfInd q e v hq he hind
  let H := fun x : ℤ × ℤ => _root_.AbcTwoNinths.ExteriorE1.planeHeight q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)
  have hbox B (hB : 0 ≤ B) : ∃ s : Finset (ℤ × ℤ), ∀ x, H x ≤ B → x ∈ s := by
    obtain ⟨M, _, hM⟩ := _root_.AbcTwoNinths.ExteriorE1.planeHeightBoxBound q e v hq hh hB
    exact ⟨_, hM⟩
  have hn : ∀ x, 0 ≤ H x := fun x => _root_.AbcTwoNinths.ExteriorE1.planeHeightNonneg q e v (_root_.AbcTwoNinths.ExteriorE1.realPair x)
  obtain ⟨w, hw, hm⟩ := existsMinimal H hbox hn (· ≠ 0) (1, 0) (by norm_num)
  obtain ⟨b, hb⟩ := primitiveCompanion q e v hw hp hm
  obtain ⟨u, hu, hm'⟩ := existsMinimal H hbox hn (fun x => |_root_.AbcTwoNinths.ExteriorE1.det2 w x| = 1) b (by simp [hb])
  refine ⟨w, u, hw, hu, hm, fun x hx => ?_⟩
  by_cases h : |_root_.AbcTwoNinths.ExteriorE1.det2 w x| = 1
  · exact hm' x h
  · have hne : x ≠ 0 := by
      rintro rfl
      simp [_root_.AbcTwoNinths.ExteriorE1.det2] at hx
    obtain ⟨z, hz, hzH⟩ := minimumTransverse q e v hb hx h (hm x hne)
    exact (hm' z (by simp [hz])).trans hzH

end

end AbcTwoNinths.ExteriorE1
