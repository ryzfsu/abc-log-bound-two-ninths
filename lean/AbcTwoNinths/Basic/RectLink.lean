/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RectBasis
public import AbcTwoNinths.Basic.RectBounds

/-!
# Rect Link

The module links a reduced weighted basis to integer coordinates and converts a rectangle collision into a short vector.

## Main results
* `AbcTwoNinths.Basic.collisionRectangle`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

variable {I : Type*} [Fintype I]

/-- The real coordinate space equipped with the L1 norm. -/
abbrev e (I : Type*) := PiLp 1 (fun _ : I => ℝ)

/-- Multiply each integer coordinate by its real weight in the L1 coordinate space. -/
noncomputable def embed (w : I → ℝ) (f : I → ℤ) : _root_.AbcTwoNinths.Basic.e I :=
  WithLp.toLp 1 (fun i => (f i : ℝ)*w i)

/-- For positive weights the L1 norm of the weighted vector equals its weighted mass. -/
theorem normEmbed (w : I → ℝ) (hw : ∀ i, 0 < w i) (f : I → ℤ) :
    ‖_root_.AbcTwoNinths.Basic.embed w f‖ = _root_.AbcTwoNinths.Basic.mass w f := by
  rw [PiLp.norm_eq_of_L1]
  unfold _root_.AbcTwoNinths.Basic.mass
  apply Finset.sum_congr rfl
  intro i _
  change |(f i:ℝ)*w i| = _
  rw [abs_mul, abs_of_pos (hw i)]

omit [Fintype I] in
/--
An integer shear of coefficient pairs gives the corresponding real linear combination of weighted vectors.
-/
theorem embedShear (w : I → ℝ) (e v : I → ℤ) (x y : _root_.AbcTwoNinths.Basic.ZPair) (n : ℤ) :
    _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v (_root_.AbcTwoNinths.Basic.shear n x y)) =
      (n : ℝ) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x) + _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y) := by
  ext i
  change (((n*x.1+y.1)*e i+(n*x.2+y.2)*v i : ℤ):ℝ)*w i =
    (n:ℝ)*((↑(x.1*e i+x.2*v i):ℝ)*w i) + (↑(y.1*e i+y.2*v i):ℝ)*w i
  push_cast
  ring

omit [Fintype I] in
/-- The inverse determinant-one matrix recovers both original weighted vectors. -/
theorem unimodularExpansion {x y : _root_.AbcTwoNinths.Basic.ZPair} (hd : _root_.AbcTwoNinths.Basic.det x y = 1)
    (w : I → ℝ) (e v : I → ℤ) :
    (y.2:ℝ) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x) + (-(x.2:ℝ)) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y) =
        _root_.AbcTwoNinths.Basic.embed w e ∧
    (-(y.1:ℝ)) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x) + (x.1:ℝ) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y) =
        _root_.AbcTwoNinths.Basic.embed w v := by
  have h : (x.1:ℝ)*y.2 - x.2*y.1 = 1 := by exact_mod_cast hd
  constructor
  · ext i
    change (y.2:ℝ)*((↑(x.1*e i+x.2*v i):ℝ)*w i) +
      (-(x.2:ℝ))*((↑(y.1*e i+y.2*v i):ℝ)*w i) = (e i:ℝ)*w i
    push_cast
    linear_combination (e i:ℝ)*w i*h
  · ext i
    change (-(y.1:ℝ))*((↑(x.1*e i+x.2*v i):ℝ)*w i) +
      (x.1:ℝ)*((↑(y.1*e i+y.2*v i):ℝ)*w i) = (v i:ℝ)*w i
    push_cast
    linear_combination (v i:ℝ)*w i*h

/-- The L1 norm of the transverse difference equals the sum of the weighted coordinate errors. -/
theorem normTransverse (w : I → ℝ) (hw : ∀ i, 0 < w i) (e v : I → ℤ) (t : ℝ) :
    ‖_root_.AbcTwoNinths.Basic.embed w v - t • _root_.AbcTwoNinths.Basic.embed w e‖ = ∑ i, |(v i:ℝ)-t*(e i:ℝ)| * w i := by
  rw [PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro i _
  change |(v i:ℝ)*w i - t*((e i:ℝ)*w i)| = _
  rw [show (v i:ℝ)*w i-t*((e i:ℝ)*w i) = ((v i:ℝ)-t*(e i:ℝ))*w i by ring,
    abs_mul, abs_of_pos (hw i)]

/--
Two rationally independent integer vectors with a nonzero first vector admit a determinant-one basis reduced under integer shears.
-/
theorem actualReducedBasis {e v : I → ℤ} {j : I} (hj : e j ≠ 0)
    (hind : ¬ ∃ r : ℚ, ∀ i, (v i : ℚ) = r * (e i : ℚ))
    {w : I → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ x y : _root_.AbcTwoNinths.Basic.ZPair, _root_.AbcTwoNinths.Basic.det x y = 1 ∧
      ‖_root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x)‖ ≤ ‖_root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y)‖ ∧
      ∀ n : ℤ, ‖_root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y)‖ ≤
        ‖(n:ℝ) • _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x) + _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y)‖ := by
  obtain ⟨x,y,hd,h₁,h₂⟩ := _root_.AbcTwoNinths.Basic.weightedBasis hj hind hw
  refine ⟨x,y,hd,?_,fun n => ?_⟩
  · simpa only [_root_.AbcTwoNinths.Basic.normEmbed w hw] using h₁
  · rw [← _root_.AbcTwoNinths.Basic.embedShear, _root_.AbcTwoNinths.Basic.normEmbed w hw, _root_.AbcTwoNinths.Basic.normEmbed w hw]
    exact h₂ n

/--
A strict transverse mass bound yields determinant-one columns with a mass-product bound and two coordinate bounds.
-/
theorem collisionRectangle {e v : I → ℤ} {j : I} (hj : e j ≠ 0)
    (hind : ¬ ∃ r : ℚ, ∀ i, (v i : ℚ) = r * (e i : ℚ))
    {w : I → ℝ} (hw : ∀ i, 0 < w i) {t T : ℝ}
    (herr : ∑ i, |(v i:ℝ)-t*(e i:ℝ)| * w i < T) :
    ∃ x y : _root_.AbcTwoNinths.Basic.ZPair, _root_.AbcTwoNinths.Basic.det x y = 1 ∧
      _root_.AbcTwoNinths.Basic.mass w (_root_.AbcTwoNinths.Basic.eval e v x) * _root_.AbcTwoNinths.Basic.mass w (_root_.AbcTwoNinths.Basic.eval e v y) < 12 * _root_.AbcTwoNinths.Basic.mass w e * T ∧
      |(y.2 : ℝ)| * _root_.AbcTwoNinths.Basic.mass w (_root_.AbcTwoNinths.Basic.eval e v x) ≤ 3 * _root_.AbcTwoNinths.Basic.mass w e ∧
      |(x.2 : ℝ)| * _root_.AbcTwoNinths.Basic.mass w (_root_.AbcTwoNinths.Basic.eval e v y) ≤ 2 * _root_.AbcTwoNinths.Basic.mass w e := by
  obtain ⟨x,y,hd,h₁,h₂⟩ := _root_.AbcTwoNinths.Basic.actualReducedBasis hj hind hw
  let X := _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v x)
  let Y := _root_.AbcTwoNinths.Basic.embed w (_root_.AbcTwoNinths.Basic.eval e v y)
  let a : ℝ := y.2
  let b : ℝ := -(x.2 : ℝ)
  let c : ℝ := -(y.1 : ℝ)
  let d : ℝ := x.1
  obtain ⟨he,hv⟩ := _root_.AbcTwoNinths.Basic.unimodularExpansion hd w e v
  change a • X + b • Y = _root_.AbcTwoNinths.Basic.embed w e at he
  change c • X + d • Y = _root_.AbcTwoNinths.Basic.embed w v at hv
  have hdet : a*d-b*c = 1 := by
    have h : (x.1:ℝ)*y.2 - x.2*y.1 = 1 := by exact_mod_cast hd
    dsimp [a,b,c,d]
    linarith
  have hdet' : |a*(d-t*b)-b*(c-t*a)| = 1 := by
    rw [show a*(d-t*b)-b*(c-t*a)=a*d-b*c by ring,hdet,abs_one]
  have htrans : (c-t*a) • X + (d-t*b) • Y = _root_.AbcTwoNinths.Basic.embed w v - t • _root_.AbcTwoNinths.Basic.embed w e := by
    rw [← he, ← hv]
    module
  have hprod := _root_.AbcTwoNinths.Basic.determinantProduct X Y h₁ h₂ a b _ _ hdet'
  have hc := _root_.AbcTwoNinths.Basic.coordBounds X Y h₁ h₂ a b
  rw [he,htrans,_root_.AbcTwoNinths.Basic.normTransverse w hw] at hprod
  rw [he] at hc
  simp only [_root_.AbcTwoNinths.Basic.normEmbed w hw] at hprod hc
  have hn : 0 < _root_.AbcTwoNinths.Basic.mass w e := by
    have hp : 0 < |(e j:ℝ)| * w j :=
      mul_pos (abs_pos.mpr (by exact_mod_cast hj)) (hw j)
    exact hp.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (abs_nonneg ((e i):ℝ)) (hw i).le) (Finset.mem_univ j))
  have hlt := hprod.trans_lt (mul_lt_mul_of_pos_left herr (show 0 < 12*_root_.AbcTwoNinths.Basic.mass w e by positivity))
  dsimp only [X,Y,a,b] at hlt hc
  simp only [_root_.AbcTwoNinths.Basic.normEmbed w hw,abs_neg] at hlt hc
  exact ⟨x,y,hd,hlt,hc⟩

end

end AbcTwoNinths.Basic
