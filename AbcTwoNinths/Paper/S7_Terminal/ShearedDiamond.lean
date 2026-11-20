/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.CellCount

/-!
# Sheared Diamond

The module computes the area of a sheared diamond and compares it with its finite lattice-site count. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.diamondSitesSpec`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

noncomputable section
open Set MeasureTheory MeasureTheory.Measure


section

/--
The first coordinate after applying the basis map and the shear of slope ξ. This is used in Section 7 of the paper.
-/
def shear (c : ℝ) (u v : _root_.AbcTwoNinths.Basic.Plane) : _root_.AbcTwoNinths.Basic.Plane →ₗ[ℝ] ℝ :=
  (u.1 + c * u.2) • LinearMap.fst ℝ ℝ ℝ +
  (v.1 + c * v.2) • LinearMap.snd ℝ ℝ ℝ

/-- The second coordinate after applying the basis map. This is used in Section 7 of the paper. -/
def ordinate (u v : _root_.AbcTwoNinths.Basic.Plane) : _root_.AbcTwoNinths.Basic.Plane →ₗ[ℝ] ℝ :=
  u.2 • LinearMap.fst ℝ ℝ ℝ + v.2 • LinearMap.snd ℝ ℝ ℝ

/--
The sum of the absolute weighted sheared abscissa and ordinate in basis coordinates. This is used in Section 7 of the paper.
-/
def diamond (c h t : ℝ) (u v : _root_.AbcTwoNinths.Basic.Plane) : Seminorm ℝ _root_.AbcTwoNinths.Basic.Plane :=
  (normSeminorm ℝ ℝ).comp (h • _root_.AbcTwoNinths.Terminal.shear c u v) +
  (normSeminorm ℝ ℝ).comp (t • _root_.AbcTwoNinths.Terminal.ordinate u v)

/--
The sum and difference of the weighted coordinates defining the diamond. This is used in Section 7 of the paper.
-/
def squareMap (c h t : ℝ) (u v : _root_.AbcTwoNinths.Basic.Plane) : _root_.AbcTwoNinths.Basic.Plane →ₗ[ℝ] _root_.AbcTwoNinths.Basic.Plane :=
  (h • _root_.AbcTwoNinths.Terminal.shear c u v + t • _root_.AbcTwoNinths.Terminal.ordinate u v).prod
  (h • _root_.AbcTwoNinths.Terminal.shear c u v - t • _root_.AbcTwoNinths.Terminal.ordinate u v)

/-- Evaluate the diamond seminorm for nonnegative weights. -/
theorem diamondApply (c h t : ℝ) (u v z : _root_.AbcTwoNinths.Basic.Plane) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    _root_.AbcTwoNinths.Terminal.diamond c h t u v z = |_root_.AbcTwoNinths.Terminal.shear c u v z| * h + |_root_.AbcTwoNinths.Terminal.ordinate u v z| * t := by
  change |h * _root_.AbcTwoNinths.Terminal.shear c u v z| + |t * _root_.AbcTwoNinths.Terminal.ordinate u v z| = _
  rw [abs_mul, abs_mul, abs_of_nonneg hh, abs_of_nonneg ht]
  ring

/-- The determinant of the square map is the basis determinant times −2ht. -/
theorem squareMapDet (c h t : ℝ) (u v : _root_.AbcTwoNinths.Basic.Plane) :
    LinearMap.det (_root_.AbcTwoNinths.Terminal.squareMap c h t u v) = -2 * h * t * (u.1 * v.2 - v.1 * u.2) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, _root_.AbcTwoNinths.Terminal.squareMap, _root_.AbcTwoNinths.Terminal.shear, _root_.AbcTwoNinths.Terminal.ordinate,
    Module.Basis.finTwoProd]
  ring

/-- The unit diamond has area 2/(ht) in a basis of absolute determinant one. -/
theorem diamondVolume (c : ℝ) {h t : ℝ} (u v : _root_.AbcTwoNinths.Basic.Plane)
    (hh : 0 < h) (ht : 0 < t)
    (hd : |u.1 * v.2 - v.1 * u.2| = 1) :
    volume ((_root_.AbcTwoNinths.Terminal.diamond c h t u v).closedBall 0 1) = ENNReal.ofReal (2 / (h * t)) := by
  have hdet : |LinearMap.det (_root_.AbcTwoNinths.Terminal.squareMap c h t u v)| = 2 * h * t := by
    rw [_root_.AbcTwoNinths.Terminal.squareMapDet, abs_mul, abs_mul, abs_mul, hd]
    simp [abs_of_pos hh, abs_of_pos ht]
  have hn : LinearMap.det (_root_.AbcTwoNinths.Terminal.squareMap c h t u v) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hdet
    exact (by positivity : 0 < 2 * h * t).ne' hdet.symm
  have hpre : (_root_.AbcTwoNinths.Terminal.diamond c h t u v).closedBall 0 1 =
      _root_.AbcTwoNinths.Terminal.squareMap c h t u v ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    ext z
    rw [Seminorm.mem_closedBall_zero]
    change |h * _root_.AbcTwoNinths.Terminal.shear c u v z| + |t * _root_.AbcTwoNinths.Terminal.ordinate u v z| ≤ 1 ↔
      ((-1 ≤ h * _root_.AbcTwoNinths.Terminal.shear c u v z + t * _root_.AbcTwoNinths.Terminal.ordinate u v z ∧
        h * _root_.AbcTwoNinths.Terminal.shear c u v z + t * _root_.AbcTwoNinths.Terminal.ordinate u v z ≤ 1) ∧
       (-1 ≤ h * _root_.AbcTwoNinths.Terminal.shear c u v z - t * _root_.AbcTwoNinths.Terminal.ordinate u v z ∧
        h * _root_.AbcTwoNinths.Terminal.shear c u v z - t * _root_.AbcTwoNinths.Terminal.ordinate u v z ≤ 1))
    generalize h * _root_.AbcTwoNinths.Terminal.shear c u v z = a
    generalize t * _root_.AbcTwoNinths.Terminal.ordinate u v z = b
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb <;>
      simp only [abs_of_nonneg, abs_of_nonpos, ha, hb] <;>
      constructor <;> intro hs
    all_goals first | exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩ | linarith [hs.1.1, hs.1.2, hs.2.1, hs.2.2]
  rw [hpre, addHaar_preimage_linearMap volume hn, abs_inv, hdet, volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/--
The cell radius bounds the cardinality of a finite enumeration of diamond sites from both sides.
-/
theorem diamondCounts (c : ℝ) {h t r δ : ℝ} (u v : _root_.AbcTwoNinths.Basic.Plane)
    (hh : 0 < h) (ht : 0 < t)
    (hd : |u.1 * v.2 - v.1 * u.2| = 1)
    (hr : 0 ≤ r) (hδ : 0 < δ) (s : Finset _root_.AbcTwoNinths.Basic.Sites)
    (hs : ∀ i, i ∈ s ↔ _root_.AbcTwoNinths.Terminal.diamond c h t u v (_root_.AbcTwoNinths.Basic.lift i) ≤ r)
    (hcell : (_root_.AbcTwoNinths.Terminal.diamond c h t u v _root_.AbcTwoNinths.Basic.e₁ + _root_.AbcTwoNinths.Terminal.diamond c h t u v _root_.AbcTwoNinths.Basic.e₂) / 2 ≤ δ) :
    2 / (h * t) * (max (r - δ) 0)^2 ≤ (s.card : ℝ) ∧
      (s.card : ℝ) ≤ 2 / (h * t) * (r + δ)^2 := by
  have hb := _root_.AbcTwoNinths.Basic.countBounds _ hr hδ s hs hcell
  rw [_root_.AbcTwoNinths.Terminal.diamondVolume c u v hh ht hd,
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_natCast s.card] at hb
  exact ⟨by simpa [mul_comm] using (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb.1,
    by simpa [mul_comm] using (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb.2⟩

/-- At any real radius only finitely many integer coefficient pairs lie in the weighted diamond. -/
theorem diamondFinite (c : ℝ) {h t r : ℝ} (u v : _root_.AbcTwoNinths.Basic.Plane)
    (hh : 0 < h) (ht : 0 < t)
    (hd : |u.1 * v.2 - v.1 * u.2| = 1) :
    ({i : _root_.AbcTwoNinths.Basic.Sites | _root_.AbcTwoNinths.Terminal.diamond c h t u v (_root_.AbcTwoNinths.Basic.lift i) ≤ r}).Finite := by
  classical
  let f := _root_.AbcTwoNinths.Terminal.squareMap c h t u v
  have hraw : u.1 * v.2 - v.1 * u.2 ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hn : LinearMap.det f ≠ 0 := by
    dsimp [f]
    rw [_root_.AbcTwoNinths.Terminal.squareMapDet]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh.ne') ht.ne') hraw
  let e := (f.equivOfDetNeZero hn).toContinuousLinearEquiv
  let box : Set _root_.AbcTwoNinths.Basic.Plane := Icc (-r) r ×ˢ Icc (-r) r
  have hb : IsCompact (e.symm '' box) :=
    (isCompact_Icc.prod isCompact_Icc).image e.symm.continuous
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : _root_.AbcTwoNinths.Basic.Plane)).mp hb.isBounded
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply ((Set.finite_Icc (a := -(N : ℤ)) (b := (N : ℤ))).prod
    (Set.finite_Icc (a := -(N : ℤ)) (b := (N : ℤ)))).subset
  intro i hi
  change |h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i)| + |t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i)| ≤ r at hi
  have hbox : e (_root_.AbcTwoNinths.Basic.lift i) ∈ box := by
    change (-r ≤ h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i) + t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i) ∧
      h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i) + t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i) ≤ r) ∧
      (-r ≤ h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i) - t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i) ∧
      h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i) - t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i) ≤ r)
    generalize h * _root_.AbcTwoNinths.Terminal.shear c u v (_root_.AbcTwoNinths.Basic.lift i) = a at *
    generalize t * _root_.AbcTwoNinths.Terminal.ordinate u v (_root_.AbcTwoNinths.Basic.lift i) = b at *
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  have hz := hR ⟨e (_root_.AbcTwoNinths.Basic.lift i), hbox, e.symm_apply_apply _⟩
  have hnorm : ‖_root_.AbcTwoNinths.Basic.lift i‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at hnorm
  change |(i.1 : ℝ)| < R ∧ |(i.2 : ℝ)| < R at hnorm
  have hx := abs_lt.mp (hnorm.1.trans hN)
  have hy := abs_lt.mp (hnorm.2.trans hN)
  exact ⟨⟨by exact_mod_cast hx.1.le, by exact_mod_cast hx.2.le⟩,
    ⟨by exact_mod_cast hy.1.le, by exact_mod_cast hy.2.le⟩⟩

/--
The finite set of coefficient pairs in the closed diamond. This is used in Section 7 of the paper.
-/
noncomputable def diamondBall (c : ℝ) {h t r : ℝ} (u v : _root_.AbcTwoNinths.Basic.Plane)
    (hh : 0 < h) (ht : 0 < t) (hd : |u.1 * v.2 - v.1 * u.2| = 1) : Finset _root_.AbcTwoNinths.Basic.Sites :=
  (_root_.AbcTwoNinths.Terminal.diamondFinite (r := r) c u v hh ht hd).toFinset

/--
An integer pair belongs to the coefficient set exactly when its diamond seminorm is at most the radius.
-/
@[simp] theorem memDiamondBall (c : ℝ) {h t r : ℝ} (u v : _root_.AbcTwoNinths.Basic.Plane)
    (hh : 0 < h) (ht : 0 < t) (hd : |u.1 * v.2 - v.1 * u.2| = 1) (i : _root_.AbcTwoNinths.Basic.Sites) :
    i ∈ _root_.AbcTwoNinths.Terminal.diamondBall (r := r) c u v hh ht hd ↔ _root_.AbcTwoNinths.Terminal.diamond c h t u v (_root_.AbcTwoNinths.Basic.lift i) ≤ r :=
  Set.Finite.mem_toFinset _

/--
Send an integer pair to the corresponding linear combination of the two lattice vectors. This is used in Section 7 of the paper.
-/
def siteMap (u v : _root_.AbcTwoNinths.Basic.Sites) (i : _root_.AbcTwoNinths.Basic.Sites) : _root_.AbcTwoNinths.Basic.Sites :=
  (i.1 * u.1 + i.2 * v.1, i.1 * u.2 + i.2 * v.2)

/-- A nonzero basis determinant makes the integer coordinate map injective. -/
theorem siteMapInjective (u v : _root_.AbcTwoNinths.Basic.Sites) (hd : u.1 * v.2 - v.1 * u.2 ≠ 0) :
    Function.Injective (_root_.AbcTwoNinths.Terminal.siteMap u v) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  dsimp [_root_.AbcTwoNinths.Terminal.siteMap] at h1 h2
  have h3 : (x.1 - y.1) * (u.1 * v.2 - v.1 * u.2) = 0 := by
    linear_combination v.2 * h1 - v.1 * h2
  have h4 : (x.2 - y.2) * (u.1 * v.2 - v.1 * u.2) = 0 := by
    linear_combination u.1 * h2 - u.2 * h1
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hd))

/--
The sheared height of the lattice site (i,j) is h abs(i+ξj) + t abs(j). This is used in Section 7 of the paper.
-/
def siteHeight (c h t : ℝ) (i : _root_.AbcTwoNinths.Basic.Sites) : ℝ :=
  |(i.1 : ℝ) + c * (i.2 : ℝ)| * h + |(i.2 : ℝ)| * t

/-- The seminorm of a coefficient pair equals the diamond height of its lattice image. -/
theorem diamondSiteMap (c : ℝ) {h t : ℝ} (u v i : _root_.AbcTwoNinths.Basic.Sites) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    _root_.AbcTwoNinths.Terminal.diamond c h t (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) (_root_.AbcTwoNinths.Basic.lift i) = _root_.AbcTwoNinths.Terminal.siteHeight c h t (_root_.AbcTwoNinths.Terminal.siteMap u v i) := by
  rw [_root_.AbcTwoNinths.Terminal.diamondApply _ _ _ _ _ _ hh ht]
  simp [_root_.AbcTwoNinths.Terminal.siteHeight, _root_.AbcTwoNinths.Terminal.siteMap, _root_.AbcTwoNinths.Basic.lift, _root_.AbcTwoNinths.Terminal.shear, _root_.AbcTwoNinths.Terminal.ordinate]
  congr 2 <;> ring

/--
The seminorm on the two coordinate unit vectors gives the heights of the corresponding lattice vectors.
-/
theorem diamondBasis (c : ℝ) {h t : ℝ} (u v : _root_.AbcTwoNinths.Basic.Sites) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    _root_.AbcTwoNinths.Terminal.diamond c h t (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) _root_.AbcTwoNinths.Basic.e₁ = _root_.AbcTwoNinths.Terminal.siteHeight c h t u ∧
    _root_.AbcTwoNinths.Terminal.diamond c h t (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) _root_.AbcTwoNinths.Basic.e₂ = _root_.AbcTwoNinths.Terminal.siteHeight c h t v := by
  constructor
  · simpa [_root_.AbcTwoNinths.Basic.lift, _root_.AbcTwoNinths.Basic.e₁, _root_.AbcTwoNinths.Terminal.siteMap] using _root_.AbcTwoNinths.Terminal.diamondSiteMap c u v (1, 0) hh ht
  · simpa [_root_.AbcTwoNinths.Basic.lift, _root_.AbcTwoNinths.Basic.e₂, _root_.AbcTwoNinths.Terminal.siteMap] using _root_.AbcTwoNinths.Terminal.diamondSiteMap c u v (0, 1) hh ht

/--
The image of the closed coefficient diamond in the integer lattice. This is used in Section 7 of the paper.
-/
noncomputable def diamondSites (c : ℝ) {h t r : ℝ} (u v : _root_.AbcTwoNinths.Basic.Sites)
    (hh : 0 < h) (ht : 0 < t)
    (hd : |(u.1 : ℝ) * v.2 - (v.1 : ℝ) * u.2| = 1) : Finset _root_.AbcTwoNinths.Basic.Sites :=
  (_root_.AbcTwoNinths.Terminal.diamondBall (r := r) c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd).image (_root_.AbcTwoNinths.Terminal.siteMap u v)

/--
Count the sites of a closed diamond, bound their heights, and include them in every larger concentric diamond. This is used in Section 7 of the paper.
-/
theorem diamondSitesSpec (c : ℝ) {h t r δ : ℝ} (u v : _root_.AbcTwoNinths.Basic.Sites)
    (hh : 0 < h) (ht : 0 < t) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hd : |(u.1 : ℝ) * v.2 - (v.1 : ℝ) * u.2| = 1)
    (hc : (_root_.AbcTwoNinths.Terminal.siteHeight c h t u + _root_.AbcTwoNinths.Terminal.siteHeight c h t v) / 2 ≤ δ) :
    let s := _root_.AbcTwoNinths.Terminal.diamondSites (r := r) c u v hh ht hd
    2 / (h * t) * (max (r - δ) 0)^2 ≤ (s.card : ℝ) ∧
      (s.card : ℝ) ≤ 2 / (h * t) * (r + δ)^2 ∧
      (∀ i ∈ s, _root_.AbcTwoNinths.Terminal.siteHeight c h t i ≤ r) ∧
      ∀ r' : ℝ, r ≤ r' → s ⊆ _root_.AbcTwoNinths.Terminal.diamondSites (r := r') c u v hh ht hd := by
  dsimp only
  have hi : u.1 * v.2 - v.1 * u.2 ≠ 0 := by
    intro hz
    have hz' : (u.1 : ℝ) * v.2 - (v.1 : ℝ) * u.2 = 0 := by exact_mod_cast hz
    simp [hz'] at hd
  obtain ⟨h1, h2⟩ := _root_.AbcTwoNinths.Terminal.diamondBasis c u v hh.le ht.le
  have hb := _root_.AbcTwoNinths.Terminal.diamondCounts c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd hr hδ _
    (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd) (by simpa only [h1, h2])
  unfold _root_.AbcTwoNinths.Terminal.diamondSites
  rw [Finset.card_image_of_injective _ (_root_.AbcTwoNinths.Terminal.siteMapInjective u v hi)]
  refine ⟨hb.1, hb.2, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [← _root_.AbcTwoNinths.Terminal.diamondSiteMap c u v j hh.le ht.le]
    exact (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd j).mp hj
  · intro r' hr' i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨j, (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd j).mpr
      (((_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd j).mp hj).trans hr'), rfl⟩

end

end
end AbcTwoNinths.Terminal
