/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialHeightDistance
public import AbcTwoNinths.Paper.S4_ExteriorE2.ReducedHeight
public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedPlaneBasisChange

/-!
# Small Prime Mass Reduction

The module constructs a basis with reduced weighted heights. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.existsReducedHeightBasis`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
A short transverse translate gives a generating integral basis with bounded height product and weighted coordinates of the original vector. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsReducedHeightBasis {I : Type*} [Fintype I]
    (K : AddSubgroup (I → ℤ)) (f : Seminorm ℝ (I → ℝ)) (hf : Continuous f)
    (hpos : ∀ z : I → ℝ, z ≠ 0 → 0 < f z)
    (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ z : I → ℝ, ∀ i, w i * |z i| ≤ f z)
    (v b : I → ℤ) (hv : v ∈ K) (hb : b ∈ K) (hv0 : v ≠ 0)
    (hgen : ∀ z ∈ K, ∃ p q : ℤ, z = p • v + q • b)
    (hind : ∀ p q : ℝ, p • (fun i => (v i : ℝ)) + q • (fun i => (b i : ℝ)) = 0 →
      p = 0 ∧ q = 0)
    (j n : ℤ) (hn : n ≠ 0) (shift ρ : ℝ)
    (hshort : f ((j : ℝ) • (fun i => (v i : ℝ)) + (n : ℝ) • (fun i => (b i : ℝ)) -
      shift • (fun i => (v i : ℝ))) ≤ ρ) :
    ∃ u ∈ K, ∃ z ∈ K, ∃ c d : ℤ,
      v = c • u + d • z ∧ c.gcd d = 1 ∧
      (∀ a ∈ K, ∃ p q : ℤ, a = p • u + q • z) ∧
      let V := f (fun i => (v i : ℝ))
      let U := f (fun i => (u i : ℝ))
      let Z := f (fun i => (z i : ℝ))
      0 < U ∧ 0 < Z ∧ U * Z ≤ 4 * V * ρ ∧
        |(c : ℝ)| * U ≤ 3 * V ∧ |(d : ℝ)| * Z ≤ 2 * V := by
  let C : (I → ℤ) →ₗ[ℤ] (I → ℝ) :=
    { toFun := fun z i => (z i : ℝ)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp [zsmul_eq_mul] }
  have hC : Function.Injective C := by
    intro x y h
    funext i
    have e : (x i : ℝ) = (y i : ℝ) := congrFun h i
    exact_mod_cast e
  have hcs (m : ℤ) (z : I → ℤ) : C (m • z) = (m : ℝ) • C z := by
    ext i
    change ((m * z i : ℤ) : ℝ) = (m : ℝ) * (z i : ℝ)
    push_cast
    rfl
  have hp (z : I → ℤ) (hz : z ≠ 0) : 0 < f (C z) :=
    hpos _ (fun e => hz (hC (e.trans C.map_zero.symm)))
  obtain ⟨u, hu, hu0, hmin⟩ := _root_.AbcTwoNinths.ExteriorE2.existsShortestIntegerVector K (fun z => f (C z))
    w hw (fun a i => hcoord (C a) i) hv hv0
  obtain ⟨p, q, hu'⟩ := hgen u hu
  have hg := _root_.AbcTwoNinths.ExteriorE2.gcdEqOneOfShortest K (fun z => f (C z)) (fun m z => by
    rw [hcs, map_smul_eq_mul, Real.norm_eq_abs]) hv hb hu0 hp hmin p q hu'
  obtain ⟨r, s, hdet⟩ := _root_.AbcTwoNinths.ExteriorE2.existsUnimodularCompanion p q hg
  let a := r • v + s • b
  have ha : a ∈ K := K.add_mem (K.zsmul_mem hv r) (K.zsmul_mem hb s)
  have hcu : C u = (p : ℝ) • C v + (q : ℝ) • C b := by
    rw [hu', map_add, hcs, hcs]
  have hca : C a = (r : ℝ) • C v + (s : ℝ) • C b := by
    simp only [a, map_add, hcs]
  have hdetR : (p : ℝ) * s - (q : ℝ) * r = 1 := by exact_mod_cast hdet
  have hai : ¬ ∃ k : ℝ, C a = k • C u := by
    rintro ⟨k, hk⟩
    have e : ((r : ℝ) - k * p) • C v + ((s : ℝ) - k * q) • C b = 0 := by
      rw [hcu] at hk
      rw [hca] at hk
      calc
        _ = ((r : ℝ) • C v + (s : ℝ) • C b) -
            k • ((p : ℝ) • C v + (q : ℝ) • C b) := by module
        _ = 0 := sub_eq_zero.mpr hk
    obtain ⟨e₁, e₂⟩ := hind _ _ e
    have e₁' : (r : ℝ) = k * p := sub_eq_zero.mp e₁
    have e₂' : (s : ℝ) = k * q := sub_eq_zero.mp e₂
    rw [e₁', e₂'] at hdetR
    ring_nf at hdetR
    exact zero_ne_one hdetR
  obtain ⟨t, D, hD, ht, htmin⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.existsAttainedQuotientDistOfContinuous
      f hf (C u) (C a) (hp u hu0) hai hpos
  let m : ℤ := round t
  let z := a - m • u
  have hz : z ∈ K := K.sub_mem ha (K.zsmul_mem hu m)
  have hcz : C z = C a - (m : ℝ) • C u := by rw [show z = a - m • u from rfl, map_sub, hcs]
  have hz0 : z ≠ 0 := by
    intro h
    apply hai
    refine ⟨(m : ℝ), sub_eq_zero.mp ?_⟩
    rw [← hcz, h, map_zero]
  have hsu : f (C u) ≤ f (C a - (round t : ℝ) • C u) := hcz ▸ hmin z hz hz0
  have hvb := _root_.AbcTwoNinths.ExteriorE2.inverseUnimodularBasis v b p q r s hdet
  change v = s • (p • v + q • b) + (-q) • a ∧
    b = (-r) • (p • v + q • b) + p • a at hvb
  rw [← hu'] at hvb
  have hvZ : v = (s - m * q) • u + (-q) • z := by
    rw [hvb.1]
    dsimp [z]
    module
  have hbZ : b = (-r + m * p) • u + p • z := by
    rw [hvb.2]
    dsimp [z]
    module
  have hcop : (s - m * q).gcd (-q) = 1 := by
    apply Nat.dvd_one.mp
    rw [Int.gcd_dvd_iff]
    refine ⟨p, r - m * p, ?_⟩
    have hd := _root_.AbcTwoNinths.ExteriorE2.roundedBasisDet p q r s m hdet
    change (1 : ℤ) = _
    linarith only [hd]
  have hvC : C v = (s : ℝ) • C u + (-(q : ℝ)) • C a := by
    have h := congrArg C hvb.1
    simp only [map_add, hcs, Int.cast_neg] at h
    exact h
  have hbC : C b = (-(r : ℝ)) • C u + (p : ℝ) • C a := by
    have h := congrArg C hvb.2
    simp only [map_add, hcs, Int.cast_neg] at h
    exact h
  let x := (j : ℝ) - shift
  let y := (j : ℝ) • C v + (n : ℝ) • C b - shift • C v
  have hy : y = (x * s - n * r) • C u + (-x * q + n * p) • C a := by
    dsimp [y, x]
    rw [hvC, hbC]
    module
  have hdet' : 1 ≤ |(s : ℝ) * (-x * q + n * p) - (-(q : ℝ)) * (x * s - n * r)| := by
    have h : (s : ℝ) * (-x * q + n * p) - (-(q : ℝ)) * (x * s - n * r) = n := by
      linear_combination (n : ℝ) * hdetR
    rw [h]
    exact_mod_cast (show (1 : ℤ) ≤ |n| from Int.add_one_le_of_lt (abs_pos.mpr hn))
  have hprod := _root_.AbcTwoNinths.ExteriorE2.reducedHeightProduct f (C u) (C a) (C v) y t D (f (C v)) ρ
    hD.le htmin ht hsu (apply_nonneg f _) le_rfl hshort _ _ _ _ hvC hy hdet'
  have hvc : C v = ((s - m * q : ℤ) : ℝ) • C u + ((-q : ℤ) : ℝ) • C z := by
    have h := congrArg C hvZ
    simpa only [map_add, hcs] using h
  have hcoeff := _root_.AbcTwoNinths.ExteriorE2.reducedHeightCoeffs f (C u) (C a) t D htmin ht hsu
    ((s - m * q : ℤ) : ℝ) ((-q : ℤ) : ℝ)
  dsimp only at hcoeff
  rw [← hcz, ← hvc] at hcoeff
  rw [← hcz] at hprod
  refine ⟨u, hu, z, hz, s - m * q, -q, hvZ, hcop, ?_, hp u hu0, hp z hz0,
    hprod, hcoeff.1, hcoeff.2⟩
  intro l hl
  obtain ⟨α, β, h⟩ := hgen l hl
  refine ⟨α * (s - m * q) + β * (-r + m * p), α * (-q) + β * p, ?_⟩
  rw [h, hvZ, hbZ]
  module

end

end AbcTwoNinths.ExteriorE2
