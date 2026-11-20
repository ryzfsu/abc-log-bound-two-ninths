/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Saturated Plane

The module constructs an integral basis of the lattice cut out by a rational plane.

## Main results
* `AbcTwoNinths.Basic.saturatedPlaneBasisExists`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/-- An integer vector belongs to the real span of the two given integer vectors. -/
def inPlane {ι : Type*} (w u z : ι → ℤ) : Prop :=
  ∃ a b : ℝ, ∀ i, (z i : ℝ) = a * (w i : ℝ) + b * (u i : ℝ)

/--
A primitive line generator extends to a basis of the integer points in its real plane with unique integral coordinates.
-/
theorem saturatedPlaneBasisExists {ι : Type*}
    (w u : ι → ℤ) (r : ι) (hr : w r ≠ 0)
    (hprim : ∀ (z : ι → ℤ) (s : ℝ), (∀ i, (z i : ℝ) = s * (w i : ℝ)) →
      ∃ k : ℤ, z = k • w)
    (hind : ¬ ∃ s : ℝ, ∀ i, (u i : ℝ) = s * (w i : ℝ)) :
    ∃ z₀ : ι → ℤ, _root_.AbcTwoNinths.Basic.inPlane w u z₀ ∧
      (∀ z : ι → ℤ, _root_.AbcTwoNinths.Basic.inPlane w u z → ∃! c : ℤ × ℤ, z = c.1 • w + c.2 • z₀) ∧
      (∃ j k : ℤ, k ≠ 0 ∧ u = j • w + k • z₀) := by
  classical
  have hrR : (w r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hminor : ∃ i, w r * u i - w i * u r ≠ 0 := by
    by_contra! h
    apply hind
    refine ⟨(u r : ℝ) / (w r : ℝ), fun i => ?_⟩
    have hh : (w r : ℝ) * (u i : ℝ) - (w i : ℝ) * (u r : ℝ) = 0 := by
      exact_mod_cast h i
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hrR).2
    nlinarith only [hh]
  obtain ⟨i, hi⟩ := hminor
  let ψ : (ι → ℤ) →+ ℤ :=
    { toFun := fun z => w r * z i - w i * z r
      map_zero' := by simp
      map_add' := by intro x y; change w r * (x i + y i) - w i * (x r + y r) = _; ring }
  have hψw : ψ w = 0 := by change w r * w i - w i * w r = 0; ring
  have hψu : ψ u ≠ 0 := hi
  have hup : _root_.AbcTwoNinths.Basic.inPlane w u u := ⟨0, 1, by simp⟩
  have hneg {z : ι → ℤ} (hz : _root_.AbcTwoNinths.Basic.inPlane w u z) : _root_.AbcTwoNinths.Basic.inPlane w u (-z) := by
    obtain ⟨a, b, hab⟩ := hz
    exact ⟨-a, -b, fun j => by simp only [Pi.neg_apply, Int.cast_neg, hab]; ring⟩
  have hsub {x y : ι → ℤ} (hx : _root_.AbcTwoNinths.Basic.inPlane w u x) (hy : _root_.AbcTwoNinths.Basic.inPlane w u y) (k : ℤ) :
      _root_.AbcTwoNinths.Basic.inPlane w u (x - k • y) := by
    obtain ⟨a, b, hab⟩ := hx
    obtain ⟨c, d, hcd⟩ := hy
    refine ⟨a - (k : ℝ) * c, b - (k : ℝ) * d, fun j => ?_⟩
    change ((x j - k * y j : ℤ) : ℝ) = _
    push_cast
    rw [hab, hcd]
    ring
  have hkernel (z : ι → ℤ) (hz : _root_.AbcTwoNinths.Basic.inPlane w u z) (hzero : ψ z = 0) :
      ∃ k : ℤ, z = k • w := by
    obtain ⟨a, b, hab⟩ := hz
    have he : (w r : ℝ) * (z i : ℝ) - (w i : ℝ) * (z r : ℝ) = 0 := by
      exact_mod_cast hzero
    have hdu : (w r : ℝ) * (u i : ℝ) - (w i : ℝ) * (u r : ℝ) ≠ 0 := by
      exact_mod_cast hψu
    rw [hab i, hab r] at he
    have hb : b = 0 := (mul_eq_zero.mp
      (show b * ((w r : ℝ) * (u i : ℝ) - (w i : ℝ) * (u r : ℝ)) = 0 by
        linear_combination he)).resolve_right hdu
    exact hprim z a (by simpa [hb] using hab)
  let P (n : ℕ) := ∃ z : ι → ℤ, _root_.AbcTwoNinths.Basic.inPlane w u z ∧ 0 < n ∧ ψ z = (n : ℤ)
  have hP : ∃ n, P n := by
    by_cases hp : 0 < ψ u
    · exact ⟨(ψ u).toNat, u, hup, by omega, by omega⟩
    · exact ⟨(-ψ u).toNat, -u, hneg hup, by omega, by rw [map_neg]; omega⟩
  obtain ⟨z₀, hz₀, hn, heq⟩ := Nat.find_spec hP
  have hp₀ : 0 < ψ z₀ := by omega
  have hrep (z : ι → ℤ) (hz : _root_.AbcTwoNinths.Basic.inPlane w u z) :
      ∃! c : ℤ × ℤ, z = c.1 • w + c.2 • z₀ := by
    let q := ψ z / ψ z₀
    let z' := z - q • z₀
    have hz' := hsub hz hz₀ q
    have hrem : ψ z' = ψ z % ψ z₀ := by
      change ψ (z - q • z₀) = _
      rw [map_sub, map_zsmul]
      change ψ z - q * ψ z₀ = _
      have h := Int.ediv_mul_add_emod (ψ z) (ψ z₀)
      dsimp [q]
      linarith only [h]
    have hnn := Int.emod_nonneg (ψ z) hp₀.ne'
    have hlt := Int.emod_lt_of_pos (ψ z) hp₀
    have hzero : ψ z' = 0 := by
      by_contra hne
      have hsmall : (ψ z').toNat < Nat.find hP := by omega
      exact Nat.find_min hP hsmall ⟨z', hz', by omega, by omega⟩
    obtain ⟨k, hk⟩ := hkernel z' hz' hzero
    have hdecomp : z = k • w + q • z₀ := by
      change z - q • z₀ = k • w at hk
      exact sub_eq_iff_eq_add.mp hk
    refine ⟨(k, q), hdecomp, ?_⟩
    rintro ⟨a, b⟩ hab
    have hb : b = q := by
      have hh := congrArg ψ (hab.symm.trans hdecomp)
      change ψ (a • w + b • z₀) = ψ (k • w + q • z₀) at hh
      rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
        hψw, smul_zero, smul_zero, zero_add, zero_add] at hh
      exact mul_right_cancel₀ hp₀.ne' hh
    have ha : a = k := by
      have hh := congrFun (hab.symm.trans hdecomp) r
      change a * w r + b * z₀ r = k * w r + q * z₀ r at hh
      rw [hb] at hh
      exact mul_right_cancel₀ hr (add_right_cancel hh)
    exact Prod.ext ha hb
  refine ⟨z₀, hz₀, hrep, ?_⟩
  obtain ⟨⟨j, k⟩, hjk, _⟩ := hrep u hup
  refine ⟨j, k, ?_, hjk⟩
  intro h
  apply hψu
  rw [hjk]
  change ψ (j • w + k • z₀) = 0
  rw [map_add, map_zsmul, map_zsmul, hψw, h, smul_zero, zero_smul, zero_add]

end

end AbcTwoNinths.Basic
