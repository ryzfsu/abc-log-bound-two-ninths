/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Maximal Power Divisor

The module selects the maximal common power divisor of the exponent vector. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.maximalDivisor`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
A vector with a specified nonzero coordinate is a positive multiple of a primitive subgroup vector, with multiplier at most the absolute coordinate. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem maximalDivisor {ι : Type*} (K : AddSubgroup (ι → ℤ)) {e : ι → ℤ}
    (he : e ∈ K) {j : ι} (hj : e j ≠ 0) :
    ∃ (k : ℕ) (w : ι → ℤ), 0 < k ∧ k ≤ (e j).natAbs ∧
      w ∈ K ∧ k • w = e ∧ (∀ (n : ℕ) (u : ι → ℤ), u ∈ K → n • u = w → n = 1) := by
  classical
  let D := (e j).natAbs
  let S := (Finset.Icc 1 D).filter (fun k => ∃ w ∈ K, k • w = e)
  have hD : 0 < D := Int.natAbs_pos.mpr hj
  have h1 : 1 ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hD⟩, e, he, one_nsmul e⟩
  let k := S.max' ⟨1, h1⟩
  obtain ⟨hkI, w, hw, hkw⟩ := Finset.mem_filter.mp (S.max'_mem ⟨1, h1⟩)
  obtain ⟨hk, hkD⟩ := Finset.mem_Icc.mp hkI
  refine ⟨k, w, hk, hkD, hw, hkw, ?_⟩
  intro n u hu hnu
  have hprod : (k * n) • u = e := by rw [mul_smul, hnu, hkw]
  have hval := congrArg (fun v : ι → ℤ => (v j).natAbs) hprod
  have hval' : k * n * (u j).natAbs = D := by
    simpa [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul] using hval
  have hn : 0 < n := by
    by_contra! hh
    have : n = 0 := by omega
    simp [this] at hval'
    omega
  have huj : 0 < (u j).natAbs := by
    by_contra! hh
    have : (u j).natAbs = 0 := by omega
    simp [this] at hval'
    omega
  have hmem : k * n ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hk hn, by
      rw [← hval']
      exact Nat.le_mul_of_pos_right _ huj⟩, u, hu, hprod⟩
  have hmax := S.le_max' (k * n) hmem
  change k * n ≤ k at hmax
  nlinarith

end

end AbcTwoNinths.PolyCap
