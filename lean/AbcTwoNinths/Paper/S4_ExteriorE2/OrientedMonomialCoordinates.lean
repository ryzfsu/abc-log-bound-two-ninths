/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Oriented Monomial Coordinates

Orients a lattice combination as a difference with positive coprime coefficients. Injective
monomial evaluation carries additive independence to multiplicative independence. It supports
Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.orientCoordinates`
* `AbcTwoNinths.ExteriorE2.monomialIndependent`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/-- The product and axis height bounds exclude a zero coordinate in a primitive pair. -/
theorem coordinatesNonzero {c d : ℤ} {U Z V C ell : ℝ}
    (hg : c.gcd d = 1) (hU : ell < U) (hZ : ell < Z)
    (hell : 0 < ell) (hC : C ≤ ell)
    (hprod : U * Z ≤ V * C)
    (hc0 : c = 0 → V = |(d : ℝ)| * Z)
    (hd0 : d = 0 → V = |(c : ℝ)| * U) :
    c ≠ 0 ∧ d ≠ 0 := by
  constructor
  · intro hc
    have hd : d.natAbs = 1 := by simpa [hc] using hg
    have hd' : |(d : ℝ)| = 1 := by exact_mod_cast (Int.abs_eq_natAbs d).trans (by exact_mod_cast hd)
    have h := hc0 hc
    rw [hd', one_mul] at h
    have hh := mul_lt_mul_of_pos_right (hC.trans_lt hU) (hell.trans hZ)
    rw [h] at hprod
    linarith only [hh, hprod, mul_comm C Z]
  · intro hd
    have hc : c.natAbs = 1 := by simpa [hd] using hg
    have hc' : |(c : ℝ)| = 1 := by exact_mod_cast (Int.abs_eq_natAbs c).trans (by exact_mod_cast hc)
    have h := hd0 hd
    rw [hc', one_mul] at h
    have hh := mul_lt_mul_of_pos_left (hC.trans_lt hZ) (hell.trans hU)
    rw [h] at hprod
    linarith only [hh, hprod]

/--
Signs can be chosen on two subgroup vectors to express their primitive combination as a difference with positive coprime coefficients.
-/
theorem orientCoordinates {A : Type*} [AddCommGroup A] {K : AddSubgroup A}
    {V u z : A} {c d : ℤ} (hu : u ∈ K) (hz : z ∈ K)
    (hc : c ≠ 0) (hd : d ≠ 0) (hg : c.gcd d = 1)
    (hV : V = c • u + d • z) :
    ∃ u' ∈ K, ∃ z' ∈ K,
      (u' = u ∨ u' = -u) ∧ (z' = z ∨ z' = -z) ∧
      0 < c.natAbs ∧ 0 < d.natAbs ∧ c.natAbs.Coprime d.natAbs ∧
      V = (c.natAbs : ℤ) • u' - (d.natAbs : ℤ) • z' := by
  let orient (a : ℤ) (v : A) := if 0 ≤ a then v else -v
  have hsign (a : ℤ) (v : A) : orient a v = v ∨ orient a v = -v := by
    unfold orient
    split <;> simp
  have hmul (a : ℤ) (v : A) : (a.natAbs : ℤ) • orient a v = a • v := by
    unfold orient
    split
    · rw [Int.natAbs_of_nonneg ‹0 ≤ a›]
    · rw [zsmul_neg, ← neg_zsmul]
      congr 1
      omega
  refine ⟨orient c u, ?_, -(orient d z), ?_, hsign c u, ?_,
    Int.natAbs_pos.mpr hc, Int.natAbs_pos.mpr hd, hg, ?_⟩
  · rcases hsign c u with h | h <;> rw [h]
    · exact hu
    · exact K.neg_mem hu
  · rcases hsign d z with h | h <;> rw [h]
    · exact K.neg_mem hz
    · simpa using hz
  · rcases hsign d z with h | h <;> simp [h]
  · rw [zsmul_neg, sub_neg_eq_add, hmul, hmul, ← hV]

/--
An injective character sends two integer-independent vectors to multiplicatively independent values. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem monomialIndependent {A G : Type*} [AddCommGroup A] [CommGroup G]
    (f : Multiplicative A →* G) (hf : Function.Injective f)
    (u z : A) (hind : ∀ m n : ℤ, m • u + n • z = 0 → m = 0 ∧ n = 0)
    (m n : ℤ) (h : f (Multiplicative.ofAdd u) ^ m *
      f (Multiplicative.ofAdd z) ^ n = 1) : m = 0 ∧ n = 0 := by
  apply hind
  have hh : f (Multiplicative.ofAdd (m • u + n • z)) = f 1 := by
    change f (Multiplicative.ofAdd u ^ m * Multiplicative.ofAdd z ^ n) = f 1
    simpa only [map_mul, map_zpow, map_one] using h
  exact Multiplicative.ofAdd.injective (hf hh)

end

end AbcTwoNinths.ExteriorE2
