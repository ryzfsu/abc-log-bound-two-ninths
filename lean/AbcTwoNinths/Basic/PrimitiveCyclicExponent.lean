/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Primitive Cyclic Exponent

The module produces a primitive cyclic exponent when the support is a singleton.

## Main results
* `AbcTwoNinths.Basic.primitiveCyclicExponent`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
A primitive integer exponent annihilating an element of a finite group has absolute value equal to its order.
-/
theorem primitiveCyclicExponent {G : Type*} [Group G] [Finite G] (u : G) {e : ℤ}
    (he : u ^ e = 1)
    (hprim : ∀ (n : ℕ) (v : ℤ), u ^ v = 1 → (n : ℤ) * v = e → n = 1) :
    e.natAbs = orderOf u := by
  obtain ⟨v, hv⟩ := (orderOf_dvd_iff_zpow_eq_one.mpr he)
  have hpos : 0 < orderOf u := orderOf_pos u
  have hs : ∃ s : ℤ, s.natAbs = 1 ∧ (v.natAbs : ℤ) * s = v := by
    by_cases h : 0 ≤ v
    · exact ⟨1, by decide, by rw [mul_one, Int.natCast_natAbs, abs_of_nonneg h]⟩
    · exact ⟨-1, by decide, by rw [mul_neg_one, Int.natCast_natAbs, abs_of_neg (by omega)]; simp⟩
  obtain ⟨s, hs, hsv⟩ := hs
  have hkernel : u ^ ((orderOf u : ℤ) * s) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp ⟨s, rfl⟩
  have hn := hprim v.natAbs ((orderOf u : ℤ) * s) hkernel (by
    calc
      _ = (orderOf u : ℤ) * ((v.natAbs : ℤ) * s) := by ring
      _ = e := by rw [hsv, ← hv])
  rw [hv, Int.natAbs_mul, Int.natAbs_natCast, hn, mul_one]

end

end AbcTwoNinths.Basic
