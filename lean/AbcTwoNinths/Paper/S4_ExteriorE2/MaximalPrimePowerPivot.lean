/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Maximal Prime Power Pivot

The module orients the exponent coordinates so that a maximal pivot has the required sign. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.orientMaxPivot`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
A nonzero vector in an integer function subgroup admits a sign with a positive coordinate of largest absolute value. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem orientMaxPivot {I : Type*} [Fintype I] (K : AddSubgroup (I → ℤ))
    (a : I → ℤ) (ha : a ∈ K) (hn : a ≠ 0) :
    ∃ p : I, ∃ b ∈ K, (b = a ∨ b = -a) ∧ 0 < b p ∧
      ∀ i, (a i).natAbs ≤ (b p).natAbs := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ (fun j => (a j).natAbs)
    (Finset.univ_nonempty_iff.mpr ⟨i⟩)
  have hmax (j) := hp j (Finset.mem_univ j)
  have hnz : a p ≠ 0 := by
    intro he
    have h := hmax i
    rw [he] at h
    exact hi (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero h))
  by_cases h : 0 < a p
  · exact ⟨p,a,ha,Or.inl rfl,h,hmax⟩
  · refine ⟨p,-a,K.neg_mem ha,Or.inr rfl,?_,?_⟩
    · change 0 < -(a p)
      omega
    · simpa using hmax

end

end AbcTwoNinths.ExteriorE2
