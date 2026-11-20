/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.PlaneCoordinateHeight

/-!
# Independent Plane Minor

The module finds a nonzero coordinate minor of an independent pair and deduces injectivity of the plane map. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.planeMapInjectiveOfMinor`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
Two integer rows with nonzero first row and no rational proportionality have a nonzero coordinate minor.
-/
theorem existsNonzeroMinorOfInd {ι : Type*} {e v : ι → ℤ} (he : e ≠ 0)
    (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ)) :
    ∃ i j, e i * v j - e j * v i ≠ 0 := by
  classical
  have hex : ∃ i, e i ≠ 0 := by
    by_contra! h
    exact he (funext h)
  obtain ⟨i, hi⟩ := hex
  by_contra! h
  apply hind
  refine ⟨(v i : ℚ) / (e i : ℚ), fun j => ?_⟩
  have hn : (e i : ℚ) ≠ 0 := by exact_mod_cast hi
  have hh : (e i : ℚ) * v j = (e j : ℚ) * v i := by
    exact_mod_cast sub_eq_zero.mp (h i j)
  field_simp
  linarith

/--
A nonzero coordinate minor makes the integer coefficient map into the exponent plane injective. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem planeMapInjectiveOfMinor {ι : Type*} {e v : ι → ℤ} {i j : ι}
    (hd : e i * v j - e j * v i ≠ 0) : Function.Injective (_root_.AbcTwoNinths.PolyCap.planeMap e v) := by
  intro x y h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [_root_.AbcTwoNinths.PolyCap.planeMap] at hi hj
  apply Prod.ext
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (e i * v j - e j * v i) * (x.1 - y.1) = 0 by
      linear_combination (v j) * hi - (v i) * hj)).resolve_left hd
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (e i * v j - e j * v i) * (x.2 - y.2) = 0 by
      linear_combination (e i) * hj - (e j) * hi)).resolve_left hd

end

end AbcTwoNinths.PolyCap
