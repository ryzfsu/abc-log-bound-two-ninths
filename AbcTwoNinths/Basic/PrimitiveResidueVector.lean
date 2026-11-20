/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Primitive Residue Vector

The module shows that an integral vector proportional to a primitive direction is an integer multiple and uses this to test independence.

## Main results
* `AbcTwoNinths.Basic.integralOfPrimitiveProportional`
* `AbcTwoNinths.Basic.independentOfPrimitivePivot`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
A vector is primitive in the subgroup if every natural scalar that represents it as a multiple of a subgroup vector equals one.
-/
def PrimitiveIn {ι : Type*} (Γ : AddSubgroup (ι → ℤ)) (e : ι → ℤ) : Prop :=
  ∀ (n : ℕ) (u : ι → ℤ), u ∈ Γ → n • u = e → n = 1

/--
A rational multiple of a primitive subgroup vector that lies in the subgroup has scalar equal to its integer numerator.
-/
theorem integralOfPrimitiveProportional {ι : Type*} {Γ : AddSubgroup (ι → ℤ)}
    {e v : ι → ℤ} (he : e ∈ Γ) (hv : v ∈ Γ) (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn Γ e)
    (r : ℚ) (hr : ∀ j, (v j : ℚ) = r * (e j : ℚ)) :
    r = (r.num : ℚ) := by
  have hcop : Int.gcd r.num (r.den : ℤ) = 1 := by
    simpa [Int.gcd] using r.reduced
  let a := Int.gcdA r.num (r.den : ℤ)
  let b := Int.gcdB r.num (r.den : ℤ)
  have hab : r.num * a + (r.den : ℤ) * b = 1 := by
    simpa [hcop, a, b] using (Int.gcd_eq_gcd_ab r.num (r.den : ℤ)).symm
  have hn : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hrv (j : ι) : (r.den : ℤ) * v j = r.num * e j := by
    have hj := hr j
    rw [← Rat.num_div_den r] at hj
    have hq : (r.den : ℚ) * (v j : ℚ) = (r.num : ℚ) * (e j : ℚ) := by
      field_simp [hn] at hj
      nlinarith
    exact_mod_cast hq
  have hu : a • v + b • e ∈ Γ := Γ.add_mem (Γ.zsmul_mem hv a) (Γ.zsmul_mem he b)
  have hde : r.den • (a • v + b • e) = e := by
    funext j
    change (r.den : ℤ) * (a * v j + b * e j) = e j
    calc
      _ = a * ((r.den : ℤ) * v j) + b * ((r.den : ℤ) * e j) := by ring
      _ = (r.num * a + (r.den : ℤ) * b) * e j := by rw [hrv]; ring
      _ = _ := by rw [hab, one_mul]
  have hd := hprim r.den _ hu hde
  simpa [hd] using (Rat.num_div_den r).symm

/--
A subgroup vector with pivot strictly between zero and the primitive pivot cannot be rationally proportional to the primitive vector.
-/
theorem independentOfPrimitivePivot {ι : Type*} {Γ : AddSubgroup (ι → ℤ)}
    {e v : ι → ℤ} (he : e ∈ Γ) (hv : v ∈ Γ) (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn Γ e)
    (h : ι) (hpos : 0 < v h) (hlt : v h < e h) :
    ¬ ∃ r : ℚ, ∀ j, (v j : ℚ) = r * (e j : ℚ) := by
  rintro ⟨r, hr⟩
  have hq := hr h
  rw [_root_.AbcTwoNinths.Basic.integralOfPrimitiveProportional he hv hprim r hr] at hq
  have hz : v h = r.num * e h := by exact_mod_cast hq
  have hep : 0 < e h := lt_trans hpos hlt
  by_cases hp : 0 < r.num
  · have hmul := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ r.num by omega) hep.le
    rw [one_mul, ← hz] at hmul
    exact (not_lt_of_ge hmul) hlt
  · have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) hep.le
    rw [← hz] at hmul
    exact (not_lt_of_ge hmul) hpos

end

end AbcTwoNinths.Basic
