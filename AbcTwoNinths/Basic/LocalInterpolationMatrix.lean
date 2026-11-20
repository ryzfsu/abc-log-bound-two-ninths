/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalGridTransport
public import AbcTwoNinths.Basic.PadicDeterminantDivisibility

/-!
# Local Interpolation Matrix

The module transfers divisibility in the local rational ring to integer divisibility after unit scaling.

## Main results
* `AbcTwoNinths.Basic.localErrorDvd`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

/-- The subring of rationals integral at the prime p. -/
def localRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {a | _root_.AbcTwoNinths.Basic.IntegralAt p a}
  zero_mem' := by simp [_root_.AbcTwoNinths.Basic.IntegralAt]
  one_mem' := by simp [_root_.AbcTwoNinths.Basic.IntegralAt]
  mul_mem' := _root_.AbcTwoNinths.Basic.integralMul
  neg_mem' := by
    intro a h
    change 0 ≤ padicValRat p (-a)
    rwa [padicValRat.neg]
  add_mem' := by
    intro a b ha hb
    change 0 ≤ padicValRat p (a+b)
    by_cases h : a+b = 0
    · simp [h]
    · exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add h)

/-- Regard a rational integral at p as an element of the corresponding subring. -/
def localRat (p : ℕ) [Fact p.Prime] (a : ℚ) (ha : _root_.AbcTwoNinths.Basic.IntegralAt p a) : _root_.AbcTwoNinths.Basic.localRing p :=
  ⟨a, ha⟩

/-- Every natural number maps to a rational integral at p. -/
theorem integralNat (p n : ℕ) [Fact p.Prime] : _root_.AbcTwoNinths.Basic.IntegralAt p (n : ℚ) := by
  simp [_root_.AbcTwoNinths.Basic.IntegralAt, padicValRat.of_nat]

/--
In the ring of p-integral rationals, divisibility by a power of p is equivalent to congruence to zero at that precision.
-/
theorem localDvdIff {p n : ℕ} [Fact p.Prime] (a : _root_.AbcTwoNinths.Basic.localRing p) :
    (p : _root_.AbcTwoNinths.Basic.localRing p)^n ∣ a ↔ _root_.AbcTwoNinths.Basic.RatCongruent p n a.val 0 := by
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hval : padicValRat p ((p : ℚ)^n) = n := by simp [padicValRat.pow, padicValRat.of_nat]
  constructor
  · rintro ⟨b,hb⟩
    have h : a.val = (p : ℚ)^n * b.val := by
      exact congrArg (fun u : _root_.AbcTwoNinths.Basic.localRing p => u.val) hb
    by_cases hz : b.val = 0
    · exact Or.inl (by simp [h,hz])
    · right
      rw [sub_zero, h, padicValRat.mul (pow_ne_zero _ hpq) hz, hval]
      exact le_add_of_nonneg_right b.property
  · intro h
    by_cases hz : a.val = 0
    · have : a = 0 := Subtype.ext hz
      rw [this]
      exact dvd_zero _
    · have h' := h.resolve_left hz
      rw [sub_zero] at h'
      refine ⟨⟨a.val / (p : ℚ)^n, ?_⟩, ?_⟩
      · change 0 ≤ padicValRat p (a.val / (p : ℚ)^n)
        rw [padicValRat.div hz (pow_ne_zero _ hpq), hval]
        exact sub_nonneg.mpr h'
      · apply Subtype.ext
        change a.val = (p : ℚ)^n * (a.val / (p : ℚ)^n)
        field_simp

/--
A congruence between two p-integral rationals gives prime-power divisibility of their difference in the integral subring.
-/
theorem localErrorDvd {p n : ℕ} [Fact p.Prime] (a b : _root_.AbcTwoNinths.Basic.localRing p)
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p n a.val b.val) : (p : _root_.AbcTwoNinths.Basic.localRing p)^n ∣ a-b := by
  apply (_root_.AbcTwoNinths.Basic.localDvdIff (a-b)).2
  rcases h with h | h
  · exact Or.inl (sub_eq_zero.mpr h)
  · exact Or.inr (by simpa using h)

end

end AbcTwoNinths.Basic
