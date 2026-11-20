/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Composite Interpolation Nodes

The module proves injectivity or noninjectivity of a grid node map from bounds on its coordinate widths. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.nodeZInjectiveOfSecondWidth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section


/--
For coprime coefficients c and d, the map (r, s) to r d + s c is injective on the rectangle when its first coordinate is bounded by R < c.
-/
theorem nodeZInjectiveOfWidth {c d R S : ℕ} (hc : c.Coprime d)
    (hR : R < c) : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R) (S := S) c d) := by
  have hc0 : 0 < c := Nat.zero_lt_of_lt hR
  intro x y h
  have hxd : c ∣ (x.1.val - y.1.val) * d := by
    rw [Nat.sub_mul]
    change x.1.val * d + x.2.val * c = y.1.val * d + y.2.val * c at h
    have hh : x.1.val * d - y.1.val * d = y.2.val * c - x.2.val * c := by omega
    rw [hh, ← Nat.sub_mul]
    exact dvd_mul_left _ _
  have hyd : c ∣ (y.1.val - x.1.val) * d := by
    rw [Nat.sub_mul]
    change x.1.val * d + x.2.val * c = y.1.val * d + y.2.val * c at h
    have hh : y.1.val * d - x.1.val * d = x.2.val * c - y.2.val * c := by omega
    rw [hh, ← Nat.sub_mul]
    exact dvd_mul_left _ _
  have hx := hc.dvd_of_dvd_mul_right hxd
  have hy := hc.dvd_of_dvd_mul_right hyd
  have hx0 : x.1.val - y.1.val = 0 := by
    by_contra hne
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hx
    have hl := x.1.isLt
    omega
  have hy0 : y.1.val - x.1.val = 0 := by
    by_contra hne
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hy
    have hl := y.1.isLt
    omega
  have hxy : x.1.val = y.1.val := by omega
  change x.1.val * d + x.2.val * c = y.1.val * d + y.2.val * c at h
  rw [hxy, Nat.add_left_cancel_iff] at h
  exact Prod.ext (Fin.ext hxy) (Fin.ext (Nat.eq_of_mul_eq_mul_right hc0 h))

/--
For coprime coefficients c and d, the map (r, s) to r d + s c is injective on the rectangle when its second coordinate is bounded by S < d. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem nodeZInjectiveOfSecondWidth {c d R S : ℕ} (hc : c.Coprime d)
    (hS : S < d) : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R) (S := S) c d) := by
  intro x y h
  have hh : _root_.AbcTwoNinths.Basic.nodeZ (R := S) (S := R) d c x.swap = _root_.AbcTwoNinths.Basic.nodeZ d c y.swap := by
    simpa only [_root_.AbcTwoNinths.Basic.nodeZ, Prod.fst_swap, Prod.snd_swap, add_comm] using h
  exact Prod.swap_injective (_root_.AbcTwoNinths.ExteriorE2.nodeZInjectiveOfWidth hc.symm hS hh)

end

end AbcTwoNinths.ExteriorE2
