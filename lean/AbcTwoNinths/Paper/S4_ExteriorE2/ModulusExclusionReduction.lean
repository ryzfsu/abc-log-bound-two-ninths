/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PlaneBasis
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimeMassReduction
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison

/-!
# Modulus Exclusion Reduction

The module constructs a reduced plane containing the distinguished source direction. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.existsReducedRoofPlane`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
A short nonzero roof projection gives two generators of the kernel plane with coprime roof coefficients and controlled weighted heights. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsReducedRoofPlane {I G : Type*} [Fintype I] [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) {k : ℤ} (hk : k ≠ 0) (v : I → ℤ)
    (hv : Sum.elim (fun _ : Unit => k) v ∈ r.ker)
    {a : (Unit ⊕ I) → ℤ} (ha : a ∈ r.ker) (i : I)
    (hai : _root_.AbcTwoNinths.Basic.roofProjection k v a i ≠ 0)
    (hprim : ∀ z ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v z = 0 →
      ∃ m : ℤ, z = m • Sum.elim (fun _ : Unit => k) v)
    (w : (Unit ⊕ I) → ℝ) (hw : ∀ j, 0 < w j) (ρ : ℝ)
    (hshort : ∑ j, w (.inr j) * |_root_.AbcTwoNinths.Basic.roofProjection k v a j| ≤ ρ) :
    let V := Sum.elim (fun _ : Unit => k) v
    let K := _root_.AbcTwoNinths.ExteriorE2.roofPlane r k v a i
    let H (z : (Unit ⊕ I) → ℤ) := _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (z j : ℝ))
    ∃ u ∈ K, ∃ z ∈ K, ∃ c d : ℤ,
      V = c • u + d • z ∧ c.gcd d = 1 ∧
      (∀ l ∈ K, ∃ p q : ℤ, l = p • u + q • z) ∧
      0 < H u ∧ 0 < H z ∧ H u * H z ≤ 4 * H V * ρ ∧
      |(c : ℝ)| * H u ≤ 3 * H V ∧ |(d : ℝ)| * H z ≤ 2 * H V := by
  classical
  let V := Sum.elim (fun _ : Unit => k) v
  let K := _root_.AbcTwoNinths.ExteriorE2.roofPlane r k v a i
  let P := _root_.AbcTwoNinths.Basic.roofProjection k v
  let f := _root_.AbcTwoNinths.ExteriorE1.heightSeminorm w (fun j => (hw j).le)
  obtain ⟨b, hb, hgen, _, n', _, hPn⟩ := _root_.AbcTwoNinths.ExteriorE2.existsRoofPlaneBasis r hk v ha i hai hprim
  have hbP : P b i ≠ 0 := by
    intro h
    have e := congrFun hPn i
    change P a i = (n' • P b) i at e
    simp only [Pi.smul_apply, h, smul_zero] at e
    exact hai e
  have hvK : V ∈ K := by
    refine ⟨hv, fun j => ?_⟩
    change P V j * P a i = P V i * P a j
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have h (l : I) : P V l = 0 := by
      change (v l : ℝ) - (k : ℝ) / k * (v l : ℝ) = 0
      simp [hkR]
    rw [h, h, zero_mul, zero_mul]
  have hv0 : V ≠ 0 := by
    intro h
    exact hk (congrFun h (.inl ()))
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hind (p q : ℝ)
      (h : p • (fun j => (V j : ℝ)) + q • (fun j => (b j : ℝ)) = 0) :
      p = 0 ∧ q = 0 := by
    have h0 := congrFun h (.inl ())
    have hi := congrFun h (.inr i)
    change p * (k : ℝ) + q * (b (.inl ()) : ℝ) = 0 at h0
    change p * (v i : ℝ) + q * (b (.inr i) : ℝ) = 0 at hi
    have e : q * P b i = 0 := by
      change q * ((b (.inr i) : ℝ) - (b (.inl ()) : ℝ) / k * (v i : ℝ)) = 0
      apply (mul_left_cancel₀ hkR)
      rw [mul_zero]
      field_simp
      linear_combination (k : ℝ) * hi - (v i : ℝ) * h0
    have hq := (mul_eq_zero.mp e).resolve_right hbP
    rw [hq, zero_mul, add_zero] at h0
    exact ⟨(mul_eq_zero.mp h0).resolve_right hkR, hq⟩
  have haK : a ∈ K := ⟨ha, fun _ => mul_comm _ _⟩
  obtain ⟨j, n, han⟩ := hgen a haK
  have hn : n ≠ 0 := by
    intro hn
    have e := congrArg P han
    rw [hn, zero_smul, add_zero, map_smul] at e
    have hPV : P V = 0 := by
      funext l
      change (v l : ℝ) - (k : ℝ) / k * (v l : ℝ) = 0
      simp [hkR]
    change P a = j • P V at e
    rw [hPV, smul_zero] at e
    exact hai (congrFun e i)
  let shift : ℝ := (a (.inl ()) : ℝ) / k
  let y : (Unit ⊕ I) → ℝ := fun l => (a l : ℝ) - shift * (V l : ℝ)
  have hy : y = Sum.elim (fun _ : Unit => (0 : ℝ)) (P a) := by
    funext l
    cases l with
    | inl l =>
      cases l
      change (a (.inl ()) : ℝ) - (a (.inl ()) : ℝ) / k * k = 0
      rw [div_mul_cancel₀ _ hkR, sub_self]
    | inr l => rfl
  have hyHeight : f y ≤ ρ := by
    have hsum : (∑ l, w l * |y l|) ≤ ρ := by
      simpa [hy, Fintype.sum_sum_type] using hshort
    change _root_.AbcTwoNinths.ExteriorE1.height w y ≤ ρ
    unfold _root_.AbcTwoNinths.ExteriorE1.height
    apply max_le <;> unfold _root_.AbcTwoNinths.ExteriorE1.positiveWeight <;>
      refine le_trans (Finset.sum_le_sum (fun l _ => ?_)) hsum
    · exact mul_le_mul_of_nonneg_left
        (max_le (le_abs_self _) (abs_nonneg _)) (hw _).le
    · exact mul_le_mul_of_nonneg_left
        (max_le (neg_le_abs _) (abs_nonneg _)) (hw _).le
  have hshift : y = (j : ℝ) • (fun l => (V l : ℝ)) +
      (n : ℝ) • (fun l => (b l : ℝ)) - shift • (fun l => (V l : ℝ)) := by
    funext l
    have h := congrFun han l
    change a l = j * V l + n * b l at h
    have e : (a l : ℝ) = (j : ℝ) * (V l : ℝ) + (n : ℝ) * (b l : ℝ) := by exact_mod_cast h
    change (a l : ℝ) - shift * (V l : ℝ) = _
    rw [e]
    rfl
  rw [hshift] at hyHeight
  exact _root_.AbcTwoNinths.ExteriorE2.existsReducedHeightBasis K f (_root_.AbcTwoNinths.ExteriorE1.heightContinuous w (fun l => (hw l).le))
    (_root_.AbcTwoNinths.ExteriorE1.heightPosOfNeZero w hw) w hw (_root_.AbcTwoNinths.ExteriorE1.coordLeHeight w (fun l => (hw l).le))
    V b hvK hb hv0 hgen hind j n hn shift ρ hyHeight

end

end AbcTwoNinths.ExteriorE2
