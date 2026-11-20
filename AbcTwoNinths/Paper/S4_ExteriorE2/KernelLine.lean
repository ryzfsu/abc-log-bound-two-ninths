/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PlaneBasis

/-!
# Kernel Line

The module constructs a generator of the line singled out by the selected prime in the kernel. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.kernelRoofGenerator`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
A kernel vector with positive roof coordinate is a positive integral multiple of a kernel vector that generates every kernel vector annihilated by its roof projection. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem kernelRoofGenerator {I G : Type*} [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) {k : ℤ} (hk : 0 < k) (v : I → ℤ)
    (hv : Sum.elim (fun _ : Unit => k) v ∈ r.ker) :
    ∃ k' : ℤ, ∃ w : I → ℤ, ∃ g : ℤ, 0 < k' ∧ 0 < g ∧
      Sum.elim (fun _ : Unit => k') w ∈ r.ker ∧
      Sum.elim (fun _ : Unit => k) v = g • Sum.elim (fun _ : Unit => k') w ∧
      ∀ z ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k' w z = 0 →
        ∃ n : ℤ, z = n • Sum.elim (fun _ : Unit => k') w := by
  classical
  let V := Sum.elim (fun _ : Unit => k) v
  let P := _root_.AbcTwoNinths.Basic.roofProjection k v
  let K := r.ker ⊓ P.toAddMonoidHom.ker
  let f : ((Unit ⊕ I) → ℤ) →+ ℤ :=
    { toFun := fun z => z (.inl ()), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hV : V ∈ K := by
    refine ⟨hv, ?_⟩
    change P V = 0
    funext i
    change (v i : ℝ) - k / (k : ℝ) * v i = 0
    simp [hkR]
  obtain ⟨b, hb, hpos, hgen⟩ := _root_.AbcTwoNinths.ExteriorE2.existsPositiveGenerator K f hV (show f V ≠ 0 from hk.ne')
  have coord {z : (Unit ⊕ I) → ℤ} (hz : z ∈ K) (i : I) :
      (z (.inr i) : ℝ) = (f z : ℝ) / k * v i := by
    have h := congrFun (show P z = 0 from hz.2) i
    exact sub_eq_zero.mp h
  have inj {z y : (Unit ⊕ I) → ℤ} (hz : z ∈ K) (hy : y ∈ K) (he : f z = f y) : z = y := by
    funext j
    cases j with
    | inl j => cases j; exact he
    | inr i =>
      exact_mod_cast (show (z (.inr i) : ℝ) = y (.inr i) by rw [coord hz i, coord hy i, he])
  obtain ⟨g, hg⟩ := hgen V hV
  have hgpos : 0 < g := by
    by_contra! h
    exact (not_le_of_gt hk) (hg.trans_le (mul_nonpos_of_nonpos_of_nonneg h hpos.le))
  have hshape : b = Sum.elim (fun _ : Unit => f b) (fun i => b (.inr i)) := by
    funext j
    cases j with
    | inl j => cases j; rfl
    | inr i => rfl
  refine ⟨f b, fun i => b (.inr i), g, hpos, hgpos, hshape ▸ hb.1, ?_, ?_⟩
  · rw [← hshape]
    apply inj hV (K.zsmul_mem hb g)
    change f V = f (g • b)
    rw [map_zsmul, zsmul_eq_mul]
    exact hg
  · intro z hz hzero
    have hbR : (f b : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hzK : z ∈ K := by
      refine ⟨hz, ?_⟩
      change P z = 0
      funext i
      have h := congrFun hzero i
      change (z (.inr i) : ℝ) - (f z : ℝ) / (f b : ℝ) * (b (.inr i) : ℝ) = 0 at h
      change (z (.inr i) : ℝ) - (f z : ℝ) / k * v i = 0
      rw [coord hb i] at h
      convert h using 1
      field_simp [hbR, hkR]
    obtain ⟨n, hn⟩ := hgen z hzK
    refine ⟨n, ?_⟩
    rw [← hshape]
    apply inj hzK (K.zsmul_mem hb n)
    change f z = f (n • b)
    rw [map_zsmul, zsmul_eq_mul]
    exact hn

end

end AbcTwoNinths.ExteriorE2
