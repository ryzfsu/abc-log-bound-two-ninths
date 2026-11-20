/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Module.Submodule.Basic
public import AbcTwoNinths.Basic.RoofCovolume

/-!
# Plane Basis

The module constructs a plane basis containing a positive generator along the distinguished direction. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.existsPositiveGenerator`
* `AbcTwoNinths.ExteriorE2.existsPlaneBasis`
* `AbcTwoNinths.ExteriorE2.existsRoofPlaneBasis`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
A nonzero integer functional on a subgroup attains a positive generator of its image. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsPositiveGenerator
    {E : Type*} [AddCommGroup E] (K : AddSubgroup E) (f : E →+ ℤ)
    {a : E} (ha : a ∈ K) (hfa : f a ≠ 0) :
    ∃ b ∈ K, 0 < f b ∧ ∀ z ∈ K, ∃ m : ℤ, f z = m * f b := by
  classical
  let P (n : ℕ) := 0 < n ∧ ∃ z ∈ K, f z = (n : ℤ)
  have hP : ∃ n, P n := by
    by_cases h : 0 < f a
    · exact ⟨(f a).toNat, by omega, a, ha, by omega⟩
    · refine ⟨(-f a).toNat, by omega, -a, K.neg_mem ha, ?_⟩
      rw [map_neg]
      omega
  obtain ⟨hn, b, hb, hbn⟩ := Nat.find_spec hP
  have hpos : 0 < f b := by omega
  refine ⟨b, hb, hpos, ?_⟩
  intro z hz
  let m := f z / f b
  let e := z - m • b
  have he : e ∈ K := K.sub_mem hz (K.zsmul_mem hb m)
  have hef : f e = f z % f b := by
    change f (z - m • b) = _
    rw [map_sub, map_zsmul, zsmul_eq_mul]
    have h := Int.emod_add_ediv_mul (f z) (f b)
    dsimp [m]
    linarith only [h]
  have he0 : f e = 0 := by
    have hl := Int.emod_nonneg (f z) hpos.ne'
    have hu := Int.emod_lt_of_pos (f z) hpos
    by_contra h
    have hsmall : (f e).toNat < Nat.find hP := by omega
    have hnew : P (f e).toNat := ⟨by omega, e, he, by omega⟩
    exact (Nat.not_lt_of_ge (Nat.find_min' hP hnew)) hsmall
  change f (z - m • b) = 0 at he0
  rw [map_sub, map_zsmul] at he0
  change f z - m * f b = 0 at he0
  exact ⟨m, sub_eq_zero.mp he0⟩

/--
A generator of the zero fiber with infinite order extends to an independent pair spanning the subgroup when the functional has nonzero image. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsPlaneBasis
    {E : Type*} [AddCommGroup E] (K : AddSubgroup E) (f : E →+ ℤ)
    {v a : E} (ha : a ∈ K) (hfa : f a ≠ 0)
    (hfv : f v = 0) (hvind : ∀ m : ℤ, m • v = 0 → m = 0)
    (hprim : ∀ z ∈ K, f z = 0 → ∃ m : ℤ, z = m • v) :
    ∃ b ∈ K, 0 < f b ∧
      (∀ z ∈ K, ∃ m n : ℤ, z = m • v + n • b) ∧
      (∀ m n : ℤ, m • v + n • b = 0 → m = 0 ∧ n = 0) := by
  obtain ⟨b, hb, hbpos, hgen⟩ := _root_.AbcTwoNinths.ExteriorE2.existsPositiveGenerator K f ha hfa
  refine ⟨b, hb, hbpos, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := hgen z hz
    obtain ⟨m, hm⟩ := hprim (z - n • b) (K.sub_mem hz (K.zsmul_mem hb n)) (by
      rw [map_sub, map_zsmul]
      change f z - n * f b = 0
      rw [hn, sub_self])
    exact ⟨m, n, sub_eq_iff_eq_add.mp hm⟩
  · intro m n h
    have hf := congrArg f h
    simp only [map_add, map_zsmul, hfv, smul_zero, zero_add, map_zero] at hf
    change n * f b = 0 at hf
    have hn : n = 0 := (mul_eq_zero.mp hf).resolve_right hbpos.ne'
    exact ⟨hvind m (by simpa [hn] using h), hn⟩



/--
The residue-kernel vectors whose roof projections satisfy the cross-product equations at a specified coordinate. This is used in the proof of Proposition 4.1 of the paper.
-/
def roofPlane {I G : Type*} [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) (k : ℤ) (v : I → ℤ)
    (a : (Unit ⊕ I) → ℤ) (i : I) : AddSubgroup ((Unit ⊕ I) → ℤ) where
  carrier := {z | z ∈ r.ker ∧ ∀ j,
    _root_.AbcTwoNinths.Basic.roofProjection k v z j * _root_.AbcTwoNinths.Basic.roofProjection k v a i =
      _root_.AbcTwoNinths.Basic.roofProjection k v z i * _root_.AbcTwoNinths.Basic.roofProjection k v a j}
  zero_mem' := ⟨r.ker.zero_mem, by simp⟩
  add_mem' {x y} hx hy := ⟨r.ker.add_mem hx.1 hy.1, fun j => by
    simp only [map_add, Pi.add_apply, add_mul]
    rw [hx.2 j, hy.2 j]⟩
  neg_mem' {x} hx := ⟨r.ker.neg_mem hx.1, fun j => by
    simp only [map_neg, Pi.neg_apply, neg_mul]
    rw [hx.2 j]⟩

/--
For a nonzero projected coordinate and a primitive zero fiber, two independent vectors span the plane and the given projection is a nonzero integer multiple of the second projection. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsRoofPlaneBasis {I G : Type*} [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) {k : ℤ} (hk : k ≠ 0) (v : I → ℤ)
    {a : (Unit ⊕ I) → ℤ} (ha : a ∈ r.ker) (i : I)
    (hai : _root_.AbcTwoNinths.Basic.roofProjection k v a i ≠ 0)
    (hprim : ∀ z ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v z = 0 →
      ∃ m : ℤ, z = m • Sum.elim (fun _ : Unit => k) v) :
    let V := Sum.elim (fun _ : Unit => k) v
    let K := _root_.AbcTwoNinths.ExteriorE2.roofPlane r k v a i
    ∃ b ∈ K,
      (∀ z ∈ K, ∃ m n : ℤ, z = m • V + n • b) ∧
      (∀ m n : ℤ, m • V + n • b = 0 → m = 0 ∧ n = 0) ∧
      ∃ n : ℤ, n ≠ 0 ∧ _root_.AbcTwoNinths.Basic.roofProjection k v a = n • _root_.AbcTwoNinths.Basic.roofProjection k v b := by
  let V := Sum.elim (fun _ : Unit => k) v
  let K := _root_.AbcTwoNinths.ExteriorE2.roofPlane r k v a i
  let P := _root_.AbcTwoNinths.Basic.roofProjection k v
  let f : ((Unit ⊕ I) → ℤ) →+ ℤ :=
    { toFun := fun z => k * z (.inr i) - v i * z (.inl ())
      map_zero' := by simp
      map_add' := by intros; simp only [Pi.add_apply]; ring }
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hf (z) : (f z : ℝ) = (k : ℝ) * P z i := by
    change ((k * z (.inr i) - v i * z (.inl ()) : ℤ) : ℝ) =
      (k : ℝ) * ((z (.inr i) : ℝ) - (z (.inl ()) : ℝ) / k * (v i : ℝ))
    push_cast
    field_simp
  have haK : a ∈ K := ⟨ha, fun j => mul_comm _ _⟩
  have hfa : f a ≠ 0 := by
    intro h
    exact mul_ne_zero hkR hai (by simpa [h] using (hf a).symm)
  have hfv : f V = 0 := sub_eq_zero.mpr (mul_comm k (v i))
  have hV (m : ℤ) (h : m • V = 0) : m = 0 := by
    have e := congrFun h (.inl ())
    change m * k = 0 at e
    exact (mul_eq_zero.mp e).resolve_right hk
  have hzero (z) (hz : z ∈ K) (hfz : f z = 0) : P z = 0 := by
    have hzi : P z i = 0 :=
      (mul_eq_zero.mp (by simpa [hfz] using (hf z).symm)).resolve_left hkR
    funext j
    change P z j = 0
    have h := hz.2 j
    change P z j * P a i = P z i * P a j at h
    rw [hzi, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hai
  obtain ⟨b, hb, -, hgen, hind⟩ := _root_.AbcTwoNinths.ExteriorE2.existsPlaneBasis K f haK hfa hfv hV
    (fun z hz hfz => hprim z hz.1 (hzero z hz hfz))
  have hPV : P V = 0 := by
    funext j
    change (v j : ℝ) - (k : ℝ) / k * (v j : ℝ) = 0
    simp [hkR]
  obtain ⟨m, n, h⟩ := hgen a haK
  have hP : P a = n • P b := by
    have e := congrArg P h
    simpa only [map_add, map_smul, hPV, smul_zero, zero_add] using e
  refine ⟨b, hb, hgen, hind, n, ?_, hP⟩
  intro hn
  exact hai (by simpa [hn] using congrFun hP i)

end

end AbcTwoNinths.ExteriorE2
