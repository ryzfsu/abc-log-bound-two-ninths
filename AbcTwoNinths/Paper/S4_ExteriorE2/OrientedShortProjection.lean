/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModulusExclusionReduction
public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedMonomialCoordinates

/-!
# Oriented Short Projection

The module builds and orients an independent plane from a short projection and bounds its basis height product. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.orientedPlaneOfShortProjection`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




private theorem independentPlaneOfShortProjection
    {I G : Type*} [Fintype I] [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) {k : ℤ} (hk : k ≠ 0) (v : I → ℤ)
    (hV : Sum.elim (fun _ : Unit => k) v ∈ r.ker)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => k) v)
    (w : (Unit ⊕ I) → ℝ) (hw : ∀ j, 0 < w j) (Q : ℕ)
    (hshort : ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection k v a i| < 1 / (Q : ℝ)) :
    let V := Sum.elim (fun _ : Unit => k) v
    let ht (a : (Unit ⊕ I) → ℤ) := _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (a j : ℝ))
    ∃ u ∈ r.ker, ∃ z ∈ r.ker, ∃ c d : ℤ,
      V = c • u + d • z ∧ c.gcd d = 1 ∧
      (∀ m n : ℤ, m • u + n • z = 0 → m = 0 ∧ n = 0) ∧
      0 < ht u ∧ 0 < ht z ∧
      ht u * ht z ≤ 4 * ht V * ((∑ i, w (.inr i)) / (Q : ℝ)) ∧
      |(c : ℝ)| * ht u ≤ 3 * ht V ∧ |(d : ℝ)| * ht z ≤ 2 * ht V := by
  classical
  obtain ⟨a, ha, hproj, hsmall⟩ := hshort
  obtain ⟨i, hi⟩ : ∃ i, _root_.AbcTwoNinths.Basic.roofProjection k v a i ≠ 0 := by
    by_contra! h
    exact hproj (funext h)
  have hsum : ∑ j, w (.inr j) * |_root_.AbcTwoNinths.Basic.roofProjection k v a j| ≤
      (∑ j, w (.inr j)) / (Q : ℝ) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by simpa only [one_div] using (hsmall j).le) (hw _).le
  obtain ⟨u, hu, z, hz, c, d, he, hcd, hspan, hu0, hz0, hp, hc, hd⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.existsReducedRoofPlane r hk v hV ha i hi hgen w hw _ hsum
  have haK : a ∈ _root_.AbcTwoNinths.ExteriorE2.roofPlane r k v a i := ⟨ha, fun _ => mul_comm _ _⟩
  obtain ⟨p, q, hapq⟩ := hspan a haK
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hindet : k * a (.inr i) - v i * a (.inl ()) ≠ 0 := by
    intro h
    have hR : (k : ℝ) * (a (.inr i) : ℝ) - (v i : ℝ) * (a (.inl ()) : ℝ) = 0 := by
      exact_mod_cast h
    apply hi
    change (a (.inr i) : ℝ) - (a (.inl ()) : ℝ) / k * (v i : ℝ) = 0
    field_simp
    linarith
  have he0 := congrFun he (.inl ())
  have he1 := congrFun he (.inr i)
  have ha0 := congrFun hapq (.inl ())
  have ha1 := congrFun hapq (.inr i)
  change k = c * u (.inl ()) + d * z (.inl ()) at he0
  change v i = c * u (.inr i) + d * z (.inr i) at he1
  change a (.inl ()) = p * u (.inl ()) + q * z (.inl ()) at ha0
  change a (.inr i) = p * u (.inr i) + q * z (.inr i) at ha1
  have hdet : u (.inl ()) * z (.inr i) - u (.inr i) * z (.inl ()) ≠ 0 := by
    intro hzero
    apply hindet
    rw [he0, he1, ha0, ha1]
    linear_combination (c * q - d * p) * hzero
  refine ⟨u, hu.1, z, hz.1, c, d, he, hcd, ?_, hu0, hz0, hp, hc, hd⟩
  intro m n hmn
  have f0 := congrFun hmn (.inl ())
  have f1 := congrFun hmn (.inr i)
  change m * u (.inl ()) + n * z (.inl ()) = 0 at f0
  change m * u (.inr i) + n * z (.inr i) = 0 at f1
  have hm : m * (u (.inl ()) * z (.inr i) - u (.inr i) * z (.inl ())) = 0 := by
    linear_combination z (.inr i) * f0 - z (.inl ()) * f1
  have hn : n * (u (.inl ()) * z (.inr i) - u (.inr i) * z (.inl ())) = 0 := by
    linear_combination u (.inl ()) * f1 - u (.inr i) * f0
  exact ⟨(mul_eq_zero.mp hm).resolve_right hdet, (mul_eq_zero.mp hn).resolve_right hdet⟩

/--
A nonzero short roof projection and a height floor yield independent kernel vectors `u` and
`z` with `V = c • u - d • z` for positive coprime `c, d` , with bounds on the height product
and both coefficient-weighted heights.
-/
theorem orientedPlaneOfShortProjection
    {I G : Type*} [Fintype I] [AddGroup G]
    (r : ((Unit ⊕ I) → ℤ) →+ G) {k : ℤ} (hk : k ≠ 0) (v : I → ℤ)
    (hV : Sum.elim (fun _ : Unit => k) v ∈ r.ker)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => k) v)
    (w : (Unit ⊕ I) → ℝ) (hw : ∀ j, 0 < w j) (Q : ℕ) {ell : ℝ}
    (hell : 0 < ell)
    (hfloor : ∀ a ∈ r.ker, a ≠ 0 → ell < _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (a j : ℝ)))
    (hgrid : 4 * ((∑ i, w (.inr i)) / (Q : ℝ)) ≤ ell)
    (hshort : ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection k v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection k v a i| < 1 / (Q : ℝ)) :
    let V := Sum.elim (fun _ : Unit => k) v
    let ht (a : (Unit ⊕ I) → ℤ) := _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (a j : ℝ))
    ∃ u ∈ r.ker, ∃ z ∈ r.ker, ∃ c d : ℕ,
      V = (c : ℤ) • u - (d : ℤ) • z ∧ c.Coprime d ∧ 0 < c ∧ 0 < d ∧
      (∀ m n : ℤ, m • u + n • z = 0 → m = 0 ∧ n = 0) ∧
      ell < ht u ∧ ell < ht z ∧
      ht u * ht z ≤ 4 * ht V * ((∑ i, w (.inr i)) / (Q : ℝ)) ∧
      (c : ℝ) * ht u ≤ 3 * ht V ∧ (d : ℝ) * ht z ≤ 2 * ht V := by
  let V := Sum.elim (fun _ : Unit => k) v
  let ht (a : (Unit ⊕ I) → ℤ) := _root_.AbcTwoNinths.ExteriorE1.height w (fun j => (a j : ℝ))
  obtain ⟨u, hu, z, hz, c, d, he, hcd, hind, _, _, hprod, hc, hd⟩ :=
    independentPlaneOfShortProjection r hk v hV hgen w hw Q hshort
  change V = c • u + d • z at he
  have hscale (m : ℤ) (a : (Unit ⊕ I) → ℤ) : ht (m • a) = |(m : ℝ)| * ht a := by
    let f := _root_.AbcTwoNinths.ExteriorE1.heightSeminorm w (fun j => (hw j).le)
    change f (fun j => ((m • a) j : ℝ)) = |(m : ℝ)| * f (fun j => (a j : ℝ))
    have hcast : (fun j => ((m • a) j : ℝ)) = (m : ℝ) • (fun j => (a j : ℝ)) := by
      funext j
      change ((m * a j : ℤ) : ℝ) = (m : ℝ) * (a j : ℝ)
      exact Int.cast_mul m (a j)
    rw [hcast, map_smul_eq_mul, Real.norm_eq_abs]
  have hneg (a : (Unit ⊕ I) → ℤ) : ht (-a) = ht a := by
    simpa using hscale (-1) a
  have hu_ne : u ≠ 0 := fun h => (by decide : (1 : ℤ) ≠ 0) (hind 1 0 (by simp [h])).1
  have hz_ne : z ≠ 0 := fun h => (by decide : (1 : ℤ) ≠ 0) (hind 0 1 (by simp [h])).2
  have hco : c ≠ 0 ∧ d ≠ 0 := by
    refine _root_.AbcTwoNinths.ExteriorE2.coordinatesNonzero (V := ht V) hcd (hfloor u hu hu_ne) (hfloor z hz hz_ne)
      hell hgrid ?_ ?_ ?_
    · calc
        ht u * ht z ≤ 4 * ht V * ((∑ i, w (.inr i)) / (Q : ℝ)) := hprod
        _ = ht V * (4 * ((∑ i, w (.inr i)) / (Q : ℝ))) := by ring
    · intro h
      rw [he, h, zero_zsmul, zero_add, hscale]
    · intro h
      rw [he, h, zero_zsmul, add_zero, hscale]
  obtain ⟨u', hu', z', hz', hsu, hsz, hcpos, hdpos, hcop, he'⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.orientCoordinates hu hz hco.1 hco.2 hcd he
  have hhu : ht u' = ht u := by rcases hsu with h | h <;> simp [h, hneg]
  have hhz : ht z' = ht z := by rcases hsz with h | h <;> simp [h, hneg]
  have habs (m : ℤ) : (m.natAbs : ℝ) = |(m : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  refine ⟨u', hu', z', hz', c.natAbs, d.natAbs, he', hcop, hcpos, hdpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    rcases hsu with rfl | rfl <;> rcases hsz with rfl | rfl
    · exact hind m n hmn
    · simpa only [neg_eq_zero] using hind m (-n) (by simpa only [neg_zsmul, zsmul_neg] using hmn)
    · simpa only [neg_eq_zero] using hind (-m) n (by simpa only [neg_zsmul, zsmul_neg] using hmn)
    · simpa only [neg_eq_zero] using hind (-m) (-n) (by simpa only [neg_zsmul, zsmul_neg] using hmn)
  · change ell < ht u'
    rw [hhu]
    exact hfloor u hu hu_ne
  · change ell < ht z'
    rw [hhz]
    exact hfloor z hz hz_ne
  · change ht u' * ht z' ≤ 4 * ht V * ((∑ i, w (.inr i)) / (Q : ℝ))
    rw [hhu, hhz]
    exact hprod
  · change (c.natAbs : ℝ) * ht u' ≤ 3 * ht V
    rw [habs, hhu]
    exact hc
  · change (d.natAbs : ℝ) * ht z' ≤ 2 * ht V
    rw [habs, hhz]
    exact hd

end

end AbcTwoNinths.ExteriorE2
