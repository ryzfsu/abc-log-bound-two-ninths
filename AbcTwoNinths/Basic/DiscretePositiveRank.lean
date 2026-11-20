/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RoofCovolume
public import Mathlib.Tactic

/-!
# Discrete Positive Rank

When the grid outnumbers the residue and coordinate classes, two grid points give a kernel
vector with nonzero projection and projected coordinates bounded by `M / Q`.

## Main results
* `AbcTwoNinths.Basic.discretePositiveRank`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section


/--
A strict excess of grid points over residue and coordinate classes yields a kernel vector with nonzero projection and every projected coordinate smaller than M/Q in absolute value.
-/
theorem discretePositiveRank
    {ι G : Type*} [Fintype ι] [AddGroup G] [Finite G]
    (r : ((Unit ⊕ ι) → ℤ) →+ G) {k M Q : ℕ}
    (hk : 0 < k) (hM : 0 < M) (hQ : 0 < Q) (v : ι → ℤ)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => (k : ℤ)) v)
    (hc : Nat.card r.range * Q ^ Fintype.card ι < k * M ^ Fintype.card ι) :
    ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a i| < (M : ℝ) / Q := by
  classical
  let _ : Fintype r.range := Fintype.ofFinite r.range
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  let z (h : Fin k) (i : ι) := (h.val : ℤ) * v i
  let vec (p : Fin k × (ι → Fin M)) : (Unit ⊕ ι) → ℤ :=
    Sum.elim (fun _ => (p.1.val : ℤ)) (fun i => z p.1 i / k - (p.2 i).val)
  let N (p : Fin k × (ι → Fin M)) (i : ι) :=
    (p.2 i).val * k + (z p.1 i % (k : ℤ)).toNat
  have hN (p : Fin k × (ι → Fin M)) (i : ι) : N p i < M * k := by
    have hr := Int.emod_lt_of_pos (z p.1 i) hkZ
    have ht := Nat.mul_le_mul_right k (show (p.2 i).val + 1 ≤ M from (p.2 i).isLt)
    have hr' : (z p.1 i % (k : ℤ)).toNat < k := by omega
    rw [Nat.add_mul, Nat.one_mul] at ht
    dsimp [N]
    omega
  have hv (p : Fin k × (ι → Fin M)) (i : ι) :
      _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v (vec p) i = -(N p i : ℝ) / k := by
    have h := Int.mul_ediv_add_emod (z p.1 i) (k : ℤ)
    have hr := Int.toNat_of_nonneg (Int.emod_nonneg (z p.1 i) hkZ.ne')
    have hc' : (k : ℝ) * ((z p.1 i / (k : ℤ) : ℤ) : ℝ) +
        ((z p.1 i % (k : ℤ) : ℤ) : ℝ) = (p.1.val : ℝ) * (v i : ℝ) := by
      exact_mod_cast h
    change ((z p.1 i / (k : ℤ) - (p.2 i).val : ℤ) : ℝ) -
      (p.1.val : ℝ) / k * (v i : ℝ) = -(N p i : ℝ) / k
    unfold N
    push_cast
    rw [show (((z p.1 i % (k : ℤ)).toNat : ℕ) : ℝ) =
      ((z p.1 i % (k : ℤ) : ℤ) : ℝ) by exact_mod_cast hr]
    field_simp
    linarith
  let D := M * k
  have hD : 0 < D := Nat.mul_pos hM hk
  let f (p : Fin k × (ι → Fin M)) : r.range × (ι → Fin Q) :=
    (⟨r (vec p), ⟨vec p, rfl⟩⟩, fun i => ⟨Q * N p i / D,
      Nat.div_lt_of_lt_mul (by simpa [D, mul_comm] using Nat.mul_lt_mul_of_pos_left (hN p i) hQ)⟩)
  have hcard : Fintype.card (r.range × (ι → Fin Q)) <
      Fintype.card (Fin k × (ι → Fin M)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      ← Nat.card_eq_fintype_card (α := r.range)]
    simpa [Fintype.card_pi] using hc
  obtain ⟨p, q, hpq, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  let a := vec p - vec q
  have ha : a ∈ r.ker := by
    have hr : r (vec p) = r (vec q) := congrArg (fun u => (u.1 : G)) hf
    change r (vec p - vec q) = 0
    rw [map_sub, hr, sub_self]
  refine ⟨a, ha, ?_, ?_⟩
  · intro hzero
    obtain ⟨m, hm⟩ := hgen a ha hzero
    have hh : (p.1.val : ℤ) - (q.1.val : ℤ) = m * k := by
      simpa [a, vec, zsmul_eq_mul] using congrFun hm (.inl ())
    have hp := p.1.isLt
    have hq := q.1.isLt
    have hlo : -(k : ℤ) < m * k := by omega
    have hhi : m * k < (k : ℤ) := by omega
    have hm0 : m = 0 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hn | hn
      · have hh := mul_le_mul_of_nonneg_right (show m ≤ -1 by omega) hkZ.le
        simp at hh
        omega
      · have hh := mul_le_mul_of_nonneg_right (show 1 ≤ m by omega) hkZ.le
        simp at hh
        omega
    have hz : a = 0 := by rw [hm, hm0, zero_smul]
    have hfst : p.1 = q.1 := by
      apply Fin.ext
      have hh' := congrFun hz (.inl ())
      change (p.1.val : ℤ) - (q.1.val : ℤ) = 0 at hh'
      omega
    apply hpq (Prod.ext hfst ?_)
    funext i
    apply Fin.ext
    have hi := congrFun hz (.inr i)
    change (z p.1 i / k - ((p.2 i).val : ℤ)) -
      (z q.1 i / k - ((q.2 i).val : ℤ)) = 0 at hi
    rw [hfst] at hi
    omega
  · intro i
    have hb : Q * N p i / D = Q * N q i / D := congrArg (fun u => (u.2 i).val) hf
    have hpl := Nat.div_mul_le_self (Q * N p i) D
    have hph := Nat.lt_div_mul_add (a := Q * N p i) hD
    have hql := Nat.div_mul_le_self (Q * N q i) D
    have hqh := Nat.lt_div_mul_add (a := Q * N q i) hD
    rw [hb] at hpl hph
    have hz : |(Q * N q i : ℤ) - (Q * N p i : ℤ)| < (D : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have hr : |(Q * N q i : ℝ) - (Q * N p i : ℝ)| < (M : ℝ) * k := by
      have hz' : |(Q * N q i : ℤ) - (Q * N p i : ℤ)| < (M : ℤ) * k := by
        simpa [D, Nat.cast_mul] using hz
      exact_mod_cast hz'
    rw [show (Q * N q i : ℝ) - (Q * N p i : ℝ) =
      Q * ((N q i : ℝ) - N p i) by ring, abs_mul, abs_of_pos hQR] at hr
    change |_root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v (vec p - vec q) i| < _
    rw [map_sub, Pi.sub_apply, hv, hv,
      show -(N p i : ℝ) / k - (-(N q i : ℝ) / k) =
        ((N q i : ℝ) - N p i) / k by ring, abs_div, abs_of_pos hkR,
        div_lt_div_iff₀ hkR hQR]
    nlinarith only [hr]

end

end AbcTwoNinths.Basic
