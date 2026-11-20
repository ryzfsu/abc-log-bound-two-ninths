/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ExponentResidueCollision
public import AbcTwoNinths.Paper.S2_PolyCap.DeepCollisionExclusion

/-!
# Rank Two Collision Bound

The module uses residue collision exclusion to bound the count entering the polynomial cap. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.collisionCountBound`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real


/--
Bounds the absolute pivot exponent of a primitive residue-kernel vector by the number of residue and logarithmic bins. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem collisionCountBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p r : ℕ} {H : ℝ} (hp : p.Prime) (ho : 2 < p) (hr : 1 ≤ r) (hH : 2 < H)
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (haway : ∀ j, ¬ p ∣ q j) (e : ι → ℤ) (i : ι)
    [Nonempty {j : ι // j ≠ i}]
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker e)
    (hne : _root_.AbcTwoNinths.PolyCap.prodMonomial q e ≠ 1)
    (hh : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) ≤ 4 * H)
    (hdepth : H / (4 * (r : ℝ)) ≤
      (padicValRat p (_root_.AbcTwoNinths.PolyCap.prodMonomial q e - 1) : ℝ) * log (p : ℝ)) :
    let I := {j : ι // j ≠ i}
    let T := 1 / (1920000 * (r : ℝ) * (1 + log (20 * H)) ^ 2)
    (e i).natAbs ≤ (p - 1) * ∏ j : I, ⌈(Fintype.card I : ℝ) * log (q j.val) / T⌉₊ := by
  let I := {j : ι // j ≠ i}
  let φ := Equiv.optionSubtypeNe i
  let q' (j : Option I) := q (φ j)
  let T : ℝ := 1 / (1920000 * (r : ℝ) * (1 + log (20 * H)) ^ 2)
  let K := (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker
  let K' := (_root_.AbcTwoNinths.Basic.residue q' (_root_.AbcTwoNinths.Basic.awayCoprime hp q' (fun j => haway (φ j)))).ker
  have reindex (x : ι → ℤ) : (fun j => x (φ j)) ∈ K' ↔ x ∈ K := by
    change (∏ j : Option I, ZMod.unitOfCoprime (q (φ j)) _ ^ x (φ j)) = 1 ↔
      (∏ j : ι, ZMod.unitOfCoprime (q j) _ ^ x j) = 1
    rw [Fintype.prod_equiv φ
      (fun j : Option I => ZMod.unitOfCoprime (q (φ j)) (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway (φ j)) ^ x (φ j))
      (fun j : ι => ZMod.unitOfCoprime (q j) (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway j) ^ x j)
      (fun _ => rfl)]
  let s : ℤ := if 0 ≤ e i then 1 else -1
  have hs : s * s = 1 := by dsimp [s]; split_ifs <;> norm_num
  have hsabs : |(s : ℝ)| = 1 := by dsimp [s]; split_ifs <;> norm_num
  let e' : Option I → ℤ := fun j => (s • e) (φ j)
  have hep : e' ∈ K' := (reindex _).2 (K.zsmul_mem he s)
  have hpivot : e' none = ((e i).natAbs : ℤ) := by
    change s * e i = ((e i).natAbs : ℤ)
    dsimp [s]
    split_ifs <;> omega
  have hpp : _root_.AbcTwoNinths.Basic.PrimitiveIn K' e' := by
    intro n u hu hnu
    let w : ι → ℤ := fun j => u (φ.symm j)
    have hw : w ∈ K := (reindex w).1 (by simpa [w] using hu)
    apply hprim n (s • w) (K.zsmul_mem hw s)
    funext j
    have h := congrFun hnu (φ.symm j)
    change (n : ℤ) * u (φ.symm j) = s * e (φ (φ.symm j)) at h
    rw [φ.apply_symm_apply] at h
    change (n : ℤ) * (s * u (φ.symm j)) = e j
    calc
      _ = s * ((n : ℤ) * u (φ.symm j)) := by ring
      _ = e j := by rw [h, ← mul_assoc, hs, one_mul]
  have hT : 0 < T := by
    have hr' : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hlog : 0 ≤ log (20 * H) := log_nonneg (by linarith)
    dsimp [T]
    positivity
  change (e i).natAbs ≤ (p - 1) *
    ∏ j : I, ⌈(Fintype.card I : ℝ) * log (q' (some j)) / T⌉₊
  by_contra! hcount
  obtain ⟨v, lam, hv, _, _, hind, hclose⟩ :=
    _root_.AbcTwoNinths.Basic.gammaLogCollision hp q' (fun j => hq (φ j)) (fun j => haway (φ j))
      e' (e i).natAbs hpivot T hT hcount hep hpp
  let w : ι → ℤ := fun j => v (φ.symm j)
  have hw : w ∈ K := (reindex w).1 (by
    change v ∈ K' at hv
    simpa only [w, φ.symm_apply_apply] using hv)
  have hwind : ¬ ∃ c : ℚ, ∀ j, (((s • w) j : ℤ) : ℚ) = c * (e j : ℚ) := by
    rintro ⟨c, hc⟩
    apply hind
    use c
    intro j
    have hj := hc (φ j)
    change ((s * v (φ.symm (φ j)) : ℤ) : ℚ) = c * (e (φ j) : ℚ) at hj
    rw [φ.symm_apply_apply, Int.cast_mul] at hj
    have hs' : (s : ℚ) * s = 1 := by exact_mod_cast hs
    change (v j : ℚ) = c * ((s * e (φ j) : ℤ) : ℚ)
    rw [Int.cast_mul]
    calc
      _ = (s : ℚ) * ((s : ℚ) * (v j : ℚ)) := by rw [← mul_assoc, hs', one_mul]
      _ = _ := by rw [hj]; ring
  apply _root_.AbcTwoNinths.PolyCap.noCollisionAtW5BThreshold hp ho hr hH q hq hinj haway
    e (s • w) lam he (K.zsmul_mem hw s) hwind hne hh hdepth
  change _ < T
  rw [← Fintype.sum_equiv φ
    (fun j => |((s • w) (φ j) : ℝ) - lam * (e (φ j) : ℝ)| * log (q (φ j) : ℝ))
    (fun j => |((s • w) j : ℝ) - lam * (e j : ℝ)| * log (q j : ℝ)) (fun _ => rfl)]
  refine lt_of_le_of_lt ?_ hclose
  apply Finset.sum_le_sum
  intro j _
  change |((s * v (φ.symm (φ j)) : ℤ) : ℝ) - lam * (e (φ j) : ℝ)| * log (q (φ j) : ℝ) ≤
    |(v j : ℝ) - lam * ((s * e (φ j) : ℤ) : ℝ)| * log (q (φ j) : ℝ)
  rw [φ.symm_apply_apply, Int.cast_mul, Int.cast_mul]
  have hs' : (s : ℝ) * s = 1 := by exact_mod_cast hs
  have heq : (s : ℝ) * (v j : ℝ) - lam * (e (φ j) : ℝ) =
      (s : ℝ) * ((v j : ℝ) - lam * ((s : ℝ) * (e (φ j) : ℝ))) := by
    linear_combination lam * (e (φ j) : ℝ) * hs'
  rw [heq, abs_mul, hsabs, one_mul]

end

end AbcTwoNinths.PolyCap
