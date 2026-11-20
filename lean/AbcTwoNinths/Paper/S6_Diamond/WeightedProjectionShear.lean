/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.ProjectedKernelBasis
public import AbcTwoNinths.Paper.S6_Diamond.ProjectedPrincipalUnits
public import AbcTwoNinths.Paper.S6_Diamond.WeightedShearBounds

/-!
# Weighted Projection Shear

Bounds the weighted projection of a signed-kernel vector independent of the distinguished source
vector. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.nativeWeightedShear`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section




/-- The depth and mass hypotheses give a lower bound of `4 * x / Real.log x` for the
log-prime-weighted distance from an independent kernel vector to the selected line. -/
theorem nativeWeightedShear {I : Type*} [Fintype I] {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)] (q : I → ℕ) (hq : ∀ i, (q i).Prime)
    (avoid : ∀ i, p ≠ q i) (hqi : Function.Injective q)
    (s w : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)) {j : I}
    (hj : s.val.toAdd j ≠ 0)
    (hind : ¬ ∃ a : ℚ, ∀ i, (w.val.toAdd i : ℚ) = a * (s.val.toAdd i : ℚ))
    {x H m α : ℝ} (hx : 0 < x) (hH : 0 < H)
    (hroof : x / 2 ≤ Real.log (p : ℝ))
    (hm : H / 2 ≤ m * Real.log (p : ℝ))
    (honset : 1000000000 ≤ Real.log x)
    (hV : _root_.AbcTwoNinths.Basic.mass (fun i => Real.log (q i : ℝ)) s.val.toAdd ≤ 3 * H)
    (hB1 :
      let γ := _root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)
      ∀ (u v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)) (c d : ℤ) (B₁ B₂ : ℝ),
        Function.Injective (fun z : ℤ × ℤ => fun i =>
          z.1 * u.val.toAdd i + z.2 * v.val.toAdd i) →
        c ≠ 0 → d ≠ 0 → s = u ^ c * v ^ d →
        max (_root_.AbcTwoNinths.Basic.rationalHeight (γ u : ℚ)) (Real.log (p : ℝ)) ≤ B₁ →
        max (_root_.AbcTwoNinths.Basic.rationalHeight (γ v : ℚ)) (Real.log (p : ℝ)) ≤ B₂ →
        ((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) * Real.log (p : ℝ) ≤ 32 * H / x →
        m * (Real.log (p : ℝ)) ^ 2 ≤ 9408 * B₁ * B₂) :
    4 * x / Real.log x ≤
      ∑ i, |(w.val.toAdd i : ℝ) - α * (s.val.toAdd i : ℝ)| * Real.log (q i : ℝ) := by
  let W := fun i => Real.log (q i : ℝ)
  let V := _root_.AbcTwoNinths.Basic.mass W s.val.toAdd
  let ell := Real.log (p : ℝ)
  let γ := _root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)
  have hW (i : I) : 0 < W i := Real.log_pos (by exact_mod_cast (hq i).one_lt)
  have hVpos : 0 < V := by
    unfold V _root_.AbcTwoNinths.Basic.mass
    have hterm : 0 < |(s.val.toAdd j : ℝ)| * W j :=
      mul_pos (abs_pos.mpr (by exact_mod_cast hj)) (hW j)
    exact hterm.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (abs_nonneg (s.val.toAdd i : ℝ)) (hW i).le)
      (Finset.mem_univ j))
  by_contra! hshort
  obtain ⟨T, hT, hTshort⟩ := exists_between hshort
  have hTpos : 0 ≤ T :=
    (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hW i).le).trans hT.le
  obtain ⟨a, b, hdet, hrep, hi, hu, hv, hprod, hc, hd⟩ :=
    _root_.AbcTwoNinths.Diamond.collisionKernelColumns q hq hqi s w hj hind hT
  let U := _root_.AbcTwoNinths.Diamond.kernelColumn s w a
  let Z := _root_.AbcTwoNinths.Diamond.kernelColumn s w b
  let A := _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd a)
  let B := _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd b)
  have hn (z : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq avoid)) (hz : z ≠ 1) :
      ell ≤ 2 * _root_.AbcTwoNinths.Basic.rationalHeight (γ z : ℚ) := by
    have hγ : (γ z : ℚ) ≠ 1 := by
      intro he
      apply hz
      apply _root_.AbcTwoNinths.ExteriorE2.modularResidueLatticeInjective q hq hqi avoid
      change γ z = γ 1
      rw [map_one]
      exact Units.ext he
    have hf := _root_.AbcTwoNinths.Diamond.principalHeightFloor (_root_.AbcTwoNinths.Diamond.signedLiftPrincipal q hq avoid z) hγ
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [Real.log_div hp.ne' (by norm_num)] at hf
    have hx4 : 4 ≤ x := by linarith [Real.log_le_sub_one_of_pos hx]
    have he : 2 ≤ ell := by linarith
    change ell - Real.log 2 ≤ _root_.AbcTwoNinths.Basic.rationalHeight (γ z : ℚ) at hf
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hinj := _root_.AbcTwoNinths.Basic.evalInjective hj hind
  have nontrivial (z : _root_.AbcTwoNinths.Basic.ZPair) (hz : z ≠ (0, 0)) : _root_.AbcTwoNinths.Diamond.kernelColumn s w z ≠ 1 := by
    intro he
    apply hz
    apply hinj
    rw [← _root_.AbcTwoNinths.Diamond.kernelColumnRow, he]
    funext i
    simp [_root_.AbcTwoNinths.Basic.eval]
  have ha : a ≠ (0, 0) := by
    intro he
    simp [he, _root_.AbcTwoNinths.Basic.det] at hdet
  have hb : b ≠ (0, 0) := by
    intro he
    simp [he, _root_.AbcTwoNinths.Basic.det] at hdet
  have hA : ell ≤ 2 * A := by linarith [hn U (nontrivial a ha), hu]
  have hB : ell ≤ 2 * B := by linarith [hn Z (nontrivial b hb), hv]
  have hsame (z : _root_.AbcTwoNinths.Basic.ZPair) (hz : z.2 = 0) (hunit : z.1 = 1 ∨ z.1 = -1) :
      V = _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd z) := by
    unfold V _root_.AbcTwoNinths.Basic.mass
    apply Finset.sum_congr rfl
    intro i _
    rcases hunit with h | h <;> simp [_root_.AbcTwoNinths.Basic.eval, hz, h]
  by_cases hb₂ : b.2 = 0
  · have hunit : b.1 = 1 ∨ b.1 = -1 := by
      have hd' : (-a.2) * b.1 = 1 := by simpa [_root_.AbcTwoNinths.Basic.det, hb₂] using hdet
      exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right (-a.2) hd')
    exact _root_.AbcTwoNinths.Diamond.scaledMassExcludeZeroFour hx hVpos hroof hA hB honset hTshort hprod.le
      (Or.inr (hsame b hb₂ hunit))
  by_cases ha₂ : a.2 = 0
  · have hunit : a.1 = 1 ∨ a.1 = -1 := by
      have hd' : a.1 * b.2 = 1 := by simpa [_root_.AbcTwoNinths.Basic.det, ha₂] using hdet
      exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one b.2 hd')
    exact _root_.AbcTwoNinths.Diamond.scaledMassExcludeZeroFour hx hVpos hroof hA hB honset hTshort hprod.le
      (Or.inl (hsame a ha₂ hunit))
  have he : 0 < ell := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hboundU : max (_root_.AbcTwoNinths.Basic.rationalHeight (γ U : ℚ)) ell ≤ 8 * A :=
    max_le (by linarith [hu]) (by linarith)
  have hboundZ : max (_root_.AbcTwoNinths.Basic.rationalHeight (γ Z : ℚ)) ell ≤ 8 * B :=
    max_le (by linarith [hv]) (by linarith)
  have hscale := _root_.AbcTwoNinths.Diamond.scaledMassCoefficient hx hroof hV hA hB
    (abs_nonneg (b.2 : ℝ)) (abs_nonneg (a.2 : ℝ)) (by linarith [hc, hd])
  have hscale' :
      ((b.2.natAbs : ℝ) / (8 * B) + ((-a.2).natAbs : ℝ) / (8 * A)) * ell ≤
        32 * H / x := by
    simp only [Int.natAbs_neg, Nat.cast_natAbs, Int.cast_abs]
    exact hscale.trans (div_le_div_of_nonneg_right (by linarith) hx.le)
  have hm' := hB1 U Z b.2 (-a.2) (8 * A) (8 * B)
    hi hb₂ (neg_ne_zero.mpr ha₂) hrep hboundU hboundZ hscale'
  exact _root_.AbcTwoNinths.Diamond.scaledMassExcludeNonzeroFour hx hH hroof hV hTpos honset hTshort hprod.le hm hm'

end

end AbcTwoNinths.Diamond
