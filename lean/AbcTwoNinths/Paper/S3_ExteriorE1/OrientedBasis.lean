/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.MonomialSeparation

/-!
# Oriented Basis

The module orients an integer plane basis to obtain the required signs of its coefficients. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.orientedBasis`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
Orients independent prime monomials above one while preserving their heights and the signed representation of log (c / b). This is used in the proof of Proposition 3.1 of the paper.
-/
theorem orientedBasis (t : _root_.AbcTwoNinths.Basic.Triple) (w v : _root_.AbcTwoNinths.Basic.supp t → ℤ) (c d : ℤ)
    (hi : ∀ m n : ℤ, m • w + n • v = 0 → m = 0 ∧ n = 0)
    (hv : _root_.AbcTwoNinths.ExteriorE1.quotientVec t = c • w + d • v) :
    ∃ (q₁ q₂ : ℚ) (c₁ c₂ : ℤ),
      1 < q₁ ∧ 1 < q₂ ∧ _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent q₁ q₂ ∧
      let L₁ := _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₁
      let L₂ := _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₂
      L₁ = _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)) w ∧
      L₂ = _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)) v ∧
      1 / 2 ≤ L₁ ∧ 1 / 2 ≤ L₂ ∧
      Real.exp (-L₁) ≤ Real.log (q₁ : ℝ) ∧ Real.log (q₁ : ℝ) ≤ L₁ ∧
      Real.exp (-L₂) ≤ Real.log (q₂ : ℝ) ∧ Real.log (q₂ : ℝ) ≤ L₂ ∧
      Real.log (q₁ : ℝ) = |∑ i : _root_.AbcTwoNinths.Basic.supp t, Real.log (i.val : ℝ) * (w i : ℝ)| ∧
      Real.log (q₂ : ℝ) = |∑ i : _root_.AbcTwoNinths.Basic.supp t, Real.log (i.val : ℝ) * (v i : ℝ)| ∧
      |c₁| = |c| ∧ |c₂| = |d| ∧
      (c₁ : ℝ) * Real.log (q₁ : ℝ) + (c₂ : ℝ) * Real.log (q₂ : ℝ) =
        Real.log ((t.c : ℝ) / t.b) := by
  let p : _root_.AbcTwoNinths.Basic.supp t → ℕ := Subtype.val
  have hp (i : _root_.AbcTwoNinths.Basic.supp t) : (p i).Prime := _root_.AbcTwoNinths.Basic.suppPrime t i.property
  have hinj : Function.Injective p := Subtype.val_injective
  have hw : w ≠ 0 := fun h => one_ne_zero (hi 1 0 (by simp [h])).1
  have hvn : v ≠ 0 := fun h => one_ne_zero (hi 0 1 (by simp [h])).2
  obtain ⟨s, hs, hqs⟩ := _root_.AbcTwoNinths.ExteriorE1.orientMonomial p hp hinj w hw
  obtain ⟨a, ha, hqa⟩ := _root_.AbcTwoNinths.ExteriorE1.orientMonomial p hp hinj v hvn
  have hs' : s * s = 1 := by rcases hs with h | h <;> simp [h]
  have ha' : a * a = 1 := by rcases ha with h | h <;> simp [h]
  have hor : ∀ m n : ℤ, m • (s • w) + n • (a • v) = 0 → m = 0 ∧ n = 0 := by
    intro m n h
    rw [smul_smul, smul_smul] at h
    obtain ⟨hm, hn⟩ := hi _ _ h
    exact ⟨(mul_eq_zero.mp hm).resolve_right (by intro hz; simp [hz] at hs'),
      (mul_eq_zero.mp hn).resolve_right (by intro hz; simp [hz] at ha')⟩
  have hheight (b : _root_.AbcTwoNinths.Basic.supp t → ℤ) (k : ℤ) (hk : k = 1 ∨ k = -1) :
      _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i => Real.log (p i : ℝ)) (k • b) =
        _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i => Real.log (p i : ℝ)) b := by
    rcases hk with h | h <;> simp [h, _root_.AbcTwoNinths.ExteriorE1.signedHeight, max_comm]
  obtain ⟨hL₁, hlo₁, hhi₁⟩ := _root_.AbcTwoNinths.ExteriorE1.monomialSeparation p hp hinj (s • w) hqs
  obtain ⟨hL₂, hlo₂, hhi₂⟩ := _root_.AbcTwoNinths.ExteriorE1.monomialSeparation p hp hinj (a • v) hqa
  have hlog (b : _root_.AbcTwoNinths.Basic.supp t → ℤ) (k : ℤ) (hk : k = 1 ∨ k = -1)
      (hpos : 1 < _root_.AbcTwoNinths.PolyCap.prodMonomial p (k • b)) :
      Real.log (_root_.AbcTwoNinths.PolyCap.prodMonomial p (k • b) : ℝ) =
        |∑ i : _root_.AbcTwoNinths.Basic.supp t, Real.log (p i : ℝ) * (b i : ℝ)| := by
    have hl : 0 < Real.log (_root_.AbcTwoNinths.PolyCap.prodMonomial p (k • b) : ℝ) :=
      Real.log_pos (by exact_mod_cast hpos)
    rw [← abs_of_pos hl, _root_.AbcTwoNinths.ExteriorE1.monomialLog p hp]
    rcases hk with h | h
    · simp [h]
    · simp [h, mul_neg, Finset.sum_neg_distrib]
  refine ⟨_, _, c*s, d*a, hqs, hqa, _root_.AbcTwoNinths.ExteriorE1.monomialIndependent p hp hinj _ _ hor,
    (_root_.AbcTwoNinths.ExteriorE1.monomialHeight p hp hinj _).trans (hheight w s hs),
    (_root_.AbcTwoNinths.ExteriorE1.monomialHeight p hp hinj _).trans (hheight v a ha),
    hL₁, hL₂, hlo₁, hhi₁, hlo₂, hhi₂, hlog w s hs hqs, hlog v a ha hqa, ?_, ?_, ?_⟩
  · rcases hs with h | h <;> simp [h]
  · rcases ha with h | h <;> simp [h]
  · have hb : (0 : ℝ) < t.b := by exact_mod_cast t.bpos
    have hcN : 0 < t.c := by have := t.add; have := t.apos; omega
    have hc : (0 : ℝ) < t.c := by exact_mod_cast hcN
    rw [_root_.AbcTwoNinths.ExteriorE1.monomialLog p hp, _root_.AbcTwoNinths.ExteriorE1.monomialLog p hp, Real.log_div hc.ne' hb.ne',
      ← _root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.c Finset.subset_union_right,
      ← _root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.b Finset.subset_union_left,
      ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hvi := congrFun hv i
    change (t.c.factorization i.val : ℤ) - t.b.factorization i.val = c * w i + d * v i at hvi
    have hR := congrArg (fun z : ℤ => (z : ℝ)) hvi
    simp only [Pi.smul_apply, zsmul_eq_mul] at ⊢
    push_cast at hR ⊢
    change (c : ℝ) * s * (Real.log (p i : ℝ) * ((s : ℝ) * w i)) +
      (d : ℝ) * a * (Real.log (p i : ℝ) * ((a : ℝ) * v i)) =
      Real.log (p i : ℝ) * (t.c.factorization i.val : ℝ) -
      Real.log (p i : ℝ) * (t.b.factorization i.val : ℝ)
    have hsR : (s : ℝ) * s = 1 := by exact_mod_cast hs'
    have haR : (a : ℝ) * a = 1 := by exact_mod_cast ha'
    linear_combination -Real.log (p i : ℝ) * hR +
      ((c : ℝ) * Real.log (p i : ℝ) * w i) * hsR +
      ((d : ℝ) * Real.log (p i : ℝ) * v i) * haR

end

end AbcTwoNinths.ExteriorE1
