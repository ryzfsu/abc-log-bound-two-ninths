/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneLogarithmicForm
public import AbcTwoNinths.Paper.S3_ExteriorE1.ActualIntegerSlab
public import AbcTwoNinths.Paper.S3_ExteriorE1.PrimitiveLineExponents
public import AbcTwoNinths.Paper.S3_ExteriorE1.RadiusWindows

/-!
# Actual Plane Contact

The module constructs the reduced logarithmic slab for a source quotient after removing the pivot coordinate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.actualReducedLogSlab`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
An integral vector on the real line through a primitive integer vector is an integer multiple of that vector.
-/
theorem primitiveRealMultiple {ι : Type*} (w : ι → ℤ) (r : ι) (hr : w r ≠ 0)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w) (z : ι → ℤ) (s : ℝ)
    (hz : ∀ i, (z i : ℝ) = s * (w i : ℝ)) : ∃ k : ℤ, z = k • w := by
  let q : ℚ := (z r : ℚ) / (w r : ℚ)
  have hrR : (w r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hs : (q : ℝ) = s := by
    simp only [q, Rat.cast_div, Rat.cast_intCast]
    exact (div_eq_iff hrR).2 (hz r)
  have hq (i : ι) : (z i : ℚ) = q * (w i : ℚ) := by
    have hi := hz i
    rw [← hs] at hi
    exact_mod_cast hi
  have he := _root_.AbcTwoNinths.Basic.integralOfPrimitiveProportional
    (show w ∈ (⊤ : AddSubgroup (ι → ℤ)) from trivial)
    (show z ∈ (⊤ : AddSubgroup (ι → ℤ)) from trivial) hprim q hq
  refine ⟨q.num, funext fun i => ?_⟩
  have hi := hq i
  rw [he] at hi
  change z i = q.num * w i
  exact_mod_cast hi

/-- Omitting a pivot with zero summand preserves the finite sum. -/
theorem sumExcludePivot {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (F : ι → ℝ) (hr : F r = 0) : (∑ i, F i) = ∑ i : {i : ι // i ≠ r}, F i.val := by
  classical
  have he (i : {i : ι // ¬ i ≠ r}) : F i.val = 0 := by
    rwa [not_ne_iff.mp i.property]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : ι => i ≠ r) F
  rw [Finset.sum_eq_zero (fun i _ => he i), add_zero] at h
  exact h.symm

/-- The prime-weighted logarithm of the quotient exponent vector equals the logarithm of c/b. -/
theorem quotientWeightedLog (t : _root_.AbcTwoNinths.Basic.Triple) :
    _root_.AbcTwoNinths.ExteriorE1.weightedLog (fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)) (fun i => (_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ)) =
      Real.log ((t.c : ℝ) / t.b) := by
  have hb : (0 : ℝ) < t.b := by exact_mod_cast t.bpos
  have hcN : 0 < t.c := by have := t.add; have := t.apos; omega
  have hc : (0 : ℝ) < t.c := by exact_mod_cast hcN
  rw [_root_.AbcTwoNinths.ExteriorE1.weightedLogApply, Real.log_div hc.ne' hb.ne',
    ← _root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.c Finset.subset_union_right,
    ← _root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.b Finset.subset_union_left,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [_root_.AbcTwoNinths.ExteriorE1.quotientVec, Int.cast_sub, Int.cast_natCast]
  ring

/--
A high triple with sufficiently small `log (c / b)` and failing the real contact bound
admits two independent integral exponent vectors spanning its quotient vector, with
bounds on their height product, coordinates, and real logarithms.
-/
theorem actualReducedLogSlab (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ)
    (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hh : Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) ≤ t.logHeight)
    (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) (hx : Real.exp 4 ≤ t.thirdLogRadical)
    (hon₁ : Real.exp (192 * Real.log (768 / _root_.AbcTwoNinths.Statement.highRate η) / _root_.AbcTwoNinths.Statement.highRate η) ≤ t.thirdLogRadical)
    (hon₂ : (16 / _root_.AbcTwoNinths.Statement.highRate η) *
      (max 0 (Real.log (9 / κ)) + 2 * Real.log (32 / _root_.AbcTwoNinths.Statement.highRate η)) ≤ t.thirdLogRadical)
    (hcontact : Real.log ((t.c : ℝ) / t.b) ≤ 1 / t.logHeight) :
    ∃ (x y : _root_.AbcTwoNinths.Basic.supp t → ℤ) (a b : ℤ) (d ε : ℝ),
      0 < d ∧ d ≤ t.thirdLogRadical / Real.log t.thirdLogRadical ∧ 0 < ε ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
      (∀ m n : ℤ, m • x + n • y = 0 → m = 0 ∧ n = 0) ∧
      _root_.AbcTwoNinths.ExteriorE1.quotientVec t = a • x + b • y ∧
      let A := fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)
      let L₁ := _root_.AbcTwoNinths.ExteriorE1.signedHeight A x
      let L₂ := _root_.AbcTwoNinths.ExteriorE1.signedHeight A y
      L₁ * L₂ ≤ 4 * t.logHeight * d ∧ |(a : ℝ)| * L₁ ≤ 3 * t.logHeight ∧ |(b : ℝ)| * L₂ ≤ 2 * t.logHeight ∧
      |∑ i, A i * (x i : ℝ)| ≤ 7 * L₁ * ε / d ∧
      |∑ i, A i * (y i : ℝ)| ≤ 7 * L₂ * ε / d := by
  classical
  obtain ⟨u, w, r, ε, sign, hs, hw, hprim, hr, hur, _, hind, helo, helog, hsum, hlog⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.actualIntegerSlab η hη κ hκ t hab hh hf hx hon₁ hon₂
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh
  have hxp : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le hx
  have hrate : (2 : ℝ) / 3 < _root_.AbcTwoNinths.Statement.highRate η := by
    have hη' : (η : ℝ) < 1 / 9 := by
      have hc : (η : ℝ) < (((1 : ℚ) / 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hη.2
      simpa using hc
    unfold _root_.AbcTwoNinths.Statement.highRate
    linarith
  have hlogx : 4 ≤ Real.log t.thirdLogRadical := by simpa using Real.log_le_log (Real.exp_pos 4) hx
  have hx5 : 5 ≤ t.thirdLogRadical := by linarith [Real.log_le_sub_one_of_pos hxp]
  have hTH : t.thirdLogRadical / Real.log t.thirdLogRadical ≤ t.logHeight := by
    have hdiv : t.thirdLogRadical / Real.log t.thirdLogRadical ≤ t.thirdLogRadical := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [mul_nonneg hxp.le (show 0 ≤ Real.log t.thirdLogRadical - 1 by linarith)]
    have hpow := Real.pow_div_factorial_le_exp ((2 / 3 : ℝ) * t.thirdLogRadical) (by positivity) 2
    norm_num at hpow
    refine hdiv.trans ((show t.thirdLogRadical ≤ (2 / 3 * t.thirdLogRadical)^2 / 2 by
      nlinarith [mul_nonneg hxp.le (sub_nonneg.mpr hx5)]).trans
      (hpow.trans ((Real.exp_le_exp.mpr ?_).trans hh)))
    exact mul_le_mul_of_nonneg_right hrate.le hxp.le
  let g : ℤ := (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * sign
  have hs0 : sign ≠ 0 := by rcases hs with h | h <;> simp [h]
  have hg : g ≠ 0 := mul_ne_zero (by exact_mod_cast (_root_.AbcTwoNinths.ExteriorE1.quotientGcdPos t).ne') hs0
  have hw' (i : _root_.AbcTwoNinths.Basic.supp t) : _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = g * w i := by rw [hw]; simp only [g, mul_assoc]
  let A := fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)
  let p : ℝ := (u r : ℝ) / ((w r : ℝ) * (g : ℝ))
  have hwR : 0 < (w r : ℝ) := by exact_mod_cast hr
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have hgp : (1 : ℝ) ≤ |(g : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |g| by have := abs_pos.mpr hg; omega)
  have hp : |p| ≤ 1 := by
    dsimp [p]
    rw [abs_div, abs_mul, abs_of_pos hwR, div_le_iff₀ (by positivity), one_mul]
    have h : |(u r : ℝ)| < (w r : ℝ) := by exact_mod_cast hur
    exact h.le.trans (by simpa using mul_le_mul_of_nonneg_left hgp hwR.le)
  let R := fun i : _root_.AbcTwoNinths.Basic.supp t => (u i : ℝ) - p * ((g * w i : ℤ) : ℝ)
  have hR (i : _root_.AbcTwoNinths.Basic.supp t) : R i = (u i : ℝ) - (w i : ℝ) / (w r : ℝ) * (u r : ℝ) := by
    change (u i : ℝ) - ((u r : ℝ) / ((w r : ℝ) * (g : ℝ))) * ((g * w i : ℤ) : ℝ) = _
    simp only [Int.cast_mul]
    generalize (g : ℝ) = G at hgR ⊢
    field_simp [hgR, hwR.ne']
  have hR0 : R r = 0 := by rw [hR, div_self hwR.ne', one_mul, sub_self]
  have hhs : _root_.AbcTwoNinths.ExteriorE1.height A (fun i => ((g * w i : ℤ) : ℝ)) = t.logHeight := by
    simp_rw [← hw']
    exact (_root_.AbcTwoNinths.ExteriorE1.quotientSignedHeight t).symm
  have hres : _root_.AbcTwoNinths.ExteriorE1.height A R ≤ t.thirdLogRadical / Real.log t.thirdLogRadical := by
    refine (_root_.AbcTwoNinths.ExteriorE1.weightAbsLe A R (fun i => Real.log_nonneg (by
      exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.property).one_le))).trans ?_
    rw [_root_.AbcTwoNinths.ExteriorE1.sumExcludePivot r _ (by rw [hR0, mul_zero, abs_zero])]
    simpa only [hR] using hsum
  have hsource : |_root_.AbcTwoNinths.ExteriorE1.weightedLog A (fun i => ((g * w i : ℤ) : ℝ))| ≤ ε := by
    simp_rw [← hw']
    rw [_root_.AbcTwoNinths.ExteriorE1.quotientWeightedLog, abs_of_nonneg]
    · exact hcontact.trans helo.le
    · apply Real.log_nonneg
      have hb : (0 : ℝ) < t.b := by exact_mod_cast t.bpos
      apply (le_div_iff₀ hb).2
      rw [one_mul]
      exact_mod_cast (show t.b ≤ t.c by have := t.add; omega)
  have htarget : |_root_.AbcTwoNinths.ExteriorE1.weightedLog A R| ≤ ε := by
    rw [_root_.AbcTwoNinths.ExteriorE1.weightedLogApply, _root_.AbcTwoNinths.ExteriorE1.sumExcludePivot r _ (by rw [hR0, mul_zero])]
    exact (by simpa only [hR] using hlog.le)
  obtain ⟨x, y, a, b, d, hd, hdT, hi, he, hprod, ha, hb, h₁, h₂⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.reducedLogSlab Subtype.val w u r hr.ne' (fun i => _root_.AbcTwoNinths.Basic.suppPrime t i.property)
      (_root_.AbcTwoNinths.ExteriorE1.primitiveRealMultiple w r hr.ne' hprim) hind g hg p _ ε hp (by rwa [hhs])
      hres hsource htarget
  rw [hhs] at hprod ha hb
  have heq : _root_.AbcTwoNinths.ExteriorE1.quotientVec t = g • w := funext hw'
  rw [_root_.AbcTwoNinths.ExteriorE1.weightedLogApply] at h₁ h₂
  exact ⟨x, y, a, b, d, ε, hd, hdT, (by positivity : 0 < 1 / t.logHeight).trans helo,
    helog, hi, heq.trans he, hprod, ha, hb, h₁, h₂⟩

end

end AbcTwoNinths.ExteriorE1
