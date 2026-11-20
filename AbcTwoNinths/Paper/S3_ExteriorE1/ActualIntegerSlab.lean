/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ActualSlabBudget
public import AbcTwoNinths.Paper.S3_ExteriorE1.PositivePivot

/-!
# Actual Integer Slab

The module applies the integer slab bound to the parameters of an ordered source triple. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.actualIntegerSlab`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
Failure of the real estimate beyond the stated thresholds yields a primitive pivot vector and an independent integer vector with controlled logarithmic sums. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem actualIntegerSlab (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ)
    (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hh : Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) ≤ t.logHeight)
    (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) (hx : Real.exp 4 ≤ t.thirdLogRadical)
    (hon₁ : Real.exp (192 * Real.log (768 / _root_.AbcTwoNinths.Statement.highRate η) / _root_.AbcTwoNinths.Statement.highRate η) ≤ t.thirdLogRadical)
    (hon₂ : (16 / _root_.AbcTwoNinths.Statement.highRate η) *
      (max 0 (Real.log (9 / κ)) + 2 * Real.log (32 / _root_.AbcTwoNinths.Statement.highRate η)) ≤ t.thirdLogRadical) :
    ∃ (u w : _root_.AbcTwoNinths.Basic.supp t → ℤ) (r : _root_.AbcTwoNinths.Basic.supp t) (ε : ℝ) (s : ℤ),
      (s = 1 ∨ s = -1) ∧ (∀ i, _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * (s * w i)) ∧
      _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w ∧ 0 < w r ∧ |u r| < w r ∧ (∀ i, |w i| ≤ w r) ∧
      ¬ (∃ z : ℝ, ∀ i, (u i : ℝ) = z * (w i : ℝ)) ∧
      1 / t.logHeight < ε ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
      (∑ i : {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r},
        |Real.log (i.val.val : ℝ) *
        ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))|) ≤
        t.thirdLogRadical / Real.log t.thirdLogRadical ∧
      |∑ i : {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r}, Real.log (i.val.val : ℝ) *
        ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))| < ε := by
  classical
  have hxp : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le hx
  have hhigh : _root_.AbcTwoNinths.Statement.High η 0 t := ⟨hxp.le, hh⟩
  obtain ⟨hcard, hg, hgk⟩ := _root_.AbcTwoNinths.ExteriorE1.orderedFailureInputs η hη κ hκ t hab hhigh hf
  obtain ⟨w, s, r, hs, hw, hprim, hwr, hmax, hlo, hhi⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.actualPositivePivot η hη κ hκ t hab hhigh hf
  let α := {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r}
  have : Nonempty α := by
    by_contra! h
    have he (i : _root_.AbcTwoNinths.Basic.supp t) : i = r := by
      by_contra hi
      exact h.false ⟨i, hi⟩
    let : Subsingleton (_root_.AbcTwoNinths.Basic.supp t) := ⟨fun i j => (he i).trans (he j).symm⟩
    have hc : (_root_.AbcTwoNinths.Basic.supp t).card ≤ 1 := by
      simpa using (Fintype.card_le_one_iff_subsingleton (α := _root_.AbcTwoNinths.Basic.supp t)).2 inferInstance
    omega
  have hm : (0 : ℝ) < w r := by exact_mod_cast hwr
  have hgR : (0 : ℝ) < _root_.AbcTwoNinths.ExteriorE1.quotientGcd t := by exact_mod_cast hg
  have hlow : κ * t.logHeight / (3 * t.thirdLogRadical) ≤ (w r : ℝ) := by
    have hga := (lt_div_iff₀ hκ).mp hgk
    have hw' := (div_le_iff₀ (by positivity : 0 < (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical))).mp hlo
    apply (div_le_iff₀ (by positivity : 0 < 3 * t.thirdLogRadical)).mpr
    calc
      κ * t.logHeight ≤ (κ * (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ)) * ((w r : ℝ) * (3 * t.thirdLogRadical)) := by
        convert mul_le_mul_of_nonneg_left hw' hκ.le using 1
        ring
      _ ≤ _ := by
        have hga' : κ * (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) ≤ 1 := by linarith
        exact mul_le_of_le_one_left (by positivity) hga'
  let T := t.thirdLogRadical / Real.log t.thirdLogRadical
  let a : α → ℝ := fun i => Real.log (i.val.val : ℝ)
  let d := Fintype.card α
  let ε := (3 * T / (w r : ℝ)) * (1 + 3 * Real.log t.thirdLogRadical) ^ d
  let N : α → ℕ := fun i => ⌈(d : ℝ) * a i / T⌉₊
  let M : ℕ := ⌈T / ε⌉₊
  obtain ⟨hT, _, he, _, helog, helo, hc⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.actualSlabBudget η hη κ hκ t r (w r : ℝ) hm hlow hhi hx hh hon₁ hon₂
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha (i : α) : 0 < a i := Real.log_pos (by
    exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.val.property).one_lt)
  obtain ⟨hN, _, hbudget⟩ := _root_.AbcTwoNinths.ExteriorE1.ceilCapacity a ha T hTp
  have hM : 0 < M := Nat.ceil_pos.mpr (div_pos hTp he)
  have hc' : M * (∏ i, N i) < (w r).toNat := by
    have hcast : ((w r).toNat : ℝ) = (w r : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hwr.le
    apply (Nat.cast_lt (α := ℝ)).mp
    rw [Nat.cast_mul, Nat.cast_prod, hcast]
    exact hc
  obtain ⟨u, _, hur, hcoord, hsum, hind⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.integerSlab r w hwr hprim N hN hM a ha T hTp hbudget hc'
  refine ⟨u, w, r, ε, s, hs, hw, hprim, hwr, hur, hmax, hind, helo, helog, ?_, ?_⟩
  · exact (Finset.sum_le_sum fun i _ => (hcoord i).le).trans hbudget
  · have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    refine hsum.trans_le ((div_le_iff₀ hMR).mpr ?_)
    have := (div_le_iff₀ he).mp (Nat.le_ceil (T / ε))
    change T ≤ (M : ℝ) * ε at this
    rwa [mul_comm]

end

end AbcTwoNinths.ExteriorE1
