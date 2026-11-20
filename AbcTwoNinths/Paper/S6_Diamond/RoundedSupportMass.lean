/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.RoundedMassForTriples
public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePlane

/-!
# Projected volume from dimension and prime weights

Bounds the dimension and weights of the projected prime support of a triple, then derives a lower
bound on the volume of its weighted ball. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.massFloorOfDimension`
* `AbcTwoNinths.Diamond.nativeDimensionWeight`
* `AbcTwoNinths.Diamond.nativeMassFloor`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

open Real MeasureTheory


section



/--
The radius used for projected separation and fresh-prime selection is twice x divided by log x. This is used in Section 6 of the paper.
-/
noncomputable def fineRadius (x : ℝ) : ℝ := 2 * x / log x

/-- The projection radius is positive for x at least exp 15. -/
theorem fineRadiusPos {x : ℝ} (hx : exp 15 ≤ x) : 0 < _root_.AbcTwoNinths.Diamond.fineRadius x := by
  have h₁ : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 15)).trans_le hx
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans h₁)) (log_pos h₁)

/--
A bound on the projected dimension and the sum of positive weights gives the mass floor at half the projection radius. This is used in Section 6 of the paper.
-/
theorem massFloorOfDimension {I : Type*} [Fintype I] (t : _root_.AbcTwoNinths.Basic.Triple)
    (S : Finset ℕ) (roof : ℕ) (hS : ∀ q ∈ S, q.Prime) (hprod : ∏ q ∈ S, q ≤ t.radical)
    (hd : Fintype.card I ≤ Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex S roof)) (hx : exp 15 ≤ t.thirdLogRadical)
    (weight : I → ℝ) (hw : ∀ i, 0 < weight i) (hW : ∑ i, weight i ≤ 3 * t.thirdLogRadical) :
    _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical ≤ (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 (_root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2)) := by
  let K : ℝ := ((⌊3 * log t.thirdLogRadical⌋₊ + 1 : ℕ) : ℝ)
  have h₁ : 1 < t.thirdLogRadical := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 15)).trans_le hx
  have hlog : 0 < log t.thirdLogRadical := log_pos h₁
  have hxpos : 0 < t.thirdLogRadical := zero_lt_one.trans h₁
  have hK : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le ⌊3 * log t.thirdLogRadical⌋₊)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hbase : 3 * log t.thirdLogRadical ≤ K := by
    dsimp [K]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have hround : _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical * K ^ Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex S roof) ≤ 1 :=
    _root_.AbcTwoNinths.Diamond.nativeRoundedMass t S roof hS hprod hx
  have hd' : K ^ Fintype.card I ≤ K ^ Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex S roof) :=
    pow_le_pow_right₀ hK hd
  have hmul : _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical * K ^ Fintype.card I ≤ 1 :=
    (mul_le_mul_of_nonneg_left hd' (exp_pos _).le).trans hround
  have hr : 0 < _root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2 := div_pos (_root_.AbcTwoNinths.Diamond.fineRadiusPos hx) (by norm_num)
  have hB : 0 < 3 * t.thirdLogRadical := by positivity
  have hinv : 1 / K ≤ (_root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2) / (3 * t.thirdLogRadical) := by
    have hratio : (_root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2) / (3 * t.thirdLogRadical) = 1 / (3 * log t.thirdLogRadical) := by
      unfold _root_.AbcTwoNinths.Diamond.fineRadius
      field_simp
    rw [hratio]
    exact one_div_le_one_div_of_le (by positivity) hbase
  calc
    _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical ≤ (1 / K) ^ Fintype.card I := by
      rw [div_pow, one_pow]
      exact (le_div_iff₀ (pow_pos hKpos _)).2 hmul
    _ ≤ ((_root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2) / (3 * t.thirdLogRadical)) ^ Fintype.card I := by
      exact pow_le_pow_left₀ (by positivity) hinv _
    _ ≤ _ := _root_.AbcTwoNinths.Diamond.ballVolumeLower weight hw hr hB hW

/--
Distinct prime divisors outside the roof coordinate bound the projected dimension and have total logarithmic weight at most 3x. This is used in Section 6 of the paper.
-/
theorem nativeDimensionWeight {I : Type*} [Fintype I] (t : _root_.AbcTwoNinths.Basic.Triple)
    (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (hi : Function.Injective old)
    (holdR : ∀ i, old i ∣ t.radical) (hR : 0 < t.radical) :
    Fintype.card I ≤ Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex t.radical.primeFactors (old (.inl ()))) ∧
      (∑ i : I, log (old (.inr i) : ℝ)) ≤ 3 * t.thirdLogRadical := by
  classical
  let S := t.radical.primeFactors
  let roof := old (.inl ())
  let e (i : I) : _root_.AbcTwoNinths.ExteriorE2.OldIndex S roof := ⟨old (.inr i), by
    apply Finset.mem_erase.mpr
    exact ⟨fun h => Sum.inr_ne_inl (hi h),
      Nat.mem_primeFactors.mpr ⟨prime (.inr i), holdR (.inr i), hR.ne'⟩⟩⟩
  have he : Function.Injective e := fun _ _ h => Sum.inr.inj (hi (congrArg Subtype.val h))
  have hS : ∀ q ∈ S, q.Prime := fun _ hq => (Nat.mem_primeFactors.mp hq).1
  have hdiv : ∀ q ∈ S, q ∣ t.radical := fun _ hq => (Nat.mem_primeFactors.mp hq).2.1
  refine ⟨Fintype.card_le_of_injective e he, ?_⟩
  calc
    (∑ i : I, log (old (.inr i) : ℝ)) ≤ ∑ j : _root_.AbcTwoNinths.ExteriorE2.OldIndex S roof, log (j.val : ℝ) := by
      apply Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
      · intro i _
        rfl
      · intro j _ _
        exact log_nonneg (by exact_mod_cast (hS j.val (Finset.mem_erase.mp j.property).2).one_lt.le)
    _ ≤ 3 * t.thirdLogRadical := _root_.AbcTwoNinths.ExteriorE2.oldLogBudget S roof hS (_root_.AbcTwoNinths.ExteriorE2.supportProductLe S hR hS hdiv) (by
      change log (t.radical : ℝ) = 3 * (log (t.radical : ℝ) / 3)
      ring)

/--
The projected ball of prime logarithmic weights at half the projection radius has volume at least the mass floor.
-/
theorem nativeMassFloor {I : Type*} [Fintype I] (t : _root_.AbcTwoNinths.Basic.Triple)
    (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (hi : Function.Injective old)
    (holdR : ∀ i, old i ∣ t.radical) (hR : 0 < t.radical) (hx : exp 15 ≤ t.thirdLogRadical) :
    _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical ≤ (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real
      (_root_.AbcTwoNinths.ExteriorE2.ball (fun i => log (old (.inr i) : ℝ)) 0 (_root_.AbcTwoNinths.Diamond.fineRadius t.thirdLogRadical / 2)) := by
  obtain ⟨hd, hW⟩ := _root_.AbcTwoNinths.Diamond.nativeDimensionWeight t old prime hi holdR hR
  let S := t.radical.primeFactors
  have hS : ∀ q ∈ S, q.Prime := fun _ hq => (Nat.mem_primeFactors.mp hq).1
  have hdiv : ∀ q ∈ S, q ∣ t.radical := fun _ hq => (Nat.mem_primeFactors.mp hq).2.1
  exact _root_.AbcTwoNinths.Diamond.massFloorOfDimension t S (old (.inl ())) hS (_root_.AbcTwoNinths.ExteriorE2.supportProductLe S hR hS hdiv)
    hd hx _ (fun i => log_pos (by exact_mod_cast (prime (.inr i)).one_lt)) hW




end

end AbcTwoNinths.Diamond
