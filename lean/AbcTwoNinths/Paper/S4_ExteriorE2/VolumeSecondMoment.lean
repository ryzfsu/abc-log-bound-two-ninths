/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

/-!
# Volume Second Moment

The module turns a multiplicity second moment into a lower bound for intersecting pairs of translates. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.overlapLower`
-/

@[expose] public section
namespace AbcTwoNinths.ExteriorE2

open MeasureTheory
open scoped BigOperators

section

variable {X : Type*}

/--
Counts one when the first index is smaller and the two centers intersect. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def hit (A : ℕ → Set X) (i j : ℕ) : ℕ := by
  classical
  exact if i < j ∧ (A i ∩ A j).Nonempty then 1 else 0

/--
Counts unordered intersecting pairs of centers in a finite family. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def overlaps (Q : Finset ℕ) (A : ℕ → Set X) : ℕ :=
  ∑ i ∈ Q, ∑ j ∈ Q, _root_.AbcTwoNinths.ExteriorE2.hit A i j

variable [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/--
Sums the real indicator functions of all centers at a point. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def multiplicity (Q : Finset ℕ) (A : ℕ → Set X) (x : X) : ℝ :=
  ∑ i ∈ Q, (A i).indicator (1 : X → ℝ) x

/--
Bounds the sum of pairwise intersection measures below by the squared total center mass divided by the ambient measure.
-/
theorem secondMoment (Q : Finset ℕ) (A : ℕ → Set X)
    (hA : ∀ i ∈ Q, MeasurableSet (A i)) (W : ℝ) (hw : ∀ i ∈ Q, μ.real (A i) = W)
    (hμ : 0 < μ.real Set.univ) :
    ((Q.card : ℝ) * W) ^ 2 / μ.real Set.univ ≤
      ∑ i ∈ Q, ∑ j ∈ Q, μ.real (A i ∩ A j) := by
  classical
  let I := fun (s : Set X) => s.indicator (1 : X → ℝ)
  have hI (s : Set X) (hs : MeasurableSet s) : Integrable (I s) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have hf : Integrable (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A) μ :=
    integrable_finsetSum Q fun i hi => hI _ (hA i hi)
  have hf1 : ∫ x, _root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x ∂μ = (Q.card : ℝ) * W := by
    unfold _root_.AbcTwoNinths.ExteriorE2.multiplicity
    rw [integral_finsetSum Q (fun i hi => hI _ (hA i hi))]
    calc
      _ = ∑ _i ∈ Q, W := Finset.sum_congr rfl (fun i hi =>
        (integral_indicator_one (hA i hi)).trans (hw i hi))
      _ = _ := by simp
  have hsq (x : X) : (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x)^2 =
      ∑ i ∈ Q, ∑ j ∈ Q, I (A i ∩ A j) x := by
    simp only [_root_.AbcTwoNinths.ExteriorE2.multiplicity, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;> simp [I, hi, hj]
  have hj (i : ℕ) (hi : i ∈ Q) :
      Integrable (fun x => ∑ j ∈ Q, I (A i ∩ A j) x) μ :=
    integrable_finsetSum Q fun j h => hI _ ((hA i hi).inter (hA j h))
  have hsqint : Integrable (fun x => (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x)^2) μ := by
    simp_rw [hsq]
    exact integrable_finsetSum Q hj
  have hf2 : ∫ x, (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x)^2 ∂μ =
      ∑ i ∈ Q, ∑ j ∈ Q, μ.real (A i ∩ A j) := by
    simp_rw [hsq]
    rw [integral_finsetSum Q hj]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Q (fun j h => hI _ ((hA i hi).inter (hA j h)))]
    exact Finset.sum_congr rfl (fun j h => integral_indicator_one ((hA i hi).inter (hA j h)))
  let c := (Q.card : ℝ) * W / μ.real Set.univ
  have hlin := integral_mono (μ := μ) ((hf.const_mul (2*c)).sub (integrable_const (c^2))) hsqint
    (fun x => show 2 * c * _root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x - c ^ 2 ≤ (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x)^2 by
      nlinarith [sq_nonneg (_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x - c)])
  change (∫ x, 2*c*_root_.AbcTwoNinths.ExteriorE2.multiplicity Q A x - c^2 ∂μ) ≤ _ at hlin
  rw [integral_sub (hf.const_mul (2*c)) (integrable_const (c^2)), integral_const_mul,
      hf1, integral_const, hf2, smul_eq_mul] at hlin
  dsimp [c] at hlin
  convert hlin using 1
  field_simp
  ring

/--
Bounds the intersection sum by the center mass times the number of diagonal and ordered overlapping pairs.
-/
theorem overlapUpper (Q : Finset ℕ) (A : ℕ → Set X)
    (W : ℝ) (hw : ∀ i ∈ Q, μ.real (A i) = W) :
    (∑ i ∈ Q, ∑ j ∈ Q, μ.real (A i ∩ A j)) ≤
      (Q.card : ℝ)*W + 2*(_root_.AbcTwoNinths.ExteriorE2.overlaps Q A : ℝ)*W := by
  classical
  let d := fun (i j : ℕ) => if j = i then W else 0
  let a := fun (i j : ℕ) => (_root_.AbcTwoNinths.ExteriorE2.hit A i j : ℝ) * W
  have hp (i j : ℕ) (hi : i ∈ Q) :
      μ.real (A i ∩ A j) ≤ d i j + (a i j + a j i) := by
    have hm := (measureReal_mono (μ := μ) (Set.inter_subset_left (s := A i) (t := A j))).trans_eq (hw i hi)
    rcases lt_trichotomy i j with h|rfl|h
    · by_cases hx : (A i ∩ A j).Nonempty
      · simpa [d, a, _root_.AbcTwoNinths.ExteriorE2.hit, h, h.ne', hx, h.not_gt] using hm
      · simp [d, a, _root_.AbcTwoNinths.ExteriorE2.hit, h, h.ne', h.not_gt, Set.not_nonempty_iff_eq_empty.mp hx]
    · simp [d, a, _root_.AbcTwoNinths.ExteriorE2.hit, hw i hi]
    · by_cases hx : (A j ∩ A i).Nonempty
      · simpa [d, a, _root_.AbcTwoNinths.ExteriorE2.hit, h, h.ne, hx, h.not_gt] using hm
      · have hem : A i ∩ A j = ∅ := by rw [Set.inter_comm]; exact Set.not_nonempty_iff_eq_empty.mp hx
        simp [d, a, _root_.AbcTwoNinths.ExteriorE2.hit, h, h.ne, hx, h.not_gt, hem]
  have hh := Finset.sum_le_sum (s := Q) fun i hi =>
    Finset.sum_le_sum (s := Q) fun j _ => hp i j hi
  have hdiag : (∑ i ∈ Q, ∑ j ∈ Q, d i j) = (Q.card : ℝ)*W := by simp [d]
  have hab : (∑ i ∈ Q, ∑ j ∈ Q, a i j) = (_root_.AbcTwoNinths.ExteriorE2.overlaps Q A : ℝ)*W := by
    simp [_root_.AbcTwoNinths.ExteriorE2.overlaps, a, Finset.sum_mul]
  have hsym : (∑ i ∈ Q, ∑ j ∈ Q, a j i) = (∑ i ∈ Q, ∑ j ∈ Q, a i j) := Finset.sum_comm
  simp only [Finset.sum_add_distrib, hdiag, hsym, hab] at hh
  linarith

/--
Bounds the number of intersecting unordered pairs from below for a nonempty family of equal positive measure. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem overlapLower (Q : Finset ℕ) (hQ : Q.Nonempty) (A : ℕ → Set X)
    (hA : ∀ i ∈ Q, MeasurableSet (A i)) (W : ℝ) (hW : 0 < W)
    (hw : ∀ i ∈ Q, μ.real (A i) = W) :
    (Q.card : ℝ) / 2 * ((Q.card : ℝ)*W / μ.real Set.univ - 1) ≤ _root_.AbcTwoNinths.ExteriorE2.overlaps Q A := by
  obtain ⟨i, hi⟩ := hQ
  have hu := (measureReal_mono (μ := μ) (Set.subset_univ (A i)))
  have hm : 0 < μ.real Set.univ := (hw i hi ▸ hW : 0 < μ.real (A i)) |>.trans_le hu
  have hb := (_root_.AbcTwoNinths.ExteriorE2.secondMoment μ Q A hA W hw hm).trans (_root_.AbcTwoNinths.ExteriorE2.overlapUpper μ Q A W hw)
  apply (mul_le_mul_iff_of_pos_right (show 0 < 2*W by positivity)).mp
  apply (mul_le_mul_iff_of_pos_right hm).mp
  have hb' := (div_le_iff₀ hm).mp hb
  field_simp
  by_contra! hn
  nlinarith only [hb', mul_lt_mul_of_pos_right hn hW]

/--
A fresh shell prime lies in the interval open at the square root of the cutoff and closed at the cutoff, and does not divide twice the radical. This is used in the proof of Proposition 4.1 of the paper.
-/
def Fresh (M : ℝ) (R q : ℕ) : Prop :=
  q.Prime ∧ Real.sqrt M < q ∧ (q : ℝ) ≤ M ∧ ¬ q ∣ 2*R

/--
A finite set satisfying the shell supply lower bound is nonempty when the cutoff exceeds one.
-/
theorem noEmptySupply {Q : Finset ℕ} {M : ℝ} (hM : 1 < M)
    (hsupply : M / (4 * Real.log M) ≤ Q.card) : Q.Nonempty := by
  have hp : 0 < M / (4 * Real.log M) :=
    div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos hM))
  exact Finset.card_pos.mp (by exact_mod_cast hp.trans_le hsupply)

end

end AbcTwoNinths.ExteriorE2
