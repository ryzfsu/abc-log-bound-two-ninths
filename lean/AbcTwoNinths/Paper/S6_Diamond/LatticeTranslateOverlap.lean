/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice

/-!
# Volume of a weighted ball

Gives a lower bound for the volume of a weighted ball in terms of its radius and coordinate weights.
It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.ballVolumeLower`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

section



variable {I : Type*} [Fintype I] [DecidableEq I]

-- The elaboration of lattice translate overlap needs a larger budget.
set_option maxHeartbeats 500000

omit [DecidableEq I] in
/--
For positive weights of sum at most B, the open weighted ball of radius r has volume at least (r / B) to the power of the dimension. This is used in Section 6 of the paper.
-/
theorem ballVolumeLower (weight : I → ℝ) (hw : ∀ i, 0 < weight i)
    {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (hsum : ∑ i, weight i ≤ B) :
    (r / B)^Fintype.card I ≤ (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 r) := by
  let t := r / (2 * B)
  have ht : 0 < t := by positivity
  let box : Set (_root_.AbcTwoNinths.ExteriorE2.Coord I) := Set.pi Set.univ (fun _ : I => Set.Icc (-t) t)
  have hsub : box ⊆ _root_.AbcTwoNinths.ExteriorE2.ball weight 0 r := by
    intro z hz
    have hz' (i : I) : |z i| ≤ t := abs_le.mpr (hz i (mem_univ _))
    change _root_.AbcTwoNinths.ExteriorE2.cost weight (z - 0) < r
    rw [sub_zero]
    calc
      _root_.AbcTwoNinths.ExteriorE2.cost weight z ≤ ∑ i, weight i * t :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz' i) (hw i).le
      _ = (∑ i, weight i) * t := (Finset.sum_mul _ _ _).symm
      _ ≤ B * t := mul_le_mul_of_nonneg_right hsum ht.le
      _ = r / 2 := by dsimp [t]; field_simp
      _ < r := by linarith
  have hball : (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)) (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 r) ≠ ⊤ := by
    let big : Set (_root_.AbcTwoNinths.ExteriorE2.Coord I) := Set.pi Set.univ (fun i => Set.Icc (-(r / weight i)) (r / weight i))
    have hs : _root_.AbcTwoNinths.ExteriorE2.ball weight 0 r ⊆ big := by
      intro z hz i _
      have hz' : weight i * |z i| ≤ _root_.AbcTwoNinths.ExteriorE2.cost weight z :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (abs_nonneg _)) (Finset.mem_univ i)
      change _root_.AbcTwoNinths.ExteriorE2.cost weight (z - 0) < r at hz
      rw [sub_zero] at hz
      exact abs_le.mp ((le_div_iff₀ (hw i)).mpr (by rw [mul_comm]; exact hz'.trans hz.le))
    have hc : IsCompact big := isCompact_univ_pi fun _ => isCompact_Icc
    exact (lt_of_le_of_lt (measure_mono hs) hc.measure_lt_top).ne
  have hvol : (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real box = (r / B)^Fintype.card I := by
    have ht2 : t - -t = r / B := by dsimp [t]; ring
    simp only [box, measureReal_def, volume_pi, Measure.pi_pi, Real.volume_Icc, ht2,
      Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by positivity : 0 ≤ r / B),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / B)^Fintype.card I)]
  exact hvol ▸ measureReal_mono hsub hball

end

end
end AbcTwoNinths.Diamond
