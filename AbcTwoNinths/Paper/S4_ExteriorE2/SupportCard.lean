/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Support Card

The module bounds the cardinality of a prime support from the logarithmic mass of its product. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.supportCardByLogMass`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
A finite set of positive naturals with logarithmic mass at most `B` has at most
`N + B / log N` elements for every natural cutoff `N > 1` .
-/
theorem supportCardByLogMass (S : Finset ℕ) (N : ℕ) (hN : 1 < N)
    (hp : ∀ p ∈ S, 1 ≤ p) {B : ℝ} (hB : ∑ p ∈ S, Real.log (p : ℝ) ≤ B) :
    (S.card : ℝ) ≤ N + B / Real.log (N : ℝ) := by
  classical
  let F := S.filter (fun p => p < N)
  let G := S.filter (fun p => ¬ p < N)
  have hF : F ⊆ Finset.range N := by
    intro p h
    exact Finset.mem_range.mpr (Finset.mem_filter.mp h).2
  have hFc : (F.card : ℝ) ≤ N := by
    exact_mod_cast (show F.card ≤ N by simpa using Finset.card_le_card hF)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hGsum : ∑ p ∈ G, Real.log (p : ℝ) ≤ B := by
    apply le_trans _ hB
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hs _ => Real.log_nonneg (by exact_mod_cast hp p hs))
  have hGc : (G.card : ℝ) ≤ B / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hL).mpr
    calc
      (G.card : ℝ) * Real.log (N : ℝ) = ∑ _p ∈ G, Real.log (N : ℝ) := by simp
      _ ≤ ∑ p ∈ G, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p h
        exact Real.log_le_log (by positivity)
          (by exact_mod_cast Nat.le_of_not_gt (Finset.mem_filter.mp h).2)
      _ ≤ B := hGsum
  have hcard : F.card + G.card = S.card := Finset.card_filter_add_card_filter_not _
  have heq : (F.card : ℝ) + (G.card : ℝ) = S.card := by exact_mod_cast hcard
  linarith

end

end AbcTwoNinths.ExteriorE2
