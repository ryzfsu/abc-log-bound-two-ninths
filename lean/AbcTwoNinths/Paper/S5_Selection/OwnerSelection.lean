/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import Mathlib.Tactic

/-!
# Concentration at a single prime

Uses the exterior estimates to show that a single prime accounts for the large valuation mass. It
supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.ownerSelectionOfE1E2`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

open Finset

section

/--
The full and truncated mass bounds and the pair-product bound select a unique support element above the cutoff with the stated mass. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem ownerSelectionOfE1E2 {S : Finset ℕ} {v : ℕ → ℕ}
    {H κ T x : ℝ}
    (hpos : 0 < (1 - 2 * κ) * H)
    (hfull : (1 - κ) * H ≤ ∑ q ∈ S, (v q : ℝ) * Real.log q)
    (hsmall : (∑ q ∈ S.filter (fun q : ℕ => (q : ℝ) ≤ T),
      (v q : ℝ) * Real.log q) ≤ κ * H)
    (hcut : 0 < T)
    (hsep : Real.exp x ≤ T ^ 2)
    (hpair : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → (p : ℝ) * q ≤ Real.exp x) :
    ∃ p ∈ S, T < (p : ℝ) ∧
      (∀ q ∈ S, T < (q : ℝ) → q = p) ∧
      (1 - 2 * κ) * H ≤ (v p : ℝ) * Real.log p := by
  classical
  let f : ℕ → ℝ := fun q => (v q : ℝ) * Real.log q
  let U := S.filter (fun q : ℕ => ¬ (q : ℝ) ≤ T)
  have hsplit : (∑ q ∈ S.filter (fun q : ℕ => (q : ℝ) ≤ T), f q) +
      (∑ q ∈ U, f q) = ∑ q ∈ S, f q := by
    exact Finset.sum_filter_add_sum_filter_not S (fun q : ℕ => (q : ℝ) ≤ T) f
  have hmass : (1 - 2 * κ) * H ≤ ∑ q ∈ U, f q := by
    change (∑ q ∈ S.filter (fun q : ℕ => (q : ℝ) ≤ T), f q) ≤ κ * H at hsmall
    change (1 - κ) * H ≤ ∑ q ∈ S, f q at hfull
    linarith
  have hU : U.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hmass
    exact (not_lt_of_ge hmass) hpos
  obtain ⟨p, hp⟩ := hU
  have hp' := Finset.mem_filter.mp hp
  have hpT := lt_of_not_ge hp'.2
  have hu : ∀ q ∈ S, T < (q : ℝ) → q = p := by
    intro q hq hqT
    by_contra hn
    have hl : T * T < (q : ℝ) * p := calc
      T * T < (q : ℝ) * T := mul_lt_mul_of_pos_right hqT hcut
      _ < (q : ℝ) * p := mul_lt_mul_of_pos_left hpT (hcut.trans hqT)
    rw [← pow_two] at hl
    exact (not_lt_of_ge ((hpair q hq p hp'.1 hn).trans hsep)) hl
  have heq : U = {p} := by
    ext q
    simp only [Finset.mem_singleton]
    constructor
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      exact hu q hq'.1 (lt_of_not_ge hq'.2)
    · rintro rfl
      exact hp
  exact ⟨p, hp'.1, hpT, hu, by simpa only [heq, Finset.sum_singleton, f] using hmass⟩

end

end AbcTwoNinths.Selection
