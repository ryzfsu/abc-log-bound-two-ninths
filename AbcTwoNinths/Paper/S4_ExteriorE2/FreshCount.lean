/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.AdaptiveShell

/-!
# Fresh Count

The module bounds the number of fresh primes left after excluding a finite covered set. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.coverCount`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE2

section

/--
Every prime up to the cutoff is fresh, below or at the square-root cutoff, or a divisor of twice the radical. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem coverCount {R : ℕ} (hR : R ≠ 0) {S : ℝ} (hS : 0 ≤ S) :
    Nat.primeCounting ⌊S⌋₊ ≤ (_root_.AbcTwoNinths.ExteriorE2.fresh R S).card +
      Nat.primeCounting ⌊Real.sqrt S⌋₊ + (2*R).primeFactors.card := by
  classical
  have hsub : Nat.primesLE ⌊S⌋₊ ⊆
      (_root_.AbcTwoNinths.ExteriorE2.fresh R S ∪ Nat.primesLE ⌊Real.sqrt S⌋₊) ∪ (2*R).primeFactors := by
    intro q hq
    obtain ⟨hqS,hqP⟩ := Nat.mem_primesLE.mp hq
    by_cases hd : q ∣ 2*R
    · exact Finset.mem_union_right _ (hqP.mem_primeFactors hd (by positivity))
    · apply Finset.mem_union_left
      by_cases hlo : Real.sqrt S < (q : ℝ)
      · exact Finset.mem_union_left _ ((_root_.AbcTwoNinths.ExteriorE2.memFresh hS).2
          ⟨hqP, hlo, (Nat.le_floor_iff hS).1 hqS, hd⟩)
      · exact Finset.mem_union_right _ (Nat.mem_primesLE.2
          ⟨(Nat.le_floor_iff (Real.sqrt_nonneg S)).2 (le_of_not_gt hlo), hqP⟩)
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/--
The prime-counting estimate and exclusion budget leave at least `S / (4 * log S)` fresh primes.
-/
theorem freshCountLower {R : ℕ} (hR : R ≠ 0) {S : ℝ} (hS : 1 < S)
    (hpi : S / (2*Real.log S) ≤ (Nat.primeCounting ⌊S⌋₊ : ℝ))
    (hexcl : (Nat.primeCounting ⌊Real.sqrt S⌋₊ : ℝ) + ((2*R).primeFactors.card : ℝ)
      ≤ S / (4*Real.log S)) :
    S/(4*Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ) := by
  have h := _root_.AbcTwoNinths.ExteriorE2.coverCount hR (show 0 ≤ S by linarith)
  have h' : (Nat.primeCounting ⌊S⌋₊ : ℝ) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ) +
      (Nat.primeCounting ⌊Real.sqrt S⌋₊ : ℝ) + ((2*R).primeFactors.card : ℝ) := by
    exact_mod_cast h
  have hd : S / (2*Real.log S) = 2*(S/(4*Real.log S)) := by ring
  linarith

end

end AbcTwoNinths.ExteriorE2
