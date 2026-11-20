/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Roof Peak

The module bounds the weight of a prime and the largest valuation mass on the chosen support. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.peakMassSubtypeLe`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section

/-- The sum of prime logarithms on any subset of the triple's support is at most three times x. -/
theorem logWeightLeThreeX (t : _root_.AbcTwoNinths.Basic.Triple) {S : Finset ℕ}
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors) :
    (∑ q ∈ S, Real.log (q : ℝ)) ≤ 3 * t.thirdLogRadical := by
  have hR : 0 < t.radical := Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hd : (∏ q ∈ S, q) ∣ t.radical := Finset.prod_dvd_prod_of_subset _ _ id hS
  have hpos : 0 < ∏ q ∈ S, q :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors (hS h)).pos
  have h := Real.log_le_log
    (show (0 : ℝ) < ↑(∏ q ∈ S, q) by exact_mod_cast hpos)
    (show (↑(∏ q ∈ S, q) : ℝ) ≤ t.radical by exact_mod_cast Nat.le_of_dvd hR hd)
  rw [Nat.cast_prod, Real.log_prod (fun q hq =>
    by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hq)).ne_zero)] at h
  unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical
  linarith

/--
A natural bound on the absolute exponents bounds their logarithmic mass by that bound times three times x.
-/
theorem peakMassLe (t : _root_.AbcTwoNinths.Basic.Triple) {S : Finset ℕ}
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors) (v : ℕ → ℤ) {P : ℕ}
    (hpeak : ∀ q ∈ S, (v q).natAbs ≤ P) :
    (∑ q ∈ S, ((v q).natAbs : ℝ) * Real.log (q : ℝ)) ≤ (P : ℝ) * (3 * t.thirdLogRadical) := by
  calc
    _ ≤ ∑ q ∈ S, (P : ℝ) * Real.log (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hpeak q hq
      · exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hq)).one_lt.le)
    _ = (P : ℝ) * ∑ q ∈ S, Real.log (q : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.AbcTwoNinths.Selection.logWeightLeThreeX t hS) (by positivity)

/--
Exponents indexed by the support subtype satisfy the same bound on their weighted mass. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem peakMassSubtypeLe (t : _root_.AbcTwoNinths.Basic.Triple) {S : Finset ℕ}
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors)
    (v : {q // q ∈ S} → ℤ) {P : ℕ} (hpeak : ∀ q, (v q).natAbs ≤ P) :
    (∑ q : {q // q ∈ S}, ((v q).natAbs : ℝ) * Real.log (q.val : ℝ)) ≤
      (P : ℝ) * (3 * t.thirdLogRadical) := by
  classical
  let w (q : ℕ) := if h : q ∈ S then v ⟨q, h⟩ else 0
  have hw : ∀ q ∈ S, (w q).natAbs ≤ P := by
    intro q hq
    simpa [w, hq] using hpeak ⟨q, hq⟩
  have he := _root_.AbcTwoNinths.Selection.peakMassLe t hS w hw
  rw [← Finset.sum_attach] at he
  simpa [w] using he

end

end AbcTwoNinths.Selection
