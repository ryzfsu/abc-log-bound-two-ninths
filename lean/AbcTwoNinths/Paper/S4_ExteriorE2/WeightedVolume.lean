/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic

/-!
# Logarithmic weight of the projected support

Bounds the sum of the logarithms of the primes outside the distinguished coordinate by the
logarithm of the radical. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.oldLogBudget`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE2

open MeasureTheory Set
open scoped ENNReal

section

/--
Coordinates indexed by members of the support other than the distinguished prime. This is used in the proof of Proposition 4.1 of the paper.
-/
abbrev OldIndex (S : Finset ℕ) (roof : ℕ) := ↥(S.erase roof)

/--
The product of distinct prime divisors in a finite support is at most the positive integer they divide.
-/
theorem supportProductLe (S : Finset ℕ) {R : ℕ} (hR : 0 < R)
    (hS : ∀ q ∈ S, q.Prime) (hdiv : ∀ q ∈ S, q ∣ R) : ∏ q ∈ S, q ≤ R := by
  have hsub : S ⊆ R.primeFactors := fun q hq =>
    Nat.mem_primeFactors.mpr ⟨hS q hq, hdiv q hq, hR.ne'⟩
  exact Nat.le_of_dvd hR (dvd_trans
    (Finset.prod_dvd_prod_of_subset S R.primeFactors id hsub) (Nat.prod_primeFactors_dvd R))

/--
If the support product is at most R and log R equals 3x, the log weights outside the distinguished coordinate sum to at most 3x. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem oldLogBudget (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) {R : ℕ} (hprod : ∏ q ∈ S, q ≤ R)
    {x : ℝ} (hx : Real.log (R : ℝ) = 3*x) :
    (∑ i : _root_.AbcTwoNinths.ExteriorE2.OldIndex S roof, Real.log (i.val : ℝ)) ≤ 3*x := by
  classical
  have hsub : S.erase roof ⊆ S := Finset.erase_subset _ _
  have hpos (q : ℕ) (hq : q ∈ S) : (0 : ℝ) < q := by exact_mod_cast (hS q hq).pos
  have hsum : (∑ q ∈ S.erase roof, Real.log (q : ℝ)) ≤ ∑ q ∈ S, Real.log (q : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun q hq _ =>
      Real.log_nonneg (by exact_mod_cast (hS q hq).one_lt.le)
  have hreal : (∏ q ∈ S, (q : ℝ)) ≤ R := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  rw [Finset.sum_coe_sort (s := S.erase roof) (f := fun q : ℕ => Real.log (q : ℝ))]
  calc
    _ ≤ (∑ q ∈ S, Real.log (q : ℝ)) := hsum
    _ = Real.log (∏ q ∈ S, (q : ℝ)) := (Real.log_prod fun q hq => (hpos q hq).ne').symm
    _ ≤ Real.log (R : ℝ) := Real.log_le_log (Finset.prod_pos hpos) hreal
    _ = _ := hx

end

end AbcTwoNinths.ExteriorE2
