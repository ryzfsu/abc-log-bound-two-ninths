/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Determinant Row Expansion

The module expands a determinant of row sums into a sum over subsets of rows.

## Main results
* `AbcTwoNinths.Basic.detAddEqSumPowerset`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open scoped BigOperators

/-- The determinant of a sum of real matrices expands over all choices of summand in each row. -/
theorem detAddEqSumPowerset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (A + B).det =
      ∑ s : Finset ι, (Matrix.of fun i j => if i ∈ s then A i j else B i j).det := by
  classical
  simp only [Matrix.det_apply, Matrix.add_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.smul_sum]
  congr 1
  let f (i : ι) := A (σ i) i
  let g (i : ι) := B (σ i) i
  change (∏ i, (f i + g i)) = ∑ s : Finset ι, ∏ i, if σ i ∈ s then f i else g i
  rw [Finset.prod_add, Finset.powerset_univ]
  let e : Finset ι ≃ Finset ι := σ.finsetCongr
  refine Fintype.sum_equiv e _ _ (fun t => ?_)
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp [e]

end

end AbcTwoNinths.Basic
