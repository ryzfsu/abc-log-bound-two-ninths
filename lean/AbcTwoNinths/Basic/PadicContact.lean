/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PadicDeterminantDivisibility
public import AbcTwoNinths.Basic.NewtonInterpolation

/-!
# Padic Contact

The module proves a p-adic divisibility bound for a matrix evaluated by Newton expansion.

## Main results
* `AbcTwoNinths.Basic.newtonMatrixDvd`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open scoped BigOperators

/--
A power divides the determinant of binomial-exponential entries with entrywise divisible errors under the Newton degree budget.
-/
theorem newtonMatrixDvd {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (p g : R) (hp : p ∣ g - 1) (E c : ℕ) (k t z : I → ℕ) (err : Matrix I I R)
    (he : ∀ i j, p ^ Fintype.card I ∣ err i j)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    p ^ E ∣ Matrix.det (fun i j =>
      (Nat.choose (c * z j) (k i) : R) * g ^ (t i * z j) + err i j : Matrix I I R) := by
  let D := (Finset.univ.sup z) + 1
  let M := (Finset.univ.sup fun ij : I × I => t ij.1 * z ij.2) + 1
  let C (i : I) (n : Fin D) : R := ∑ m ∈ Finset.range M, (g-1)^m *
    (_root_.AbcTwoNinths.Basic.newtonCoefficient (fun y => ((c*y).choose (k i) : ℤ) * ((t i*y).choose m : ℤ)) n.val : R)
  have hC (i) (n : Fin D) : p ^ (n.val-k i) ∣ C i n :=
    _root_.AbcTwoNinths.Basic.newtonWeightedDvd p g hp c (k i) (t i) n.val M
  have hX (i j : I) : (Nat.choose (c*z j) (k i) : R) * g ^ (t i*z j) =
      ∑ n : Fin D, C i n * (Nat.choose (z j) n.val : R) := by
    have hz : z j < D := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))
    have ht : t i*z j < M := Nat.lt_succ_of_le
      (Finset.le_sup (f := fun ij : I × I => t ij.1 * z ij.2) (Finset.mem_univ (i,j)))
    rw [_root_.AbcTwoNinths.Basic.weightedNewtonExpansion g c (k i) (t i) (z j) D M hz ht]
    exact (Fin.sum_univ_eq_sum_range (fun n => (∑ m ∈ Finset.range M,
      (g-1)^m * (_root_.AbcTwoNinths.Basic.newtonCoefficient (fun y => ((c*y).choose (k i) : ℤ) *
        ((t i*y).choose m : ℤ)) n : R)) * (Nat.choose (z j) n : R)) D).symm
  have h := _root_.AbcTwoNinths.Basic.determinantDvdWithErrors p E D k C
    (fun n j => (Nat.choose (z j) n.val : R)) err hC he hE
  suffices hh : (fun i j => (Nat.choose (c*z j) (k i) : R) *
      g ^ (t i * z j) + err i j : Matrix I I R) =
        (fun i => (∑ n, C i n • fun j => (Nat.choose (z j) n.val : R)) + err i) by
    rw [hh]
    exact h
  funext i j
  simp [hX, Finset.sum_apply]

end

end AbcTwoNinths.Basic
