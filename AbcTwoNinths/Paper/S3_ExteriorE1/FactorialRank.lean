/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SlabPenalty

/-!
# Factorial Rank

The module bounds the factorial of the support size by a product of distinct primes. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.factorialLeProductOfPrimes`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

private theorem factorialFinProduct (d : ℕ) :
    (d + 1).factorial = ∏ i : Fin d, (i.val + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.factorial_succ, ih, Fin.prod_univ_castSucc]
    simp [mul_comm]

/--
The product of a finite set of primes bounds the factorial of its cardinality plus one. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem factorialLeProductOfPrimes (S : Finset ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p) :
    (S.card + 1).factorial ≤ ∏ p ∈ S, p := by
  let e := S.orderEmbOfFin (rfl : S.card = S.card)
  have he (j : ℕ) (hj : j < S.card) : j + 2 ≤ e ⟨j, hj⟩ := by
    induction j with
    | zero => exact (hp _ (S.orderEmbOfFin_mem rfl ⟨0, hj⟩)).two_le
    | succ j ih =>
      have hj' : j < S.card := by omega
      have he' : e ⟨j, hj'⟩ < e ⟨j+1, hj⟩ := e.strictMono (by exact Nat.lt_succ_self j)
      have := ih hj'
      omega
  rw [factorialFinProduct]
  calc
    _ ≤ ∏ i : Fin S.card, e i := Finset.prod_le_prod fun i _ => he i.val i.isLt
    _ = _ := by
      have h := S.map_orderEmbOfFin_univ (rfl : S.card = S.card)
      calc
        _ = ∏ p ∈ Finset.univ.map e.toEmbedding, p := (Finset.prod_map _ _ _).symm
        _ = _ := congrArg (fun U : Finset ℕ => ∏ p ∈ U, p) h

end

end AbcTwoNinths.ExteriorE1
