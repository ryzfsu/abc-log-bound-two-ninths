/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.SupportCard
public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Prime support cardinality

Bounds the cardinality of a subset of the prime support of the triple using the logarithm of its
radical. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.nativeSupportCardByLogMass`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
A subset of the triple's prime support has cardinality at most N plus three times x divided by log N. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem nativeSupportCardByLogMass (t : _root_.AbcTwoNinths.Basic.Triple) (S : Finset ℕ)
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors) (N : ℕ) (hN : 1 < N) :
    (S.card : ℝ) ≤ N + 3 * t.thirdLogRadical / Real.log (N : ℝ) := by
  have hprime p (hp : p ∈ S) := Nat.prime_of_mem_primeFactors (hS hp)
  apply _root_.AbcTwoNinths.ExteriorE2.supportCardByLogMass S N hN (fun p hp => (hprime p hp).one_le)
  have hfull :
      (∑ p ∈ (t.a * t.b * t.c).primeFactors, Real.log (p : ℝ)) = 3 * t.thirdLogRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical
    push_cast
    rw [Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    ring
  rw [← hfull]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))

end

end AbcTwoNinths.ExteriorE2
