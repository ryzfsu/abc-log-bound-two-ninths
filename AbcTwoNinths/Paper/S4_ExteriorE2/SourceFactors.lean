/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Source Factors

The module rewrites products of prime powers as monomial parts of a difference of factorizations. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.partsOfFactorDifference`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



private theorem factorProduct {N : ℕ} (hN : N ≠ 0) (s : Finset ℕ)
    (hs : N.primeFactors ⊆ s) :
    (∏ p : s, (p : ℕ) ^ N.factorization p) = N := by
  classical
  rw [Finset.prod_coe_sort s (fun p : ℕ => p ^ N.factorization p)]
  rw [← Finset.prod_subset hs, ← Nat.prod_primeFactors_pow_factorization hN]
  intro p _ hp
  have hz : N.factorization p = 0 := by
    by_contra h
    exact hp (Finsupp.mem_support_iff.mpr h)
  simp [hz]

/--
On any prime set containing the supports of nonzero coprime `A` and `D` , the positive and
negative part products of the factorization difference recover `A` and `D` respectively.
-/
theorem partsOfFactorDifference {A D : ℕ} (hA : A ≠ 0) (hD : D ≠ 0)
    (hc : A.Coprime D) (s : Finset ℕ) (ha : A.primeFactors ⊆ s)
    (hd : D.primeFactors ⊆ s) (hs : ∀ p ∈ s, Nat.Prime p) :
    let e := fun p : s => (A.factorization p : ℤ) - D.factorization p
    _root_.AbcTwoNinths.PolyCap.posPartNat (fun p : s => (p : ℕ)) e = A ∧
      _root_.AbcTwoNinths.PolyCap.negPartNat (fun p : s => (p : ℕ)) e = D := by
  classical
  let e := fun p : s => (A.factorization p : ℤ) - D.factorization p
  have hcoord (p : s) : (e p).toNat = A.factorization p ∧
      (-e p).toNat = D.factorization p := by
    have hp := hs p p.property
    by_cases h : (p : ℕ) ∣ A
    · have hnd : ¬ (p : ℕ) ∣ D := fun hd =>
        hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd h hd)
      simp [e, Nat.factorization_eq_zero_of_not_dvd hnd]
    · simp [e, Nat.factorization_eq_zero_of_not_dvd h]
  constructor
  · change (∏ p : s, (p : ℕ) ^ (e p).toNat) = A
    simpa only [(fun p => (hcoord p).1)] using factorProduct hA s ha
  · change (∏ p : s, (p : ℕ) ^ (-(e p)).toNat) = D
    simpa only [(fun p => (hcoord p).2)] using factorProduct hD s hd

end

end AbcTwoNinths.ExteriorE2
