/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Factorization Monomial Powers

The module relates exponent-vector scaling to a monomial power and splits off the remaining factor. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.monomialSplit`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
Multiplying the exponent vector by a natural number raises its rational monomial to that power.
-/
theorem monomialNsmul {ι : Type*} [Fintype ι] (q : ι → ℕ) (k : ℕ) (e : ι → ℤ) :
    (∏ i, (q i : ℚ) ^ ((k • e) i)) = (∏ i, (q i : ℚ) ^ e i) ^ k := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]

/--
The monomial on positive natural bases is the ratio of its positive and negative exponent products. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem monomialSplit {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℤ)
    (hq : ∀ i, 0 < q i) :
    (∏ i, (q i : ℚ) ^ e i) =
      ((∏ i, q i ^ (e i).toNat : ℕ) : ℚ) /
        ((∏ i, q i ^ (-e i).toNat : ℕ) : ℚ) := by
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by exact_mod_cast (hq i).ne')]
  congr 1
  omega

end

end AbcTwoNinths.PolyCap
