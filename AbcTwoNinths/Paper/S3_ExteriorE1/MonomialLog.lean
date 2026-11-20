/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusForm
public import AbcTwoNinths.Paper.S3_ExteriorE1.QuotientHeight

/-!
# Monomial Log

The module computes the logarithm of a positive real monomial and proves independence for its exponent data. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.monomialIndependent`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- A rational prime monomial is positive for all integer exponents. -/
theorem monomialPos {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (e : ι → ℤ) :
    0 < _root_.AbcTwoNinths.PolyCap.prodMonomial p e :=
  Finset.prod_pos fun i _ => zpow_pos (by exact_mod_cast (hp i).pos) _

/-- The real logarithm of a prime monomial is the exponent-weighted sum of the prime logarithms. -/
theorem monomialLog {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (e : ι → ℤ) :
    Real.log (_root_.AbcTwoNinths.PolyCap.prodMonomial p e : ℝ) =
      ∑ i, Real.log (p i : ℝ) * (e i : ℝ) := by
  simp only [_root_.AbcTwoNinths.PolyCap.prodMonomial, Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => zpow_ne_zero _ (by exact_mod_cast (hp i).ne_zero))]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.log_zpow, mul_comm]

/--
Independent integer exponent vectors on distinct primes give multiplicatively independent rational monomials. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem monomialIndependent {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (u v : ι → ℤ)
    (hi : ∀ m n : ℤ, m • u + n • v = 0 → m = 0 ∧ n = 0) :
    _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent (_root_.AbcTwoNinths.PolyCap.prodMonomial p u) (_root_.AbcTwoNinths.PolyCap.prodMonomial p v) := by
  intro m n h
  have he : _root_.AbcTwoNinths.PolyCap.prodMonomial p (m • u + n • v) =
      _root_.AbcTwoNinths.PolyCap.prodMonomial p u ^ m * _root_.AbcTwoNinths.PolyCap.prodMonomial p v ^ n := by
    simp only [_root_.AbcTwoNinths.PolyCap.prodMonomial, Pi.add_apply, Pi.smul_apply]
    rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    change (p i : ℚ) ^ (m * u i + n * v i) = _
    rw [zpow_add₀ (by exact_mod_cast (hp i).ne_zero), mul_comm m, mul_comm n, zpow_mul, zpow_mul]
  exact hi m n (funext ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff p hp hinj _).mp (he.trans h)))

end

end AbcTwoNinths.ExteriorE1
