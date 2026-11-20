/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import Mathlib

/-!
# Products

The module defines exponent evaluation on a finite prime support in rational and residue rings. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.resEval`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

noncomputable section

/-- The support. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev Support (n d : ℕ) := ↥(n.primeFactors ∪ d.primeFactors : Finset ℕ)
/-- The base. This is used in the proof of Proposition 4.1 of the paper. -/
def base (n d : ℕ) (i : _root_.AbcTwoNinths.ExteriorE2.Support n d) : ℕ := i.val
/-- Each member of the union of the prime supports of `n` and `d` is prime. -/
theorem prime (n d : ℕ) (i : _root_.AbcTwoNinths.ExteriorE2.Support n d) : (_root_.AbcTwoNinths.ExteriorE2.base n d i).Prime := by
  rcases Finset.mem_union.mp i.property with hi | hi <;> exact Nat.prime_of_mem_primeFactors hi
/-- The vec. This is used in the proof of Proposition 4.1 of the paper. -/
def vec (n d : ℕ) : _root_.AbcTwoNinths.ExteriorE2.Exponents (_root_.AbcTwoNinths.ExteriorE2.Support n d) :=
  Multiplicative.ofAdd fun i => (n.factorization i : ℤ) - d.factorization i

private theorem factor {k : ℕ} (hk : k ≠ 0) (s : Finset ℕ) (hs : k.primeFactors ⊆ s) :
    (∏ i : s, (i.val ^ k.factorization i)) = k := by
  rw [Finset.prod_coe_sort s (fun q : ℕ => q ^ k.factorization q),
    ← Finset.prod_subset hs, ← Nat.prod_primeFactors_pow_factorization hk]
  intro q _ hq
  have hz : k.factorization q = 0 := by
    by_contra hh
    exact hq (Finsupp.mem_support_iff.mpr hh)
  simp [hz]

private theorem common {K : Type*} [Field K] {n d : ℕ}
    (hn : n ≠ 0) (hd : d ≠ 0) (b : _root_.AbcTwoNinths.ExteriorE2.Support n d → Kˣ)
    (hb : ∀ i, (b i : K) = (_root_.AbcTwoNinths.ExteriorE2.base n d i : K)) :
    (_root_.AbcTwoNinths.ExteriorE2.eval b (_root_.AbcTwoNinths.ExteriorE2.vec n d) : K) * (d : K) = n := by
  classical
  have prodK (k : ℕ) (hk : k ≠ 0) (hs : k.primeFactors ⊆ n.primeFactors ∪ d.primeFactors) :
      ((∏ i : _root_.AbcTwoNinths.ExteriorE2.Support n d, b i ^ k.factorization i : Kˣ) : K) = k := by
    simpa only [Units.coe_prod, Units.val_pow_eq_pow_val, hb, _root_.AbcTwoNinths.ExteriorE2.base, Nat.cast_prod,
      Nat.cast_pow] using congrArg (fun z : ℕ => (z : K)) (factor hk _ hs)
  have eqU : _root_.AbcTwoNinths.ExteriorE2.eval b (_root_.AbcTwoNinths.ExteriorE2.vec n d) * (∏ i, b i ^ d.factorization i) =
      ∏ i, b i ^ n.factorization i := by
    change (∏ i, b i ^ ((n.factorization i : ℤ) - d.factorization i)) * _ = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp [zpow_sub]
  simpa only [Units.val_mul, prodK n hn Finset.subset_union_left,
    prodK d hd Finset.subset_union_right] using congrArg Units.val eqU

/--
The rational monomial of the prime exponent difference of `n` and `d` is `n / d` when both
are nonzero.
-/
theorem ratEval {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    (_root_.AbcTwoNinths.ExteriorE2.monomial (_root_.AbcTwoNinths.ExteriorE2.base n d) (_root_.AbcTwoNinths.ExteriorE2.prime n d) (_root_.AbcTwoNinths.ExteriorE2.vec n d) : ℚ) = n / d := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hd)).2
  exact common hn hd (_root_.AbcTwoNinths.ExteriorE2.ratUnit (_root_.AbcTwoNinths.ExteriorE2.base n d) (_root_.AbcTwoNinths.ExteriorE2.prime n d)) (fun _ => rfl)

/--
For nonzero `n` and `d` , evaluating their factorization-difference vector in the residue
units and multiplying by `d` gives `n` modulo the prime `p` outside the support.
-/
theorem resEval {p n d : ℕ} [Fact p.Prime] (hn : n ≠ 0) (hd : d ≠ 0)
    (avoid : ∀ i, p ≠ _root_.AbcTwoNinths.ExteriorE2.base n d i) :
    (_root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base n d) (_root_.AbcTwoNinths.ExteriorE2.prime n d) avoid (_root_.AbcTwoNinths.ExteriorE2.vec n d) : ZMod p) * d = n :=
  common hn hd (_root_.AbcTwoNinths.ExteriorE2.residueUnit (_root_.AbcTwoNinths.ExteriorE2.base n d) (_root_.AbcTwoNinths.ExteriorE2.prime n d) avoid) (fun _ => rfl)

end
end

end AbcTwoNinths.ExteriorE2
