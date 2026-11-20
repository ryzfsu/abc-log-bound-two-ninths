/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactTail
public import AbcTwoNinths.Paper.S3_ExteriorE1.MaximalLogarithmicPivot

/-!
# Quotient Height

The module expresses the height of the source quotient as a signed logarithmic sum over its support. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quotientSignedHeight`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




private theorem valuationZero (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) :
    t.b.factorization p = 0 ∨ t.c.factorization p = 0 := by
  have hcop : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact t.coprime.symm
  by_cases hp : p.Prime
  · by_cases hb : p ∣ t.b
    · right
      apply (Nat.factorization_eq_zero_iff _ _).2
      right; left
      intro hc
      have h := Nat.dvd_gcd hb hc
      rw [hcop.gcd_eq_one] at h
      exact hp.not_dvd_one h
    · exact Or.inl ((Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hb)))
  · exact Or.inl (Nat.factorization_eq_zero_of_not_prime _ hp)

/--
The sum of prime logarithms with their factorization multiplicities over any support containing the prime factors equals the logarithm of the integer.
-/
theorem sumLogOnSupport (S : Finset ℕ) (n : ℕ)
    (hs : n.primeFactors ⊆ S) :
    (∑ i : S, Real.log (i.val : ℝ) * (n.factorization i.val : ℝ)) =
      Real.log (n : ℝ) := by
  change (∑ i ∈ S.attach, Real.log (i.val : ℝ) * (n.factorization i.val : ℝ)) = _
  rw [Finset.sum_attach S (fun p => Real.log (p : ℝ) * (n.factorization p : ℝ))]
  rw [Real.log_nat_eq_sum_factorization]
  change _ = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log (p : ℝ)
  symm
  calc
    _ = ∑ p ∈ n.factorization.support, Real.log (p : ℝ) * (n.factorization p : ℝ) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by
      apply Finset.sum_subset (show n.factorization.support ⊆ S from hs)
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp, Nat.cast_zero, mul_zero]

/--
The height of the triple equals the signed height of the exponent vector of the ratio of its last coordinate to its second coordinate. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem quotientSignedHeight (t : _root_.AbcTwoNinths.Basic.Triple) :
    t.logHeight = _root_.AbcTwoNinths.ExteriorE1.signedHeight (fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)) (_root_.AbcTwoNinths.ExteriorE1.quotientVec t) := by
  have hp (i : _root_.AbcTwoNinths.Basic.supp t) : max (_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ) 0 = (t.c.factorization i.val : ℝ) := by
    simp only [_root_.AbcTwoNinths.ExteriorE1.quotientVec, Int.cast_sub, Int.cast_natCast]
    rcases valuationZero t i.val with h | h <;> simp [h]
  have hn (i : _root_.AbcTwoNinths.Basic.supp t) : max (-(_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ)) 0 = (t.b.factorization i.val : ℝ) := by
    simp only [_root_.AbcTwoNinths.ExteriorE1.quotientVec, Int.cast_sub, Int.cast_natCast, neg_sub]
    rcases valuationZero t i.val with h | h <;> simp [h]
  unfold _root_.AbcTwoNinths.ExteriorE1.signedHeight
  simp only [hp, hn]
  rw [_root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.c Finset.subset_union_right,
    _root_.AbcTwoNinths.ExteriorE1.sumLogOnSupport (_root_.AbcTwoNinths.Basic.supp t) t.b Finset.subset_union_left]
  have hbc : t.b ≤ t.c := by have := t.add; omega
  rw [max_eq_left (Real.log_le_log (by exact_mod_cast t.bpos) (by exact_mod_cast hbc))]
  rfl

end

end AbcTwoNinths.ExteriorE1
