/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ValuationGcd

/-!
# Low Rank Contact

An ordered primitive triple supported on at most two primes is either `(1, 1, 2)` or has its two
larger entries equal to powers of distinct primes. An ordered triple supported on at most one prime
fails the high-triple inequality. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.rankLeTwoShapes`
* `AbcTwoNinths.ExteriorE1.rankOneClosed`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



private theorem primeMem {a : ℕ} (h : 1 < a) : a.primeFactors.Nonempty := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show a ≠ 1 by omega)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩⟩

/--
If at most two primes divide the product of the two larger sides, the triple is (1,1,2) or those sides are positive powers of distinct primes.
-/
theorem rankLeTwoShapes (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hs : (_root_.AbcTwoNinths.Basic.supp t).card ≤ 2) :
    (t.a = 1 ∧ t.b = 1 ∧ t.c = 2) ∨
    ∃ p q m n : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < m ∧ 0 < n ∧
      t.b = p ^ m ∧ t.c = q ^ n := by
  have ha := t.apos
  have hb := t.bpos
  have ht := t.add
  by_cases hb1 : t.b = 1
  · exact Or.inl ⟨by omega, hb1, by omega⟩
  have hd : Disjoint t.b.primeFactors t.c.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hcop : t.b.Coprime t.c := by
      rw [← ht, Nat.coprime_add_self_right]
      exact t.coprime.symm
    have h := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
    rw [hcop.gcd_eq_one] at h
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one h
  have hbc := (primeMem (show 1 < t.b by omega)).card_pos
  have hcc := (primeMem (show 1 < t.c by omega)).card_pos
  unfold _root_.AbcTwoNinths.Basic.supp at hs
  rw [Finset.card_union_of_disjoint hd] at hs
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show t.b.primeFactors.card = 1 by omega)
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (show t.c.primeFactors.card = 1 by omega)
  have hp' : p ∈ t.b.primeFactors := by simp [hp]
  have hq' : q ∈ t.c.primeFactors := by simp [hq]
  have hpq : p ≠ q := by rintro rfl; exact Finset.disjoint_left.mp hd hp' hq'
  have hB := Nat.prod_primeFactors_pow_factorization hb.ne'
  have hC := Nat.prod_primeFactors_pow_factorization (show t.c ≠ 0 by omega)
  rw [hp, Finset.prod_singleton] at hB
  rw [hq, Finset.prod_singleton] at hC
  exact Or.inr ⟨p, q, _, _, Nat.prime_of_mem_primeFactors hp',
    Nat.prime_of_mem_primeFactors hq', hpq, by
      by_contra! z
      rw [Nat.eq_zero_of_le_zero z, pow_zero] at hB
      contradiction, by
      by_contra! z
      rw [Nat.eq_zero_of_le_zero z, pow_zero] at hC
      omega, hB, hC⟩

/--
A triple with largest side two fails the high condition at threshold zero for every admissible eta.
-/
theorem notHighOfTwo (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (t : _root_.AbcTwoNinths.Basic.Triple)
    (hc : t.c = 2) : ¬ _root_.AbcTwoNinths.Statement.High η 0 t := by
  intro hh
  have hηR : (η : ℝ) < 1 / 9 := by
    have h := Rat.cast_lt (K := ℝ).mpr hη.2
    simpa using h
  have hr : 0 ≤ _root_.AbcTwoNinths.Statement.highRate η := by unfold _root_.AbcTwoNinths.Statement.highRate; linarith
  have he := Real.exp_le_exp.mpr (mul_nonneg hr hh.1)
  rw [Real.exp_zero] at he
  have h := he.trans hh.2
  rw [_root_.AbcTwoNinths.Basic.Triple.logHeight, hc, Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

/--
An ordered triple with at most one prime dividing the product of its two larger sides fails the high condition at threshold zero for every admissible eta. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem rankOneClosed (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (t : _root_.AbcTwoNinths.Basic.Triple)
    (hab : t.a ≤ t.b) (hs : (_root_.AbcTwoNinths.Basic.supp t).card ≤ 1) : ¬ _root_.AbcTwoNinths.Statement.High η 0 t := by
  rcases _root_.AbcTwoNinths.ExteriorE1.rankLeTwoShapes t hab (by omega) with h | ⟨p,q,m,n,hp,hq,hne,hm,hn,hb,hc⟩
  · exact _root_.AbcTwoNinths.ExteriorE1.notHighOfTwo η hη t h.2.2
  · unfold _root_.AbcTwoNinths.Basic.supp at hs
    rw [hb, hc, Nat.primeFactors_prime_pow hm.ne' hp, Nat.primeFactors_prime_pow hn.ne' hq] at hs
    simp [hne] at hs

end

end AbcTwoNinths.ExteriorE1
