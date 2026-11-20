/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.CommonPowers

/-!
# Valuation Gcd

The module relates divisibility of the quotient valuation gcd to common powers and excludes large gcd in a real-contact failure. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quotientGcdLtOfNotE1`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
The gcd of the absolute prime-valuation differences of the two coordinates b and c. This is used in the proof of Proposition 3.1 of the paper.
-/
def quotientGcd (t : _root_.AbcTwoNinths.Basic.Triple) : ℕ := (_root_.AbcTwoNinths.Basic.supp t).gcd fun p => (_root_.AbcTwoNinths.Basic.coeff t p).natAbs

private theorem coprimeBc (t : _root_.AbcTwoNinths.Basic.Triple) : t.b.Coprime t.c := by
  rw [← t.add, Nat.coprime_add_self_right]
  exact t.coprime.symm

private theorem valuationCases (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) :
    t.b.factorization p = 0 ∨ t.c.factorization p = 0 := by
  by_cases hp : p.Prime
  · by_cases hb : p ∣ t.b
    · right
      apply (Nat.factorization_eq_zero_iff _ _).2
      right; left
      intro hc
      have h := Nat.dvd_gcd hb hc
      rw [(coprimeBc t).gcd_eq_one] at h
      exact hp.not_dvd_one h
    · exact Or.inl ((Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hb)))
  · exact Or.inl (Nat.factorization_eq_zero_of_not_prime _ hp)

private theorem absCoeff (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) :
    (_root_.AbcTwoNinths.Basic.coeff t p).natAbs = t.b.factorization p + t.c.factorization p := by
  rcases valuationCases t p with h | h <;> simp [_root_.AbcTwoNinths.Basic.coeff, h]

private theorem powerIffValuations (a g : ℕ) (ha : a ≠ 0) :
    (∃ A : ℕ, a = A ^ g) ↔ ∀ p ∈ a.primeFactors, g ∣ a.factorization p := by
  constructor
  · rintro ⟨A, rfl⟩ p _
    rw [Nat.factorization_pow]
    exact dvd_mul_right _ _
  · intro h
    refine ⟨∏ p ∈ a.primeFactors, p ^ (a.factorization p / g), ?_⟩
    rw [← Finset.prod_pow]
    calc
      a = ∏ p ∈ a.primeFactors, p ^ a.factorization p :=
        Nat.prod_primeFactors_pow_factorization ha
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_mul, Nat.div_mul_cancel (h p hp)]

/--
An exponent divides the valuation-difference gcd exactly when b and c are both powers with that exponent.
-/
theorem dvdQuotientGcdIffPower (t : _root_.AbcTwoNinths.Basic.Triple) (g : ℕ) :
    g ∣ _root_.AbcTwoNinths.ExteriorE1.quotientGcd t ↔ ∃ B C : ℕ, t.b = B ^ g ∧ t.c = C ^ g := by
  have hc : t.c ≠ 0 := by have := t.add; have := t.apos; omega
  unfold _root_.AbcTwoNinths.ExteriorE1.quotientGcd
  rw [Finset.dvd_gcd_iff]
  constructor
  · intro h
    obtain ⟨B, hB⟩ := (powerIffValuations t.b g t.bpos.ne').2 (by
      intro p hp
      have hs := h p (Finset.mem_union_left _ hp)
      rw [absCoeff] at hs
      rcases valuationCases t p with hz | hz
      · rw [hz]; exact dvd_zero _
      · rwa [hz, add_zero] at hs)
    obtain ⟨C, hC⟩ := (powerIffValuations t.c g hc).2 (by
      intro p hp
      have hs := h p (Finset.mem_union_right _ hp)
      rw [absCoeff] at hs
      rcases valuationCases t p with hz | hz
      · rwa [hz, zero_add] at hs
      · rw [hz]; exact dvd_zero _)
    exact ⟨B, C, hB, hC⟩
  · rintro ⟨B, C, hB, hC⟩ p _
    rw [absCoeff, hB, hC, Nat.factorization_pow, Nat.factorization_pow]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- The valuation-difference gcd of a positive primitive triple is positive. -/
theorem quotientGcdPos (t : _root_.AbcTwoNinths.Basic.Triple) : 0 < _root_.AbcTwoNinths.ExteriorE1.quotientGcd t := by
  apply Nat.pos_of_ne_zero
  intro h
  obtain ⟨_, C, _, hC⟩ := (_root_.AbcTwoNinths.ExteriorE1.dvdQuotientGcdIffPower t 0).1 (by simp [h])
  simp at hC
  have := t.apos
  have := t.bpos
  have := t.add
  omega

/-- Real contact holds when the valuation-difference gcd times the margin is at least one. -/
theorem e1OfQuotientGcd (t : _root_.AbcTwoNinths.Basic.Triple) (κ : ℝ)
    (hk : 1 ≤ (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * κ) : _root_.AbcTwoNinths.Statement.RealContactBound κ t := by
  obtain ⟨B,C,hB,hC⟩ := (_root_.AbcTwoNinths.ExteriorE1.dvdQuotientGcdIffPower t (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t)).1 (dvd_refl _)
  have hg := _root_.AbcTwoNinths.ExteriorE1.quotientGcdPos t
  obtain ⟨n, hn⟩ : ∃ n : ℕ, _root_.AbcTwoNinths.ExteriorE1.quotientGcd t = n + 1 := ⟨_root_.AbcTwoNinths.ExteriorE1.quotientGcd t - 1, by omega⟩
  rw [hn] at hB hC hk
  have hBC : B < C := by
    by_contra! h
    have hpow := Nat.pow_le_pow_left h (n+1)
    rw [← hB, ← hC] at hpow
    have := t.apos
    have := t.add
    omega
  push_cast at hk
  exact _root_.AbcTwoNinths.ExteriorE1.e1OfLargeCommonPower t κ B C n hBC hB hC hk

/--
Failure of real contact at a positive margin bounds the valuation-difference gcd by its reciprocal. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem quotientGcdLtOfNotE1 (t : _root_.AbcTwoNinths.Basic.Triple) (κ : ℝ) (hk : 0 < κ)
    (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) : (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) < 1 / κ := by
  apply (lt_div_iff₀ hk).2
  exact lt_of_not_ge fun h => hf (_root_.AbcTwoNinths.ExteriorE1.e1OfQuotientGcd t κ h)

end

end AbcTwoNinths.ExteriorE1
