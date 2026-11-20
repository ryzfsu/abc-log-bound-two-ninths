/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.WeightedValuationSelection

/-!
# Same Side Prime Selection

An odd prime dividing the larger summand or the sum of an ordered triple satisfies the same-side
condition. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.sameSidePrimeSelectionSameSideOfSelected`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section



/--
The same side same side prime selection. This is used in the proof of Proposition 2.1 of the paper.
-/
def SameSideSameSidePrimeSelection (t : _root_.AbcTwoNinths.Basic.Triple) (M p : ℕ) : Prop :=
  (M = t.b ∧ ¬ p ∣ t.a ∧ (t.c : ℚ) / t.a - 1 = (t.b : ℚ) / t.a) ∨
  (M = t.c ∧ ¬ p ∣ t.a ∧
    ((t.b : ℚ) / t.a)^2 - 1 =
      (((t.b : ℚ) - t.a) * t.c) / (t.a : ℚ)^2 ∧ ¬ p ∣ t.b - t.a)

/--
If an odd prime `p` divides `b` or `c` in an ordered triple, the corresponding factorization of
`c / a - 1` or `(b / a)² - 1` isolates that side as a factor with a `p`-adic unit cofactor.
-/
theorem sameSidePrimeSelectionSameSideOfSelected (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b)
    {M p : ℕ} (hM : M = t.b ∨ M = t.c) (hp : p.Prime) (hp2 : 2 < p)
    (hd : p ∣ M) : _root_.AbcTwoNinths.PolyCap.SameSideSameSidePrimeSelection t M p := by
  have hs := t.add
  have ha : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
  have hsQ : (t.a : ℚ) + (t.b : ℚ) = t.c := by exact_mod_cast hs
  have hcop (hpa : p ∣ t.a) (hpb : p ∣ t.b) : False := by
    have hg := Nat.dvd_gcd hpa hpb
    rw [t.coprime.gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  rcases hM with rfl | rfl
  · refine Or.inl ⟨rfl, fun h => hcop h hd, ?_⟩
    rw [← hsQ]
    field_simp
    ring
  · have hpa : ¬ p ∣ t.a := by
      intro h
      apply hcop h
      have hd' : p ∣ t.a + t.b := by rwa [hs]
      have hh := Nat.dvd_sub hd' h
      rwa [show t.a + t.b - t.a = t.b by omega] at hh
    have hdiff : ¬ p ∣ t.b - t.a := by
      intro h
      have hsum : p ∣ t.a + t.b := by rwa [hs]
      have htwice := Nat.dvd_sub hsum h
      have he : t.a + t.b - (t.b - t.a) = 2 * t.a := by omega
      rw [he] at htwice
      rcases hp.dvd_mul.mp htwice with htwo | hdiv
      · exact (not_le_of_gt hp2) (Nat.le_of_dvd (by decide) htwo)
      · exact hpa hdiv
    refine Or.inr ⟨rfl, hpa, ?_, hdiff⟩
    rw [← hsQ]
    field_simp
    ring

end

end AbcTwoNinths.PolyCap
