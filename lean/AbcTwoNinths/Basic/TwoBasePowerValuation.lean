/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Tactic

/-!
# Two Base Power Valuation

The module relates the local depth of two powers to the product of their exponent and valuation data.

## Main results
* `AbcTwoNinths.Basic.twoBaseDepthProduct`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
For a principal unit pair satisfying the dyadic congruence, a modulus power dividing the difference of positive powers divides the base difference times the exponent.
-/
theorem twoBaseDepthProduct {B m A D g : ℕ}
    (hB : B ≠ 0) (hDA : D < A) (hg : g ≠ 0)
    (hunit : A.Coprime B) (hprincipal : B ∣ A - D)
    (hdyadic : 2 ∣ B → 4 ∣ A - D)
    (hdepth : B ^ m ∣ A ^ g - D ^ g) :
    B ^ m ∣ (A - D) * g := by
  have hpow : D ^ g < A ^ g := Nat.pow_lt_pow_left hDA hg
  have hAD : A - D ≠ 0 := by omega
  have hdiff : A ^ g - D ^ g ≠ 0 := by omega
  have hBm : B ^ m ≠ 0 := pow_ne_zero _ hB
  apply (Nat.factorization_le_iff_dvd hBm (mul_ne_zero hAD hg)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpb : p ∣ B
    · have hpa : ¬ p ∣ A := fun h => hp.not_dvd_one (by
        simpa [hunit.gcd_eq_one] using Nat.dvd_gcd h hpb)
      let : Fact p.Prime := ⟨hp⟩
      have hval : padicValNat p (A ^ g - D ^ g) =
          padicValNat p (A - D) + padicValNat p g := by
        by_cases h2 : p = 2
        · subst p
          have h4 : (4 : ℤ) ∣ (A : ℤ) - (D : ℤ) := by
            rw [← Int.ofNat_sub hDA.le]
            exact_mod_cast hdyadic hpb
          have hZ := Int.two_pow_sub_pow' (x := (A : ℤ)) (y := (D : ℤ)) g
            h4 (by exact_mod_cast hpa)
          have hpcast : ((A ^ g - D ^ g : ℕ) : ℤ) = (A : ℤ) ^ g - (D : ℤ) ^ g := by
            rw [Int.ofNat_sub hpow.le]
            push_cast
            rfl
          rw [← hpcast, ← Int.ofNat_sub hDA.le] at hZ
          change emultiplicity ((2 : ℕ) : ℤ) ((A ^ g - D ^ g : ℕ) : ℤ) =
            emultiplicity ((2 : ℕ) : ℤ) ((A - D : ℕ) : ℤ) +
              emultiplicity ((2 : ℕ) : ℤ) (g : ℤ) at hZ
          simp only [Int.natCast_emultiplicity] at hZ
          rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add,
            padicValNat_eq_emultiplicity hdiff, padicValNat_eq_emultiplicity hAD,
            padicValNat_eq_emultiplicity hg]
          exact hZ
        · exact padicValNat.pow_sub_pow (hp.odd_of_ne_two h2) hDA
            (hpb.trans hprincipal) hpa hg
      have hh := (Nat.factorization_le_iff_dvd hBm hdiff).2 hdepth p
      rw [Nat.factorization_def (A ^ g - D ^ g) hp, hval] at hh
      simpa [Nat.factorization_mul hAD hg, Nat.factorization_def _ hp] using hh
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hpb (hp.dvd_of_dvd_pow h))]
      exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end

end AbcTwoNinths.Basic
