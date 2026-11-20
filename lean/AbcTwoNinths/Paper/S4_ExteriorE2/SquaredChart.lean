/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.SourceFactors
public import AbcTwoNinths.Paper.S4_ExteriorE2.SquaredSource

/-!
# Squared Chart

The module gives signed exponent coordinates for the squared source ratio. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.squaredSourceChart`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
If `M` divides the chosen side, the squares of the two source numbers are the positive and
negative part products of an exponent vector supported on primes coprime to `M` .
-/
theorem squaredSourceChart (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) (M : ℕ)
    (hM : M ∣ _root_.AbcTwoNinths.Statement.sideValue t s) :
    let P := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2
    let D := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2
    let S := (P * D).primeFactors
    ∃ e : S → ℤ, _root_.AbcTwoNinths.PolyCap.posPartNat (fun p : S => (p : ℕ)) e = P ∧
      _root_.AbcTwoNinths.PolyCap.negPartNat (fun p : S => (p : ℕ)) e = D ∧
      ∀ p : S, (p : ℕ).Coprime M := by
  classical
  let P := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1
  let D := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2
  let S := (P ^ 2 * D ^ 2).primeFactors
  have hp : 0 < P ∧ 0 < D := by
    have hc : 0 < t.c := by rw [← t.add]; exact Nat.add_pos_left t.apos _
    cases s
    · exact ⟨hc, t.bpos⟩
    · exact ⟨hc, t.apos⟩
    · exact ⟨t.bpos, t.apos⟩
  have hx : P ^ 2 * D ^ 2 ≠ 0 := by obtain ⟨hp, hd⟩ := hp; positivity
  have hsP : (P ^ 2).primeFactors ⊆ S := Nat.primeFactors_mono (dvd_mul_right _ _) hx
  have hsD : (D ^ 2).primeFactors ⊆ S := Nat.primeFactors_mono (dvd_mul_left _ _) hx
  have hc := _root_.AbcTwoNinths.ExteriorE2.sourcePairCoprime t s
  have h2 : (P ^ 2).Coprime (D ^ 2) := (hc.1.pow_left 2).pow_right 2
  have hcm : (P ^ 2 * D ^ 2).Coprime M := by
    rw [← mul_pow]
    exact (hc.2.of_dvd_right hM).pow_left _
  let e := fun p : S => ((P ^ 2).factorization p : ℤ) - (D ^ 2).factorization p
  obtain ⟨h1,h2'⟩ := _root_.AbcTwoNinths.ExteriorE2.partsOfFactorDifference (pow_ne_zero 2 hp.1.ne')
    (pow_ne_zero 2 hp.2.ne') h2 S hsP hsD (fun _ h => Nat.prime_of_mem_primeFactors h)
  exact ⟨e,h1,h2',fun p => hcm.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)⟩

end

end AbcTwoNinths.ExteriorE2
