/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.SelectedDepth

/-!
# Valuation under powering

Computes the valuation of the powered selected-source difference using lifting the exponent. It
supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.selectedSourceDepthPower`
-/

@[expose] public section


namespace AbcTwoNinths.Selection



section

/--
The odd-prime loss on the actual source, given its signed rational root. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem selectedSourceDepthPower (t : _root_.AbcTwoNinths.Basic.Triple) {p g : ℕ} {N D : ℤ}
    (hp : p.Prime) (ho : Odd p)
    (hs : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    (hg : 0 < g) (hD : ¬ (p : ℤ) ∣ D) (hN : ¬ (p : ℤ) ∣ N)
    (hdiff : (p : ℤ) ∣ N - D) (hroot : N - D ≠ 0)
    (hpow : N ^ g - D ^ g ≠ 0)
    (hz : _root_.AbcTwoNinths.Statement.selectedSource t = ((N : ℚ) / (D : ℚ)) ^ g) :
    (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) =
      padicValRat p ((N : ℚ) / (D : ℚ) - 1) + (padicValNat p g : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hd0 : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast hd0
  have val (X Y : ℤ) (hx : X ≠ 0) (hy : Y ≠ 0) (hu : ¬ (p : ℤ) ∣ Y) :
      padicValRat p ((X : ℚ) / (Y : ℚ)) = (multiplicity (p : ℤ) X : ℤ) := by
    have hxq : (X : ℚ) ≠ 0 := by exact_mod_cast hx
    have hyq : (Y : ℚ) ≠ 0 := by exact_mod_cast hy
    rw [padicValRat.defn p (div_ne_zero hxq hyq) (Rat.intCast_div_eq_divInt X Y),
      multiplicity_eq_zero_of_not_dvd hu, Nat.cast_zero, sub_zero]
  have hL := Int.emultiplicity_pow_sub_pow hp ho hdiff hN g
  rw [(padicValRat.finite_int_prime_iff.mpr hpow).emultiplicity_eq_multiplicity,
    (padicValRat.finite_int_prime_iff.mpr hroot).emultiplicity_eq_multiplicity,
    ← padicValNat_eq_emultiplicity hg.ne',
    ← Nat.cast_add, Nat.cast_inj] at hL
  have hraw := (_root_.AbcTwoNinths.Selection.selectedSourceDepthOfMem t hs).2
  rw [hz, div_pow,
    show (N : ℚ) ^ g / (D : ℚ) ^ g - 1 = ((N ^ g - D ^ g : ℤ) : ℚ) /
      ((D ^ g : ℤ) : ℚ) by push_cast; field_simp,
    val _ _ hpow (pow_ne_zero _ hd0) (fun h => hD ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h))]
    at hraw
  rw [← hraw,
    show (N : ℚ) / (D : ℚ) - 1 = ((N - D : ℤ) : ℚ) / (D : ℚ) by push_cast; field_simp,
    val _ _ hroot hd0 hD, hL, Nat.cast_add]

end

end AbcTwoNinths.Selection
