/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Basic.Onset
public import AbcTwoNinths.Basic.SignedExponentRange

/-!
# Polynomial Height Bound

The module turns the rank-based bound into a uniform polynomial cap while tracking the effect of swapping the summands. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.polyCapOfMaster`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

noncomputable section

/-- The swap. This is used in the proof of Proposition 2.1 of the paper. -/
private def swap (t : _root_.AbcTwoNinths.Basic.Triple) : _root_.AbcTwoNinths.Basic.Triple :=
  ⟨t.b, t.a, t.c, t.bpos, t.apos, by simpa [add_comm] using t.add, t.coprime.symm⟩

private theorem swapRadical (t : _root_.AbcTwoNinths.Basic.Triple) : (swap t).radical = t.radical := by
  simp [swap, _root_.AbcTwoNinths.Basic.Triple.radical, mul_comm t.a t.b]

private theorem radicalPositive (t : _root_.AbcTwoNinths.Basic.Triple) : 0 < t.radical := by
  unfold _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical
  exact Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos

/--
Close both scalar ranges once the arithmetic supplies the master inequality. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem polyCapOfMaster
    (produce : ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → 2 < t.logHeight →
      t.logHeight ≤ 192 * (t.radical : ℝ) ^ (3 : ℕ) ∨
        ∃ s : ℝ, 1 < t.logRadical ∧ 0 ≤ s ∧ s ≤ 2 * t.logRadical ∧
          s ≤ 3 * t.logRadical / log t.logRadical ∧
          let Z := 1 + log (20 * t.logHeight)
          Z - (2 * s) * log Z ≤ 9 + 2 * log t.logRadical + t.logRadical + s * (24 + 3 * log t.logRadical)) :
    _root_.AbcTwoNinths.Statement.PolyCap := by
  let M : ℝ := 4 * exp 50
  let B : ℝ := 109 + 349 * exp 50
  let C : ℝ := max 192 (exp (2 * B + 2 * M * log (2 * M)))
  have h192 : 192 ≤ C := le_max_left _ _
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 192).trans h192
  have ordered (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b) : _root_.AbcTwoNinths.Statement.PolynomialHeightBound C 20 t := by
    unfold _root_.AbcTwoNinths.Statement.PolynomialHeightBound
    have hR : 0 < (t.radical : ℝ) := by exact_mod_cast radicalPositive t
    have hR1 : 1 ≤ (t.radical : ℝ) := by exact_mod_cast (radicalPositive t)
    have hpow : 1 ≤ (t.radical : ℝ) ^ (20 : ℝ) := one_le_rpow hR1 (by norm_num)
    have hmul : C ≤ C * (t.radical : ℝ) ^ (20 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hpow hC
    by_cases hH : 2 < t.logHeight
    · rcases produce t hord hH with hc | ⟨s, hW1, hs, hsW, hsupp, hmaster⟩
      · have hpow3 : (t.radical : ℝ) ^ (3 : ℕ) ≤ (t.radical : ℝ) ^ (20 : ℝ) := by
          rw [← Real.rpow_natCast]
          exact rpow_le_rpow_of_exponent_le hR1 (by norm_num)
        exact hc.trans (mul_le_mul h192 hpow3 (by positivity) hC)
      · let Z := 1 + log (20 * t.logHeight)
        change Z - (2 * s) * log Z ≤ _ at hmaster
        have hpos : 0 < t.logHeight := by linarith
        have hpos20 : 0 < 20 * t.logHeight := by positivity
        have hZ : 1 ≤ Z := by
          dsimp [Z]
          linarith [log_nonneg (show 1 ≤ 20 * t.logHeight by linarith)]
        have hHZ : t.logHeight ≤ exp Z := by
          dsimp [Z]
          rw [exp_add, exp_log hpos20]
          nlinarith [add_one_le_exp (1 : ℝ)]
        by_cases htail : exp 50 ≤ t.logRadical
        · have hx : exp 50 / 3 ≤ t.thirdLogRadical := by unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical; linarith
          have heq : 3 * t.thirdLogRadical = t.logRadical := by unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical; ring
          have htailZ := _root_.AbcTwoNinths.Basic.eventualPolynomialCap hx hs
            (by simpa only [heq] using hsupp) (by simpa only [heq] using hmaster)
          have hZW : Z ≤ 20 * t.logRadical := by linarith
          have hcap := hHZ.trans (exp_le_exp.mpr hZW)
          change t.logHeight ≤ exp (20 * log (t.radical : ℝ)) at hcap
          rw [mul_comm, ← rpow_def_of_pos hR] at hcap
          refine hcap.trans ?_
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (show 1 ≤ C by linarith) (show 0 ≤ (t.radical : ℝ) ^ (20 : ℝ) by positivity)
        · have hW : 0 < t.logRadical := by linarith
          have hlog : log t.logRadical ≤ 50 := (log_le_iff_le_exp hW).2 (le_of_not_ge htail)
          have hWindow : t.logRadical ≤ exp 50 := le_of_not_ge htail
          have hm : 2 * s ≤ 4 * exp 50 := by linarith
          have hb : 9 + 2 * log t.logRadical + t.logRadical + s * (24 + 3 * log t.logRadical) ≤
              109 + 349 * exp 50 := by
            have hterm := mul_le_mul_of_nonneg_left
              (show 24 + 3 * log t.logRadical ≤ 174 by linarith) hs
            linarith
          have hbZ := _root_.AbcTwoNinths.Basic.polynomialBoundOnFiniteWindow hZ hm hb hmaster
          exact hHZ.trans ((exp_le_exp.mpr hbZ).trans ((le_max_right _ _).trans hmul))
    · exact (le_of_not_gt hH).trans ((by norm_num : (2 : ℝ) ≤ 192).trans (h192.trans hmul))
  refine ⟨C, 20, (by norm_num : (0 : ℝ) < 192).trans_le h192, by norm_num, ?_⟩
  intro t
  by_cases h : t.a ≤ t.b
  · exact ordered t h
  · have hs := ordered (swap t) (by change t.b ≤ t.a; omega)
    simpa only [_root_.AbcTwoNinths.Statement.PolynomialHeightBound, swapRadical, show (swap t).logHeight = t.logHeight from rfl] using hs

end
end

end AbcTwoNinths.PolyCap
