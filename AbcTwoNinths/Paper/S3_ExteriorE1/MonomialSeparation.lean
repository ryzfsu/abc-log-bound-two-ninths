/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.MonomialOrientation
public import AbcTwoNinths.Paper.S3_ExteriorE1.PrimitiveLineExponents

/-!
# Monomial Separation

The module lower-bounds the separation of distinct rational monomial values. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.monomialSeparation`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- For a rational prime monomial greater than one, its logarithm lies between `exp (-L)`
and `L`, where its logarithmic height `L` is at least `1 / 2`. -/
theorem monomialSeparation {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (e : ι → ℤ)
    (he : 1 < _root_.AbcTwoNinths.PolyCap.prodMonomial p e) :
    let L := _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial p e)
    (1 : ℝ) / 2 ≤ L ∧ Real.exp (-L) ≤ Real.log (_root_.AbcTwoNinths.PolyCap.prodMonomial p e : ℝ) ∧
      Real.log (_root_.AbcTwoNinths.PolyCap.prodMonomial p e : ℝ) ≤ L := by
  obtain ⟨hP, hQ, _, heq, hnum, hden⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime p hp hinj e
  let P := _root_.AbcTwoNinths.PolyCap.posPartNat p e
  let Q := _root_.AbcTwoNinths.PolyCap.negPartNat p e
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hltq : (Q : ℚ) < P := by
    rw [heq] at he
    exact (one_lt_div hQq).mp he
  have hlt : Q < P := by exact_mod_cast hltq
  have hL : _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial p e) = Real.log (P : ℝ) := by
    rw [_root_.AbcTwoNinths.ExteriorE1.rationalLogHeight, hnum, hden, max_eq_left hlt.le]
  have hex : (_root_.AbcTwoNinths.PolyCap.prodMonomial p e : ℝ) = (P : ℝ) / Q := by
    rw [heq, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hP2 : (2 : ℝ) ≤ P := by
    exact_mod_cast (show 2 ≤ P by omega)
  dsimp only
  rw [hL, hex]
  refine ⟨?_, _root_.AbcTwoNinths.ExteriorE1.rationalSeparation hQ hlt, ?_⟩
  · exact (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hP2)
  · rw [Real.log_div hPr.ne' hQr.ne']
    linarith [Real.log_nonneg hQ1]

end

end AbcTwoNinths.ExteriorE1
