/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Paper.S1_Statement.RadicalScaleAndTail

/-!
# Polynomial Bound Tail

The polynomial height cap and the common tail exclusion give the stated exponent bound in
Section 8 of the paper.

## Main results
* `AbcTwoNinths.Assembly.twoNinthsOfPolycapAndTail`
-/

@[expose] public section

namespace AbcTwoNinths.Assembly

section

/-- The polynomial cap bounds triples below the radical cutoff and the tail exclusion bounds
those above it, giving the uniform `2 / 9 + ε` exponent for each positive `ε`. -/
theorem twoNinthsOfPolycapAndTail (cap : _root_.AbcTwoNinths.Statement.PolyCap)
    (tail : _root_.AbcTwoNinths.Statement.CommonTailExclusion) : twoNinthsStatement := by
  intro ε hε
  obtain ⟨e, -, -, hη, hηtop, hexp⟩ := _root_.AbcTwoNinths.Statement.realEpsilonRationalParameters hε
  obtain ⟨onset, htail⟩ := tail (_root_.AbcTwoNinths.Statement.etaOf e) hη hηtop
  obtain ⟨C, k, hC, hk, hcap⟩ := cap
  let B := C * (Real.exp (3 * onset)) ^ k
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro a b c ht
  let R : ℝ := radNat (a * b * c)
  let x := _root_.AbcTwoNinths.Statement.radicalScale a b c
  let η : ℝ := _root_.AbcTwoNinths.Statement.etaOf e
  have hR : 1 ≤ R := _root_.AbcTwoNinths.Statement.radicalGeOne _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  by_cases hx : x ≤ onset
  · let t : _root_.AbcTwoNinths.Basic.Triple := ⟨a, b, c, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    have hb : Real.log (c : ℝ) ≤ C * R ^ k := hcap t
    have hlog : Real.log R ≤ 3 * onset := by
      change Real.log R / 3 ≤ onset at hx
      linarith
    have hwindow : R ≤ Real.exp (3 * onset) := (Real.log_le_iff_le_exp hRp).mp hlog
    have hB : Real.log (c : ℝ) ≤ B :=
      hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hRp.le hwindow hk) hC.le)
    exact hB.trans ((le_max_right 1 B).trans
      (le_mul_of_one_le_right (zero_le_one.trans (le_max_left 1 B))
        (Real.one_le_rpow hR (by positivity))))
  · have hsmall : Real.log (c : ℝ) < Real.exp ((1 - 3 * η) * x) :=
      lt_of_not_ge (htail a b c ht (le_of_lt (lt_of_not_ge hx)))
    have hpower : Real.exp ((1 - 3 * η) * x) = R ^ (1/3 - η) := by
      rw [Real.rpow_def_of_pos hRp]
      congr 1
      change (1 - 3 * η) * (Real.log R / 3) = _
      ring
    have hb := Real.rpow_le_rpow_of_exponent_le hR hexp.le
    exact (hsmall.le.trans (hpower.le.trans hb)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hRp.le _) (le_max_left 1 B))

end

end AbcTwoNinths.Assembly
