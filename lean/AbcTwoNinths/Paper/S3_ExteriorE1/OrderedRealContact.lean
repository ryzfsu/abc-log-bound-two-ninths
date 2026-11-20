/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusForm

/-!
# Ordered Real Contact

For an ordered triple, `log(c/b)` is positive, and its negative logarithm plus `log 2` bounds
`log(c/a)` . This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.contactOfOrdered`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
For an ordered triple, the positive contact logarithm of c/b bounds log(c/a) through its negative logarithm. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem contactOfOrdered (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) :
    0 < Real.log ((t.c : ℝ) / t.b) ∧
    Real.log ((t.c : ℝ) / t.a) ≤
      -Real.log (Real.log ((t.c : ℝ) / t.b)) + Real.log 2 := by
  have ha : (0 : ℝ) < t.a := by exact_mod_cast t.apos
  have hb : (0 : ℝ) < t.b := by exact_mod_cast t.bpos
  have hadd : (t.a : ℝ) + t.b = t.c := by exact_mod_cast t.add
  have habR : (t.a : ℝ) ≤ t.b := by exact_mod_cast hab
  have hc : (0 : ℝ) < t.c := by linarith
  have hratio : (1 : ℝ) < (t.c : ℝ) / t.b :=
    (lt_div_iff₀ hb).2 (by linarith)
  have hlog := Real.log_pos hratio
  have hsplit : (t.c : ℝ) / t.b - 1 = (t.a : ℝ) / t.b := by
    field_simp
    linarith
  have hupper := Real.log_le_sub_one_of_pos (div_pos hc hb)
  rw [hsplit] at hupper
  have hbnd : Real.log (t.c : ℝ) ≤ Real.log 2 + Real.log (t.b : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb.ne']
    exact Real.log_le_log hc (by linarith)
  have hlogupper := Real.log_le_log hlog hupper
  rw [Real.log_div ha.ne' hb.ne'] at hlogupper
  rw [Real.log_div hc.ne' ha.ne']
  exact ⟨hlog, by linarith⟩

end

end AbcTwoNinths.ExteriorE1
