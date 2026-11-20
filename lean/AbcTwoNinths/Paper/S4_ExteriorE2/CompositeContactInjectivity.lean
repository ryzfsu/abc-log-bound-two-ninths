/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeModulusLogarithmBound
public import AbcTwoNinths.Basic.InterpolationDeterminantDepth
public import AbcTwoNinths.Basic.LocalDepthHeightComparison
public import AbcTwoNinths.Basic.DeterminantLogBound
public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Composite Contact Injectivity

The module uses nonvanishing on an injective grid to compare composite contact depth with minor height. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeInjective`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open Real

/--
Injective rectangle nodes and congruent unit powers modulo a power of the base give the logarithmic bound for a minor with 36 columns of exponents per level. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeInjective {B J c d R S R' S' : ℕ} (hB : 1 < B)
    (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (ha : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) a.val = 1)
    (hb : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) b.val = 1)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((J+1)*36)) (a.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B ((J+1)*36)) (b.val ^ d))
    (hi : ∀ m n : ℤ, a.val.val ^ m * b.val.val ^ n = 1 → m = 0 ∧ n = 0)
    (hc : c.Coprime d) (hJ : 0 < J)
    (h₁ : 36 ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S))
    (h₂ : 36*J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S'))
    (hz : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') c d))
    (W : ℝ) (hM : 0 < (R+R')*d+(S+S')*c)
    (hW : ((R+R' : ℕ) : ℝ) * log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ)) +
      ((S+S' : ℕ) : ℝ) * log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ)) ≤
      2*W*log B) :
    ((J : ℝ)+1)*35 <
      2*log (((J+1)*36 : ℕ) : ℝ)/log B +
      (J : ℝ)*(2+log (((((R+R')*d+(S+S')*c : ℕ) : ℝ))/J))/log B + 36*W := by
  classical
  have ha0 : a.val.val ≠ 0 := (Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom a).ne_zero
  have hb0 : b.val.val ≠ 0 := (Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom b).ne_zero
  obtain ⟨f,hf⟩ := _root_.AbcTwoNinths.Basic.rectangleBinomialMinor a.val.val b.val.val ha0 hb0 hi h₁ h₂ hz
  let r : _root_.AbcTwoNinths.Basic.Rows J 36 → ℕ := fun i => (f i).1.val
  let s : _root_.AbcTwoNinths.Basic.Rows J 36 → ℕ := fun i => (f i).2.val
  have hD : (_root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val
      (fun i : _root_.AbcTwoNinths.Basic.Rows J 36 => i.1.val) (fun i => i.2.val) r s c d).det ≠ 0 := by
    convert hf using 2
    apply Matrix.ext
    intro i j
    change (Nat.choose (r j*d+s j*c) i.1.val : ℚ) * a.val.val^(i.2.val*r j) *
      b.val.val^(i.2.val*s j) = (Nat.choose (r j*d+s j*c) i.1.val : ℚ) *
      (a.val.val^(r j)*b.val.val^(s j))^i.2.val
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc,
      mul_comm (r j) i.2.val, mul_comm (s j) i.2.val]
  have hr (i : _root_.AbcTwoNinths.Basic.Rows J 36) : r i ≤ R+R' := Nat.le_of_lt_succ (f i).1.isLt
  have hs (i : _root_.AbcTwoNinths.Basic.Rows J 36) : s i ≤ S+S' := Nat.le_of_lt_succ (f i).2.isLt
  have hlog := _root_.AbcTwoNinths.ExteriorE2.compositeLog36 hB hc a b ha hb hab r s hr hs hM hD
  apply _root_.AbcTwoNinths.Basic.archBridge36 J B _ W _ hJ (by exact_mod_cast hB)
    (by exact_mod_cast hM) ?_ hlog
  simpa only [Nat.cast_succ] using mul_le_mul_of_nonneg_left hW
    (show 0 ≤ ((J+1 : ℕ) : ℝ) * 324 by positivity)

end

end AbcTwoNinths.ExteriorE2
