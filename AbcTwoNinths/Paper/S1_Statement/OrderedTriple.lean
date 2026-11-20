/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Side Selection and Admissible Parameters

The least-radical side determines the rational quotient used in the local analysis. The section
also defines admissible parameters and the polynomial height, real contact, and small-prime mass
conditions. This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.minRadicalSideSpec`
* `AbcTwoNinths.Statement.selectedSource`
* `AbcTwoNinths.Statement.High`
* `AbcTwoNinths.Statement.FixedMarginExterior`
-/

@[expose] public section

namespace AbcTwoNinths.Statement

section

noncomputable section



/--
A side of a triple is one of a, b or c. This is used in the proof of Theorem 1.1 of the paper.
-/
inductive Side where
  | a | b | c
  deriving DecidableEq

/--
Read the positive integer on the given side. This is used in the proof of Theorem 1.1 of the paper.
-/
def sideValue (t : _root_.AbcTwoNinths.Basic.Triple) : _root_.AbcTwoNinths.Statement.Side → ℕ
  | .a => t.a
  | .b => t.b
  | .c => t.c

/--
Take the radical of the integer on the given side. This is used in the proof of Theorem 1.1 of the paper.
-/
def sideRadical (t : _root_.AbcTwoNinths.Basic.Triple) (i : _root_.AbcTwoNinths.Statement.Side) : ℕ := _root_.AbcTwoNinths.Basic.radical (_root_.AbcTwoNinths.Statement.sideValue t i)

/--
Select the first side of least radical in the order a, b, c. This is used in the proof of Theorem 1.1 of the paper.
-/
def minRadicalSide (t : _root_.AbcTwoNinths.Basic.Triple) : _root_.AbcTwoNinths.Statement.Side :=
  if _root_.AbcTwoNinths.Statement.sideRadical t .a ≤ _root_.AbcTwoNinths.Statement.sideRadical t .b ∧ _root_.AbcTwoNinths.Statement.sideRadical t .a ≤ _root_.AbcTwoNinths.Statement.sideRadical t .c then .a
  else if _root_.AbcTwoNinths.Statement.sideRadical t .b ≤ _root_.AbcTwoNinths.Statement.sideRadical t .c then .b
  else .c

/--
The radical of the selected side is at most that of any side. This is used in the proof of Theorem 1.1 of the paper.
-/
theorem minRadicalSideSpec (t : _root_.AbcTwoNinths.Basic.Triple) (i : _root_.AbcTwoNinths.Statement.Side) :
    _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) ≤ _root_.AbcTwoNinths.Statement.sideRadical t i := by
  cases i <;> unfold _root_.AbcTwoNinths.Statement.minRadicalSide <;> split
  all_goals first | (rename_i h; exact h.1) | (rename_i h; exact h.2) | exact le_rfl | skip
  all_goals split <;> first | exact le_rfl | omega

/--
For the selected side a, b or c, the rational number z equals c/b, c/a or -a/b, respectively. This is used in the proof of Theorem 1.1 of the paper.
-/
def selectedSource (t : _root_.AbcTwoNinths.Basic.Triple) : ℚ :=
  match _root_.AbcTwoNinths.Statement.minRadicalSide t with
  | .a => (t.c : ℚ) / (t.b : ℚ)
  | .b => (t.c : ℚ) / (t.a : ℚ)
  | .c => -(t.a : ℚ) / (t.b : ℚ)

/--
The rational parameter eta lies strictly between zero and one ninth. This is used in the proof of Theorem 1.1 of the paper.
-/
def admissibleEta (η : ℚ) : Prop := 0 < η ∧ η < (1 : ℚ) / 9

/--
The high-triple exponent lambda in Table 1 is one minus three times eta. This is used in the proof of Theorem 1.1 of the paper.
-/
def highRate (η : ℚ) : ℝ := 1 - 3 * (η : ℝ)

/--
The maximum admissible cutoff exponent e is one hundredth of lambda minus two thirds, with the difference taken first. This is used in the proof of Theorem 1.1 of the paper.
-/
def cutoffBudget (η : ℚ) : ℝ := (_root_.AbcTwoNinths.Statement.highRate η - 2 / 3) / 100

/--
The cutoff exponent is positive and at most the Table 1 budget e. This is used in the proof of Theorem 1.1 of the paper.
-/
def admissibleCutoff (η : ℚ) (σ : ℝ) : Prop := 0 < σ ∧ σ ≤ _root_.AbcTwoNinths.Statement.cutoffBudget η

/--
The margin kappa lies strictly between zero and (1 - 9 eta)/16. This is used in the proof of Theorem 1.1 of the paper.
-/
def admissibleMargin (η : ℚ) (κ : ℝ) : Prop :=
  0 < κ ∧ κ < (1 - 9 * (η : ℝ)) / 16

/--
The radical coordinate x is at least the threshold X and H is at least exp(lambda x). This is used in the proof of Theorem 1.1 of the paper.
-/
def High (η : ℚ) (X : ℝ) (t : _root_.AbcTwoNinths.Basic.Triple) : Prop :=
  X ≤ t.thirdLogRadical ∧ Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) ≤ t.logHeight

/--
Sum the valuation times log prime over prime factors at or below the cutoff. This is used in the proof of Theorem 1.1 of the paper.
-/
def primePowerLogMass (n : ℕ) (cutoff : ℝ) : ℝ := by
  classical
  exact (n.primeFactors.filter (fun q : ℕ => (q : ℝ) ≤ cutoff)).sum
    (fun q : ℕ => (padicValNat q n : ℝ) * Real.log (q : ℝ))

/--
The height H of this triple is at most C times the k-th power of its radical. This is used in the proof of Theorem 1.1 of the paper.
-/
def PolynomialHeightBound (C k : ℝ) (t : _root_.AbcTwoNinths.Basic.Triple) : Prop := t.logHeight ≤ C * (t.radical : ℝ) ^ k

/--
The real contact log(c/a) is at most kappa times the height. This is used in the proof of Theorem 1.1 of the paper.
-/
def RealContactBound (κ : ℝ) (t : _root_.AbcTwoNinths.Basic.Triple) : Prop := Real.log ((t.c : ℝ) / (t.a : ℝ)) ≤ κ * t.logHeight

/--
The small-prime mass on the least-radical side up to H exp(-sigma x) is at most kappa H. This is used in the proof of Theorem 1.1 of the paper.
-/
def SmallPrimeMassBound (σ κ : ℝ) (t : _root_.AbcTwoNinths.Basic.Triple) : Prop :=
  _root_.AbcTwoNinths.Statement.primePowerLogMass (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) (t.logHeight * Real.exp (-σ * t.thirdLogRadical)) ≤ κ * t.logHeight

/--
Some positive coefficient and nonnegative exponent give a global polynomial height bound. This is used in the proof of Theorem 1.1 of the paper.
-/
def PolyCap : Prop := ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, _root_.AbcTwoNinths.Statement.PolynomialHeightBound C k t

/--
For each admissible eta, both estimates hold on ordered high triples at one nonnegative threshold with a common admissible cutoff and margin. This is used in the proof of Theorem 1.1 of the paper.
-/
def FixedMarginExterior : Prop :=
  ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
    ∃ σ κ X : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ ∧ _root_.AbcTwoNinths.Statement.admissibleMargin η κ ∧ 0 ≤ X ∧
      ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t ∧ _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t

end

end

end AbcTwoNinths.Statement
