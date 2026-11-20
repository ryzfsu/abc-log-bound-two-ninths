/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Paper.S4_ExteriorE2.InterpolationGridCollision

/-!
# Small Prime Valuation Mass

Uses the size of a residue image to obtain a short projection and combines bounds for the two
ranges of small primes. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.shortProjectionOfActualImageBudget`
* `AbcTwoNinths.ExteriorE2.fixedMarginExteriorOfSplitTails`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
The logarithmic budget for the image cardinality gives a kernel element with nonzero roof projection and all projected coordinates smaller than 1/Q in absolute value. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem shortProjectionOfActualImageBudget
    {ι G : Type*} [Fintype ι] [AddGroup G] [Finite G]
    (r : ((Unit ⊕ ι) → ℤ) →+ G) {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (v : ι → ℤ)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => (k : ℤ)) v)
    {g H U θ depth rootHeight : ℝ}
    (hg : 1 ≤ g) (hH : 0 < H) (hU : 0 < U) (hθ : 0 < θ)
    (hroof : H ≤ (k : ℝ) * (g * U))
    (hshare : θ * H ≤ depth) (hlte : depth ≤ rootHeight + Real.log g)
    (hroot : g * rootHeight ≤ 2 * H) (hroot_lb : Real.log 2 ≤ rootHeight)
    (hH_onset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H)
    (hbudget : Real.log (4 / θ) + Real.log U + (Fintype.card ι : ℝ) * Real.log Q <
      Real.log H - Real.log (Nat.card r.range : ℝ)) :
    ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a i| < 1 / (Q : ℝ) := by
  have hB : 0 < (Nat.card r.range : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := r.range))
  apply _root_.AbcTwoNinths.ExteriorE2.shortProjectionOfNativeLogBudget r hk hQ v hgen hB hg hH hU hθ
    le_rfl hroof hshare hlte hroot hroot_lb hH_onset _ hbudget
  linarith

end

section




/--
At a common admissible margin, the maximum of the two exterior thresholds gives both bounds for every ordered triple above it. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem fixedMarginExteriorOfSplitTails
    (htail : ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
      ∃ σ κ X₁ X₂ : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ ∧ _root_.AbcTwoNinths.Statement.admissibleMargin η κ ∧
        0 ≤ X₁ ∧ 0 ≤ X₂ ∧
        (∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X₁ t → _root_.AbcTwoNinths.Statement.RealContactBound κ t) ∧
        (∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X₂ t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t)) :
    _root_.AbcTwoNinths.Statement.FixedMarginExterior := by
  intro η hη
  obtain ⟨σ, κ, X₁, X₂, hσ, hκ, hX₁, _, he1, he2⟩ := htail η hη
  refine ⟨σ, κ, max X₁ X₂, hσ, hκ, hX₁.trans (le_max_left _ _), ?_⟩
  intro t hab ht
  exact ⟨he1 t hab ⟨(le_max_left _ _).trans ht.1, ht.2⟩,
    he2 t hab ⟨(le_max_right _ _).trans ht.1, ht.2⟩⟩

end

end AbcTwoNinths.ExteriorE2
