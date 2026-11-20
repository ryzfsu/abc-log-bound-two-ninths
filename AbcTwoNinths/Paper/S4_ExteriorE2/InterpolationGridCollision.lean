/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.InterpolationGridMargin
public import AbcTwoNinths.Basic.DiscretePositiveRank

/-!
# Interpolation Grid Collision

The module obtains a short projected vector by applying a grid collision bound to the available logarithmic budget. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.shortProjectionOfNativeLogBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section


/--
The logarithmic index budget yields a kernel vector with nonzero roof projection and every coordinate strictly smaller than the reciprocal grid size in absolute value. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem shortProjectionOfNativeLogBudget
    {ι G : Type*} [Fintype ι] [AddGroup G] [Finite G]
    (r : ((Unit ⊕ ι) → ℤ) →+ G) {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (v : ι → ℤ)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => (k : ℤ)) v)
    {B g H U θ depth rootHeight saving : ℝ}
    (hB : 0 < B) (hg : 1 ≤ g) (hH : 0 < H) (hU : 0 < U) (hθ : 0 < θ)
    (hI : (Nat.card r.range : ℝ) ≤ B)
    (hroof : H ≤ (k : ℝ) * (g * U))
    (hshare : θ * H ≤ depth) (hlte : depth ≤ rootHeight + Real.log g)
    (hroot : g * rootHeight ≤ 2 * H) (hroot_lb : Real.log 2 ≤ rootHeight)
    (hH_onset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H)
    (hsaving : Real.log B ≤ Real.log H - saving)
    (hbudget : Real.log (4 / θ) + Real.log U + (Fintype.card ι : ℝ) * Real.log Q < saving) :
    ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a i| < 1 / (Q : ℝ) := by
  have hm := _root_.AbcTwoNinths.ExteriorE2.nativeGridMarginOfLogBudget hQ hB hg hH hU hθ hI hroof
    hshare hlte hroot hroot_lb hH_onset hsaving hbudget
  simpa using _root_.AbcTwoNinths.Basic.discretePositiveRank r hk Nat.one_pos hQ v hgen (by simpa using hm)

end

end AbcTwoNinths.ExteriorE2
