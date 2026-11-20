/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffBudget

/-!
# Cutoff Residue Image Bound

The module finds a short projected vector using a bound on the cutoff residue image. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.shortProjectionOfCutoffImage`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
The cutoff bound on the residue image, together with the height and grid budgets, yields a
kernel vector whose roof projection is nonzero and has all coordinates below `1 / Q` in
absolute value.
-/
theorem shortProjectionOfCutoffImage
    {ι G : Type*} [Fintype ι] [AddGroup G] [Finite G]
    (r : ((Unit ⊕ ι) → ℤ) →+ G) {k Q M : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (v : ι → ℤ)
    (hgen : ∀ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => (k : ℤ)) v)
    {g H U θ depth rootHeight σ x : ℝ}
    (hg : 1 ≤ g) (hH : 0 < H) (hU : 0 < U) (hθ : 0 < θ)
    (hroof : H ≤ (k : ℝ) * (g * U))
    (hshare : θ * H ≤ depth) (hlte : depth ≤ rootHeight + Real.log g)
    (hroot : g * rootHeight ≤ 2 * H) (hroot_lb : Real.log 2 ≤ rootHeight)
    (hH_onset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H)
    (hcard : Nat.card r.range ≤ M) (hM : (M : ℝ) ≤ H * Real.exp (-σ * x))
    (hbudget : Real.log (4 / θ) + Real.log U + (Fintype.card ι : ℝ) * Real.log Q < σ * x) :
    ∃ a ∈ r.ker, _root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection (k : ℤ) v a i| < 1 / (Q : ℝ) := by
  refine _root_.AbcTwoNinths.ExteriorE2.shortProjectionOfActualImageBudget r hk hQ v hgen hg hH hU hθ
    hroof hshare hlte hroot hroot_lb hH_onset (hbudget.trans_le ?_)
  have hpos : 0 < (Nat.card r.range : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := r.range))
  have hcap : (Nat.card r.range : ℝ) ≤ H * Real.exp (-σ * x) :=
    (show (Nat.card r.range : ℝ) ≤ M by exact_mod_cast hcard).trans hM
  have hlog := Real.log_le_log hpos hcap
  rw [Real.log_mul hH.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

end

end AbcTwoNinths.ExteriorE2
