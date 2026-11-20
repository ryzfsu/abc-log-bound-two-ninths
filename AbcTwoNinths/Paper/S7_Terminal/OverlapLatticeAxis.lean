/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ShapeCount
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPlaneData

/-!
# Overlap Lattice Axis

The module defines the lattice shape associated with the overlap and identifies the height of its distinguished axis. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.overlapShape`
-/

@[expose] public section
namespace AbcTwoNinths.Terminal

noncomputable section

section




variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable (base : (ι ⊕ Bool) → ℕ) (prime : ∀ j, (base j).Prime)
variable (avoid : ∀ j, p ≠ base j) (hi : Function.Injective base)
variable (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun j => base (.inl j)) (fun j => prime (.inl j))
  (fun j => avoid (.inl j))) (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid)
variable (k : ι) (hroof : v.val.toAdd k ≠ 0) (hu : u.val.toAdd (.inr false) = 1)

/--
Package the ordered source and overlap basis without changing its site coordinates. This is used in Section 7 of the paper.
-/
def overlapShape : _root_.AbcTwoNinths.Basic.Shape (Fintype.card (ι ⊕ Bool)) where
  primeAt j := base ((Fintype.equivFin (ι ⊕ Bool)).symm j)
  prime j := prime _
  distinct := hi.comp (Fintype.equivFin (ι ⊕ Bool)).symm.injective
  v j := (_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val.toAdd ((Fintype.equivFin (ι ⊕ Bool)).symm j)
  u j := u.val.toAdd ((Fintype.equivFin (ι ⊕ Bool)).symm j)
  independent a b hab := by
    let e := Fintype.equivFin (ι ⊕ Bool)
    have hh (j : ι ⊕ Bool) :
        a * ((_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val.toAdd j : ℝ) +
          b * (u.val.toAdd j : ℝ) = 0 := by
      have hj := hab (e j)
      change a * ((_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val.toAdd (e.symm (e j)) : ℝ) +
        b * (u.val.toAdd (e.symm (e j)) : ℝ) = 0 at hj
      simpa only [e.symm_apply_apply] using hj
    have hvf : (_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val.toAdd (.inr false) = 0 := rfl
    have hb : b = 0 := by simpa [hvf, hu] using hh (.inr false)
    have hvk : (_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val.toAdd (.inl k) = v.val.toAdd k := rfl
    have hkr : (v.val.toAdd k : ℝ) ≠ 0 := by exact_mod_cast hroof
    have ha : a * (v.val.toAdd k : ℝ) = 0 := by simpa [hvk, hb] using hh (.inl k)
    exact ⟨(mul_eq_zero.mp ha).resolve_right hkr, hb⟩

end

end
end AbcTwoNinths.Terminal
