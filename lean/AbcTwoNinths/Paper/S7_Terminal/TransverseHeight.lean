/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.SelectedInterpolationHeightSum
public import AbcTwoNinths.Paper.S6_Diamond.FreshTorusWitness

/-!
# Transverse Height

The module bounds the height of a fresh-prime direction from its transverse coordinates. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.transverseHeight`
* `AbcTwoNinths.Terminal.freshHeightBound`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal





section
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable (b : ((Unit ⊕ I) ⊕ Bool) → ℕ) (pr : ∀ i, (b i).Prime)
variable (av : ∀ i, p ≠ b i) (inj : Function.Injective b)
variable (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => b (.inl i)) (fun i => pr (.inl i)) (fun i => av (.inl i)))
variable (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData b pr av) (hv : v.val.toAdd (.inl ()) ≠ 0)
variable (hf : u.val.toAdd (.inr false) = 1) (ht : u.val.toAdd (.inr true) = -1)
include inj hv hf ht

set_option linter.unusedSectionVars false in
/--
The height at the shear cancelling the pivot is at most the projected cost plus the logarithm of the larger fresh prime. This is used in Section 7 of the paper.
-/
theorem transverseHeight :
    let c := (u.val.toAdd (.inl (.inl ())) : ℝ) / v.val.toAdd (.inl ())
    let s := _root_.AbcTwoNinths.Terminal.overlapShape b pr av inj v u (.inl ()) hv hf
    _root_.AbcTwoNinths.Basic.height s (-c, 1) ≤
      _root_.AbcTwoNinths.ExteriorE2.cost (fun j : I => Real.log (b (.inl (.inr j)) : ℝ))
        (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) +
      Real.log ((max (b (.inr false)) (b (.inr true)) : ℕ) : ℝ) := by
  classical
  intro c s
  let V := _root_.AbcTwoNinths.Diamond.extension b pr av v
  let e := (Fintype.equivFin ((Unit ⊕ I) ⊕ Bool)).symm
  let l (i : (Unit ⊕ I) ⊕ Bool) : ℝ := Real.log (b i : ℝ)
  let f (i : (Unit ⊕ I) ⊕ Bool) : ℝ :=
    ((u.val.toAdd i : ℝ) - c * (V.val.toAdd i : ℝ)) * l i
  let T := _root_.AbcTwoNinths.ExteriorE2.cost (fun j : I => l (.inl (.inr j)))
    (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i)))
  have hl (i) : 0 ≤ l i := Real.log_nonneg (by exact_mod_cast (pr i).one_le)
  have hx (i) : _root_.AbcTwoNinths.Basic.logCoord s (-c, 1) i = f (e i) := by
    change (-c * (V.val.toAdd (e i) : ℝ) + 1 * (u.val.toAdd (e i) : ℝ)) * l (e i) = _
    dsimp only [f]
    ring
  have rf : f (.inl (.inl ())) = 0 := by
    change (((u.val.toAdd (.inl (.inl ())) : ℝ) - _ / _ * (v.val.toAdd (.inl ()) : ℝ)) * _) = 0
    rw [div_mul_cancel₀ _ (by exact_mod_cast hv), sub_self, zero_mul]
  have ff : f (.inr false) = l (.inr false) := by
    change ((u.val.toAdd (.inr false) : ℝ) - c * (0 : ℤ)) * _ = _
    simp [hf]
  have ft : f (.inr true) = -l (.inr true) := by
    change ((u.val.toAdd (.inr true) : ℝ) - c * (0 : ℤ)) * _ = _
    simp [ht]
  have absOld : (∑ i : I, |f (.inl (.inr i))|) = T := by
    apply Finset.sum_congr rfl
    intro j _
    change |((u.val.toAdd (.inl (.inr j)) : ℝ) - c * (v.val.toAdd (.inr j) : ℝ)) *
      l (.inl (.inr j))| = l (.inl (.inr j)) * |(_ : ℝ)|
    rw [abs_mul, abs_of_nonneg (hl _), mul_comm]
    rfl
  let L := Real.log ((max (b (.inr false)) (b (.inr true)) : ℕ) : ℝ)
  have hL (i : Bool) : l (.inr i) ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (pr _).pos)
    cases i <;> exact_mod_cast (by first | apply le_max_left | apply le_max_right)
  have bound (g : ℝ → ℝ) (g0 : g 0 = 0) (ga : ∀ t, g t ≤ |t|)
      (fresh : g (l (.inr false)) + g (-l (.inr true)) ≤ L) :
      (∑ j, g (_root_.AbcTwoNinths.Basic.logCoord s (-c, 1) j)) ≤ T + L := by
    rw [Fintype.sum_equiv e (fun j => g (_root_.AbcTwoNinths.Basic.logCoord s (-c, 1) j)) (fun i => g (f i))
      (fun j => congrArg g (hx j)), Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h := (Finset.sum_le_sum (s := Finset.univ)
      (fun (i : I) _ => ga (f (.inl (.inr i))))).trans_eq absOld
    simp only [Fintype.sum_unique, rf, g0, zero_add, Fintype.sum_bool, ff, ft]
    linarith
  apply max_le
  · apply bound (fun x => max x 0) (by simp) (fun x => max_le (le_abs_self _) (abs_nonneg _))
    rw [max_eq_left (hl _), max_eq_right (neg_nonpos.mpr (hl _)), add_zero]
    exact hL false
  · apply bound (fun x => max (-x) 0) (by simp) (fun x => max_le (neg_le_abs _) (abs_nonneg _))
    rw [neg_neg, max_eq_right (neg_nonpos.mpr (hl _)), max_eq_left (hl _), zero_add]
    exact hL true

/--
The log height of the plane character at each integer site is bounded by the sheared diamond expression. This is used in Section 7 of the paper.
-/
theorem freshHeightBound (z : _root_.AbcTwoNinths.Basic.Sites) :
    let c := (u.val.toAdd (.inl (.inl ())) : ℝ) / v.val.toAdd (.inl ())
    let V := _root_.AbcTwoNinths.Diamond.extension b pr av v
    let γ := _root_.AbcTwoNinths.Diamond.planeCharacter b pr av V u
    let h := Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (γ (Multiplicative.ofAdd ((1, 0) : _root_.AbcTwoNinths.Basic.Sites)) : ℚ) : ℝ)
    let t := _root_.AbcTwoNinths.ExteriorE2.cost (fun j : I => Real.log (b (.inl (.inr j)) : ℝ))
      (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) +
      Real.log ((max (b (.inr false)) (b (.inr true)) : ℕ) : ℝ)
    Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (γ (Multiplicative.ofAdd z) : ℚ) : ℝ) ≤
      |(z.1 : ℝ) + c * z.2| * h + |(z.2 : ℝ)| * t := by
  intro c V γ h t
  let s := _root_.AbcTwoNinths.Terminal.overlapShape b pr av inj v u (.inl ()) hv hf
  have hz := _root_.AbcTwoNinths.Terminal.overlapRowHeight b pr av inj v u (.inl ()) hv hf z
  have ha := _root_.AbcTwoNinths.Terminal.overlapRowHeight b pr av inj v u (.inl ()) hv hf (1, 0)
  change _ = _root_.AbcTwoNinths.Basic.height s (_root_.AbcTwoNinths.Basic.lift z) at hz
  change h = _root_.AbcTwoNinths.Basic.height s (_root_.AbcTwoNinths.Basic.lift (1,0)) at ha
  have haxis : _root_.AbcTwoNinths.Basic.lift ((1,0) : _root_.AbcTwoNinths.Basic.Sites) = ((1,0) : ℝ × ℝ) := by simp [_root_.AbcTwoNinths.Basic.lift]
  rw [haxis] at ha
  rw [hz, ha]
  have eqn : _root_.AbcTwoNinths.Basic.lift z = _root_.AbcTwoNinths.Basic.lin ((z.1 : ℝ) + c*z.2) z.2 (1,0) (-c,1) := by
    ext <;> simp [_root_.AbcTwoNinths.Basic.lin, _root_.AbcTwoNinths.Basic.lift]
    ring
  rw [eqn]
  exact (_root_.AbcTwoNinths.Basic.heightLinLe s _ _ _ _).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (_root_.AbcTwoNinths.Terminal.transverseHeight b pr av inj v u hv hf ht) (abs_nonneg _)))

end
end

end AbcTwoNinths.Terminal
