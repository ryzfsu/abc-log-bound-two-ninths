/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.FreshTorusWitness

/-!
# Primitive Plane Line

The module proves primitivity of the distinguished line used in the fresh-prime plane. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.primitiveOfLine`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section




/--
A scalar dividing a lattice line generator with nonzero pivot is a unit. This is used in Section 6 of the paper.
-/
theorem primitiveOfLine {I : Type} [Fintype I] {p : ℕ} [Fact p.Prime]
    (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (hv : v.val.toAdd (.inl ()) ≠ 0)
    (line : ∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (a : ℝ),
      (∀ i, (w.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, w = v ^ c)
    (a : ℤ) (w : (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid).toAdditive.ker)
    (h : a • w = ⟨v.val.toAdd, v.property⟩) : IsUnit a := by
  let W : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid := ⟨Multiplicative.ofAdd w.val, w.property⟩
  have eqn (i : Unit ⊕ I) : a * w.val i = v.val.toAdd i := by
    have e := congrArg (fun z : (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid).toAdditive.ker => z.val i) h
    change a • (w.val i) = v.val.toAdd i at e
    simpa [zsmul_eq_mul] using e
  have ha : a ≠ 0 := by
    intro e
    exact hv (by simpa [e] using (eqn (.inl ())).symm)
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨c, hc⟩ := line W (a : ℝ)⁻¹ (by
    intro i
    change (w.val i : ℝ) = _
    rw [← eqn i, Int.cast_mul, ← mul_assoc, inv_mul_cancel₀ har, one_mul])
  have hcw : w.val (.inl ()) = c * v.val.toAdd (.inl ()) := by
    have e := congrArg (fun z : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid => z.val.toAdd (.inl ())) hc
    change w.val (.inl ()) = c • (v.val.toAdd (.inl ())) at e
    simpa [zsmul_eq_mul] using e
  have ac : a * c = 1 := by
    apply mul_right_cancel₀ hv
    rw [mul_assoc, ← hcw, eqn, one_mul]
  exact ⟨⟨a, c, ac, (mul_comm c a).trans ac⟩, rfl⟩

end

end AbcTwoNinths.Diamond
