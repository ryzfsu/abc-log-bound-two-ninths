/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SelectedPlaneData

/-!
# Reindexing the pivot coordinate

The module puts the selected prime first and transports the exponent lattice, character, and distinguished line. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.reindexLine`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section




noncomputable section

/--
The equivalence puts the chosen peak coordinate first and indexes the remaining coordinates by its complement. This is used in Section 6 of the paper.
-/
def roofFirst {J : Type*} (j : J) : Unit ⊕ {i : J // i ≠ j} ≃ J := by
  classical
  let single : Unit ≃ {i : J // i = j} :=
    { toFun := fun _ => ⟨j, rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun i => Subtype.ext i.property.symm }
  exact (Equiv.sumCongr single (Equiv.refl _)).trans (Equiv.sumCompl (· = j))

private theorem residueReindex {J K : Type*} [Fintype J] [Fintype K]
    {p : ℕ} [Fact p.Prime] (e : J ≃ K) (base : K → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i) (z : K → ℤ) :
    _root_.AbcTwoNinths.ExteriorE2.residue (base ∘ e) (fun i => prime (e i)) (fun i => avoid (e i))
      (Multiplicative.ofAdd (z ∘ e)) = _root_.AbcTwoNinths.ExteriorE2.residue base prime avoid (Multiplicative.ofAdd z) := by
  change (∏ i, _root_.AbcTwoNinths.ExteriorE2.residueUnit base prime avoid (e i) ^ z (e i)) =
    ∏ j, _root_.AbcTwoNinths.ExteriorE2.residueUnit base prime avoid j ^ z j
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

private theorem monomialReindex {J K : Type*} [Fintype J] [Fintype K]
    (e : J ≃ K) (base : K → ℕ) (prime : ∀ i, (base i).Prime) (z : K → ℤ) :
    _root_.AbcTwoNinths.ExteriorE2.monomial (base ∘ e) (fun i => prime (e i))
      (Multiplicative.ofAdd (z ∘ e)) = _root_.AbcTwoNinths.ExteriorE2.monomial base prime (Multiplicative.ofAdd z) := by
  change (∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime (e i) ^ z (e i)) =
    ∏ j, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime j ^ z j
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

/--
Reindexing the prime coordinates gives a multiplicative equivalence of signed residue lattices. This is used in Section 6 of the paper.
-/
def reindexLattice {J K : Type*} [Fintype J] [Fintype K]
    {p : ℕ} [Fact p.Prime] (e : J ≃ K) (base : K → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i) :
    _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid ≃* _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (base ∘ e) (fun i => prime (e i)) (fun i => avoid (e i)) where
  toFun w := ⟨Multiplicative.ofAdd (w.val.toAdd ∘ e), by
    have hw := (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).mp w.property
    apply (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).mpr
    rw [residueReindex e base prime avoid]
    exact hw⟩
  invFun w := ⟨Multiplicative.ofAdd (w.val.toAdd ∘ e.symm), by
    have hw := (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).mp w.property
    apply (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).mpr
    have he := residueReindex e base prime avoid (w.val.toAdd ∘ e.symm)
    have hcomp : (w.val.toAdd ∘ e.symm) ∘ e = w.val.toAdd := by
      funext i
      simp [Function.comp_def]
    rw [hcomp] at he
    rw [← he]
    exact hw⟩
  left_inv w := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    change w.val.toAdd (e (e.symm i)) = _
    rw [e.apply_symm_apply]
  right_inv w := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    change w.val.toAdd (e.symm (e i)) = _
    rw [e.symm_apply_apply]
  map_mul' _ _ := rfl

/-- A reindexed lattice element has at coordinate `i` the original exponent at `e i`. -/
@[simp] theorem reindexLatticeApply {J K : Type*} [Fintype J] [Fintype K]
    {p : ℕ} [Fact p.Prime] (e : J ≃ K) (base : K → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i)
    (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (i : J) :
    (_root_.AbcTwoNinths.Diamond.reindexLattice e base prime avoid w).val.toAdd i = w.val.toAdd (e i) := rfl

/-- The rational character of a signed residue-lattice element is invariant under reindexing. -/
theorem reindexCharacter {J K : Type*} [Fintype J] [Fintype K]
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)] (e : J ≃ K) (base : K → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i)
    (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) :
    _root_.AbcTwoNinths.Diamond.character (base ∘ e) (fun i => prime (e i)) (fun i => avoid (e i))
      (_root_.AbcTwoNinths.Diamond.reindexLattice e base prime avoid w) = _root_.AbcTwoNinths.Diamond.character base prime avoid w := by
  change
    (if _root_.AbcTwoNinths.ExteriorE2.residue (base ∘ e) (fun i => prime (e i)) (fun i => avoid (e i))
      (Multiplicative.ofAdd (w.val.toAdd ∘ e)) = 1 then (1 : ℚˣ) else -1) *
        _root_.AbcTwoNinths.ExteriorE2.monomial (base ∘ e) (fun i => prime (e i))
          (Multiplicative.ofAdd (w.val.toAdd ∘ e)) =
      (if _root_.AbcTwoNinths.ExteriorE2.residue base prime avoid w.val = 1 then (1 : ℚˣ) else -1) *
        _root_.AbcTwoNinths.ExteriorE2.monomial base prime w.val
  rw [residueReindex e base prime avoid, monomialReindex e base prime]
  rfl

/--
Reindexing preserves the property that lattice points on the real source line are integer powers of its generator. This is used in Section 6 of the paper.
-/
theorem reindexLine {J K : Type*} [Fintype J] [Fintype K]
    {p : ℕ} [Fact p.Prime] (e : J ≃ K) (base : K → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i) (s : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid)
    (line : ∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (a : ℝ),
      (∀ i, (w.val.toAdd i : ℝ) = a * s.val.toAdd i) → ∃ c : ℤ, w = s ^ c) :
    ∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (base ∘ e) (fun i => prime (e i)) (fun i => avoid (e i))) (a : ℝ),
      (∀ i, (w.val.toAdd i : ℝ) = a * (_root_.AbcTwoNinths.Diamond.reindexLattice e base prime avoid s).val.toAdd i) →
        ∃ c : ℤ, w = (_root_.AbcTwoNinths.Diamond.reindexLattice e base prime avoid s) ^ c := by
  intro w a hw
  let E := _root_.AbcTwoNinths.Diamond.reindexLattice e base prime avoid
  have he : E (E.symm w) = w := E.apply_symm_apply w
  have hp (i : K) : ((E.symm w).val.toAdd i : ℝ) = a * s.val.toAdd i := by
    have h := hw (e.symm i)
    rw [← he] at h
    simp only [E, _root_.AbcTwoNinths.Diamond.reindexLatticeApply, e.apply_symm_apply] at h
    exact h
  obtain ⟨c, hc⟩ := line (E.symm w) a hp
  exact ⟨c, by rw [← map_zpow, ← hc, he]⟩

end

end

end AbcTwoNinths.Diamond
