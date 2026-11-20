/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice

/-!
# Selected Shear Estimate

The module transfers a weighted shear estimate to separated projected columns after reindexing the kernel. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.projectedSeparationOfReindexedShear`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/--
Reindexing the prime support identifies membership in the reduction kernel with membership in the signed residue kernel.
-/
theorem reindexedReductionMemKernel {p : ℕ} [Fact p.Prime]
    {I J : Type*} [Fintype I] [Fintype J] (e : Unit ⊕ I ≃ J)
    (q : J → ℕ) (hq : ∀ i, (q i).Prime) (ha : ∀ i, p ≠ q i)
    (w : _root_.AbcTwoNinths.ExteriorE2.Old I) :
    w ∈ (_root_.AbcTwoNinths.ExteriorE2.residueLatticeReduction (q ∘ e) (fun i => hq (e i)) (fun i => ha (e i))).ker ↔
      Multiplicative.ofAdd (w ∘ e.symm) ∈ _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq ha) := by
  have hr : _root_.AbcTwoNinths.ExteriorE2.residue (q ∘ e) (fun i => hq (e i)) (fun i => ha (e i))
      (Multiplicative.ofAdd w) =
      _root_.AbcTwoNinths.ExteriorE2.residue q hq ha (Multiplicative.ofAdd (w ∘ e.symm)) := by
    change (∏ i, _root_.AbcTwoNinths.ExteriorE2.residueUnit q hq ha (e i) ^ w i) =
      ∏ j, _root_.AbcTwoNinths.ExteriorE2.residueUnit q hq ha j ^ w (e.symm j)
    exact Fintype.prod_equiv e _ _ (fun i => by rw [e.symm_apply_apply])
  change _root_.AbcTwoNinths.ExteriorE2.reduction _ (Multiplicative.ofAdd w) = 1 ↔
    _root_.AbcTwoNinths.ExteriorE2.reduction _ (Multiplicative.ofAdd (w ∘ e.symm)) = 1
  unfold _root_.AbcTwoNinths.ExteriorE2.reduction
  simp only [MonoidHom.comp_apply, hr]

/-- After reindexing the distinguished coordinate first, a kernel vector with projected cost
below the weighted separation threshold has zero projection. -/
theorem projectedSeparationOfReindexedShear {p : ℕ} [Fact p.Prime]
    {I J : Type*} [Fintype I] [Fintype J] (e : Unit ⊕ I ≃ J)
    (q : J → ℕ) (hq : ∀ i, (q i).Prime) (ha : ∀ i, p ≠ q i)
    (s : J → ℤ) (hs : s (e (.inl ())) ≠ 0) {T : ℝ}
    (shear : ∀ (v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq ha)),
      (¬ ∃ a : ℚ, ∀ i, (v.val.toAdd i : ℚ) = a * (s i : ℚ)) →
      ∀ a : ℝ, T ≤ ∑ i, |(v.val.toAdd i : ℝ) - a * (s i : ℝ)| * Real.log (q i : ℝ)) :
    ∀ w ∈ (_root_.AbcTwoNinths.ExteriorE2.residueLatticeReduction (q ∘ e) (fun i => hq (e i)) (fun i => ha (e i))).ker,
      _root_.AbcTwoNinths.ExteriorE2.cost (fun j => Real.log (q (e (.inr j)) : ℝ)) (_root_.AbcTwoNinths.ExteriorE2.project (s ∘ e) w) < T →
      _root_.AbcTwoNinths.ExteriorE2.project (s ∘ e) w = 0 := by
  intro w hw hshort
  let v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue q hq ha) :=
    ⟨Multiplicative.ofAdd (w ∘ e.symm), (_root_.AbcTwoNinths.Diamond.reindexedReductionMemKernel e q hq ha w).mp hw⟩
  by_contra hne
  have hind : ¬ ∃ a : ℚ, ∀ i, (v.val.toAdd i : ℚ) = a * (s i : ℚ) := by
    rintro ⟨a, ha⟩
    apply hne
    have hreal (i : Unit ⊕ I) : (w i : ℝ) = (a : ℝ) * (s (e i) : ℝ) := by
      have h := ha (e i)
      change (w (e.symm (e i)) : ℚ) = _ at h
      rw [e.symm_apply_apply] at h
      exact_mod_cast h
    have hs' : (s (e (.inl ())) : ℝ) ≠ 0 := by exact_mod_cast hs
    ext j
    change (w (.inr j) : ℝ) - (w (.inl ()) : ℝ) / (s (e (.inl ())) : ℝ) *
      (s (e (.inr j)) : ℝ) = 0
    rw [hreal (.inr j), hreal (.inl ())]
    field_simp
    ring
  let a : ℝ := (w (.inl ()) : ℝ) / (s (e (.inl ())) : ℝ)
  have h := shear v hind a
  let f (i : Unit ⊕ I) : ℝ :=
    |(w i : ℝ) - a * (s (e i) : ℝ)| * Real.log (q (e i) : ℝ)
  have heq : (∑ i, f i) = ∑ j, |(v.val.toAdd j : ℝ) - a * (s j : ℝ)| * Real.log (q j : ℝ) :=
    Fintype.sum_equiv e _ _ (fun i => by
      change f i = |(w (e.symm (e i)) : ℝ) - a * (s (e i) : ℝ)| * Real.log (q (e i) : ℝ)
      rw [e.symm_apply_apply])
  have hzero : f (.inl ()) = 0 := by
    have hs' : (s (e (.inl ())) : ℝ) ≠ 0 := by exact_mod_cast hs
    have hh : (w (.inl ()) : ℝ) - a * (s (e (.inl ())) : ℝ) = 0 := by
      dsimp [a]
      field_simp
      ring
    simp [f, hh]
  rw [← heq, Fintype.sum_sum_type] at h
  simp only [Fintype.sum_unique, hzero, zero_add] at h
  have hcost : (∑ j, f (.inr j)) =
      _root_.AbcTwoNinths.ExteriorE2.cost (fun j => Real.log (q (e (.inr j)) : ℝ)) (_root_.AbcTwoNinths.ExteriorE2.project (s ∘ e) w) := by
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  exact (not_lt_of_ge (hcost ▸ h)) hshort

end

end AbcTwoNinths.Diamond
