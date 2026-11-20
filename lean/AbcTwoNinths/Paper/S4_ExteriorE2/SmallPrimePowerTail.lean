/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PivotedSource
public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeExponentHeight
public import AbcTwoNinths.Paper.S4_ExteriorE2.ShortProjectedVector
public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedShortProjection
public import AbcTwoNinths.Paper.S4_ExteriorE2.ReducedOrientedPlane

/-!
# Exterior bound for small prime powers

Bounds the total logarithmic mass of small prime powers on the side of least radical by excluding
deep composite moduli. This is Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.smallPrimeMassEventually`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real


/--
For admissible `η` and `σ` and any positive `κ` , some height threshold excludes tight
moduli satisfying the divisibility, parity, cutoff, and mass conditions.
-/
theorem tightModulusExclusionOfParameters {η : ℚ} {σ κ : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : 0 < κ) :
    ∃ X : ℝ, _root_.AbcTwoNinths.ExteriorE2.TightModulusExclusion η σ κ X := by
  classical
  let Q := ⌈max 48 (44236800 / κ)⌉₊
  have hQ48 : 48 ≤ (Q : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hQκ : 44236800 / κ ≤ (Q : ℝ) := (le_max_right _ _).trans (Nat.le_ceil _)
  have hQ : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
  obtain ⟨X, hX⟩ := _root_.AbcTwoNinths.ExteriorE2.uniformConditions Q hη hσ hκ
  refine ⟨X, fun t htord ht M L hM hL hd hpar hcut hmod hmass => ?_⟩
  have h := hX t ht M L hM hcut hmod hmass
  have hH := (exp_pos _).trans_le h.high.2
  have hell : 0 < log (M : ℝ) := log_pos (by exact_mod_cast (show 1 < M by omega))
  obtain ⟨s⟩ := _root_.AbcTwoNinths.ExteriorE2.actualSource t htord h.modulus hL hd
  obtain ⟨V, g, hg, hpivot, hV, he, hline, hgκ, hdV, hlte, hroot, hHt, hfloor⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.generatorOfKernel s.q s.hprime s.hcop s.hinj s.E s.hroof s.hkernel hM hpar s.hdepth
      hH hκ hmass s.hheight.2 h.root_onset
  have hdim : Fintype.card s.i ≤ s.S.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective (Subtype.val : s.i → s.S) Subtype.val_injective
  have hshort := _root_.AbcTwoNinths.ExteriorE2.actualShortVector h hκ hQ s.q s.hprime s.hcop s.E V hg he hpivot
    s.hmax hline s.hheight.1 s.hweights s.S s.hsupport hdim hlte hroot hfloor.le hcut hmass
  let w := fun j => log (s.q j : ℝ)
  have hw j : 0 < w j := log_pos (by exact_mod_cast (s.hprime j).one_lt)
  let v := fun i => V (.inr i)
  have hshape : Sum.elim (fun _ : Unit => V (.inl ())) v = V := by
    funext j
    rcases j with ⟨⟩ | j <;> rfl
  have hgeom := fun U Z => _root_.AbcTwoNinths.ExteriorE2.gridGeometry w (fun j => (hw j).le)
    (U := U) (Z := Z) hQ48 hell.le h.log_floor (hell.trans hfloor).le hHt s.hweights
  have hplane := _root_.AbcTwoNinths.ExteriorE2.orientedPlaneOfShortProjection
    (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M s.q s.hcop) hpivot.ne' v (hshape.symm ▸ hV)
    (by rw [hshape]; exact hline) w hw Q hell
    (_root_.AbcTwoNinths.ExteriorE2.kernelWeightedHeightGtLog s.q s.hprime s.hcop s.hinj hM) (hgeom 0 0).1 hshort
  dsimp only at hplane
  rw [hshape] at hplane
  obtain ⟨u, hu, z, hz, c, d, heq, hcd, hc, hd', hind, huℓ, hzℓ, hp, hcu, hdz⟩ := hplane
  have hlarge : 146 + 2 * ((Nat.log 2 g : ℕ) : ℝ) ≤ L := by
    linarith only [h.depth, _root_.AbcTwoNinths.ExteriorE2.generatorLossLe hgκ]
  exact _root_.AbcTwoNinths.ExteriorE2.excludeOrientedPlaneOnHigh s.q s.hprime s.hcop s.hinj
    V u z heq hu hz hind hdV hη le_rfl h.high hσ hκ h.modulus hQκ h.log_floor hmass
    hmod hlarge hcd hc hd' huℓ.le hzℓ.le hHt ((hgeom _ _).2 hp) hcu hdz

/--
For admissible `η` , tight modulus exclusion holds eventually at `cutoffBudget η` and margin
`(1 - 9 * η) / 32` .
-/
theorem tightModulusExclusion (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) :
    ∃ X : ℝ, _root_.AbcTwoNinths.ExteriorE2.TightModulusExclusion η (_root_.AbcTwoNinths.Statement.cutoffBudget η) ((1 - 9 * (η : ℝ)) / 32) X := by
  have hη' : (η : ℝ) < 1 / 9 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).2 hη.2
  have hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η (_root_.AbcTwoNinths.Statement.cutoffBudget η) := by
    refine ⟨?_, le_rfl⟩
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget _root_.AbcTwoNinths.Statement.highRate
    linarith
  exact _root_.AbcTwoNinths.ExteriorE2.tightModulusExclusionOfParameters hη hσ (by linarith)

/-- Proposition 4.1 of the paper. This is used in Section 4 of the paper. -/
theorem smallPrimeMassEventually :
    ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η → ∃ σ κ X : ℝ,
      _root_.AbcTwoNinths.Statement.admissibleCutoff η σ ∧ _root_.AbcTwoNinths.Statement.admissibleMargin η κ ∧ 0 ≤ X ∧
        ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t :=
  _root_.AbcTwoNinths.ExteriorE2.e2TailOfTightModulusExclusion _root_.AbcTwoNinths.ExteriorE2.tightModulusExclusion

end

end AbcTwoNinths.ExteriorE2
