/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RoofCovolume
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice
public import AbcTwoNinths.Paper.S4_ExteriorE2.ProjectedMass
public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeSupply
public import AbcTwoNinths.Paper.S4_ExteriorE2.VolumeSecondMoment
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Residue Lattice

Projects the exponent lattice along the source direction, constructs a fundamental domain for the
projected kernel, and defines the weighted norm. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.existsSourceBasis`
* `AbcTwoNinths.ExteriorE2.fundamentalData`
-/

@[expose] public section
namespace AbcTwoNinths.ExteriorE2

noncomputable section

open MeasureTheory Module Matrix Set
open scoped ENNReal Pointwise

section



variable {I : Type*} [Fintype I] [DecidableEq I]

/--
An integral exponent vector with one distinguished roof coordinate. This is used in the proof of Proposition 4.1 of the paper.
-/
abbrev Old (I : Type*) := (Unit ⊕ I) → ℤ
/--
Real coordinates indexed by the exponents other than the roof coordinate. This is used in the proof of Proposition 4.1 of the paper.
-/
abbrev Coord (I : Type*) := I → ℝ

section Coordinates

variable {G : Type*} [AddCommGroup G] [Finite G] (red : _root_.AbcTwoNinths.ExteriorE2.Old I →+ G)

/--
The integral submodule obtained by projecting the kernel of the residue homomorphism. This is used in the proof of Proposition 4.1 of the paper.
-/
def projected (s : _root_.AbcTwoNinths.ExteriorE2.Old I) : Submodule ℤ (_root_.AbcTwoNinths.ExteriorE2.Coord I) :=
  red.ker.toIntSubmodule.map (_root_.AbcTwoNinths.Basic.roofProjection (s (.inl ())) (fun j => s (.inr j)))

/--
Subtract the source direction using the roof coordinate and retain the other coordinates. This is used in the proof of Proposition 4.1 of the paper.
-/
def project (s : _root_.AbcTwoNinths.ExteriorE2.Old I) : _root_.AbcTwoNinths.ExteriorE2.Old I →ₗ[ℤ] _root_.AbcTwoNinths.ExteriorE2.Coord I :=
  _root_.AbcTwoNinths.Basic.roofProjection (s (.inl ())) (fun j => s (.inr j))

omit [Fintype I] [DecidableEq I] [Finite G] in
/-- The projected kernel consists of the projections of integral kernel elements. -/
theorem memProjected (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (z : _root_.AbcTwoNinths.ExteriorE2.Coord I) :
    z ∈ _root_.AbcTwoNinths.ExteriorE2.projected red s ↔ ∃ w ∈ red.ker, _root_.AbcTwoNinths.ExteriorE2.project s w = z := Iff.rfl

omit [Fintype I] [DecidableEq I] in
/-- A source with nonzero roof coordinate projects to zero along itself. -/
theorem projectSource (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (hs : s (.inl ()) ≠ 0) : _root_.AbcTwoNinths.ExteriorE2.project s s = 0 := by
  ext j
  change (s (.inr j) : ℝ) - (s (.inl ()) : ℝ) / s (.inl ()) * s (.inr j) = 0
  simp [hs]

/--
A nonzero primitive element of a finite-image residue kernel extends to an integral basis with that element first. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem existsSourceBasis (s : red.ker) (hs : s ≠ 0)
    (primitive : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a) :
    ∃ b : Basis (Unit ⊕ I) ℤ red.ker, b (.inl ()) = s := by
  classical
  let K := red.ker.toIntSubmodule
  let s' : K := s
  have hs' : s' ≠ 0 := hs
  have hfin : Finite (_root_.AbcTwoNinths.ExteriorE2.Old I ⧸ K) :=
    Finite.of_equiv red.range (QuotientAddGroup.quotientKerEquivRange red).toEquiv.symm
  have hrank : Module.finrank ℤ K = Fintype.card (Unit ⊕ I) :=
    (Submodule.finiteQuotient_iff K).mp hfin |>.trans
      (Module.finrank_fintype_fun_eq_card ℤ)
  let b0 := (Module.Free.chooseBasis ℤ K).reindex
    (Fintype.equivOfCardEq ((Module.finrank_eq_card_chooseBasisIndex ℤ K).symm.trans hrank))
  let N : Submodule ℤ K := ℤ ∙ s'
  obtain ⟨n, sn⟩ := N.smithNormalForm b0
  let e := LinearEquiv.toSpanNonzeroSingleton ℤ K s' hs'
  have hr : n = 1 := by
    rw [← Fintype.card_fin n]
    rw [← Module.finrank_eq_card_basis sn.bN, ← e.finrank_eq, Module.finrank_self]
  let j : Fin n := ⟨0, by omega⟩
  have hbN : (sn.bN j : K) = sn.a j • sn.bM (sn.f j) := sn.snf j
  have hel : ∀ i : Fin n, i = j := fun i => Fin.ext (by have := i.isLt; omega)
  let ss : N := ⟨s', Submodule.mem_span_singleton_self s'⟩
  have ha : (sn.bN.repr ss j : ℤ) • sn.bN j = ss := by
    conv_rhs => rw [← sn.bN.sum_repr ss]
    rw [Finset.sum_eq_single j (fun i _ hi => (hi (hel i)).elim)
      (fun h => (h (Finset.mem_univ j)).elim)]
  have ha' : (sn.bN.repr ss j * sn.a j) • sn.bM (sn.f j) = s' := by
    have h := congrArg Subtype.val ha
    change (sn.bN.repr ss j : ℤ) • (sn.bN j : K) = s' at h
    rwa [hbN, smul_smul] at h
  let scale (i : Unit ⊕ I) : ℤ := if i = sn.f j then sn.bN.repr ss j * sn.a j else 1
  have hscale (i : Unit ⊕ I) : IsUnit (scale i) := by
    by_cases h : i = sn.f j
    · simpa [scale, h] using primitive _ _ ha'
    · simp [scale, h]
  have hh : ∃ b : Basis (Unit ⊕ I) ℤ K, b (.inl ()) = s' := by
    refine ⟨(sn.bM.isUnitSMul hscale).reindex (Equiv.swap (.inl ()) (sn.f j)), ?_⟩
    rw [Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left, Basis.isUnitSMul_apply]
    simpa only [scale, ite_eq_left rfl] using ha'
  exact hh

/--
A kernel basis beginning with the source yields a measurable fundamental domain of volume equal to the image order divided by the absolute roof coordinate. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem fundamentalData (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (hs : s (.inl ()) ≠ 0)
    (b : Basis (Unit ⊕ I) ℤ red.ker) (hb : (b (.inl ()) : _root_.AbcTwoNinths.ExteriorE2.Old I) = s) :
    ∃ D : Set (_root_.AbcTwoNinths.ExteriorE2.Coord I), IsAddFundamentalDomain (_root_.AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup D volume ∧
      MeasurableSet D ∧ volume D < ⊤ ∧
      volume.real D = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)| := by
  let k := s (.inl ())
  let v : I → ℤ := fun i => s (.inr i)
  let c : I → ℤ := fun i => (b (.inr i) : _root_.AbcTwoNinths.ExteriorE2.Old I) (.inl ())
  let Y : Matrix I I ℤ := fun i j => (b (.inr i) : _root_.AbcTwoNinths.ExteriorE2.Old I) (.inr j)
  let P := _root_.AbcTwoNinths.Basic.projectRows (k : ℝ) (fun i => (v i : ℝ)) (fun i => (c i : ℝ)) (Y.map Int.cast)
  have hblock : Matrix.of (fun i => (b i : _root_.AbcTwoNinths.ExteriorE2.Old I)) = _root_.AbcTwoNinths.Basic.roofBlock k v c Y := by
    ext (i | i) (j | j)
    · cases i; cases j; exact congrFun hb (.inl ())
    · cases i; exact congrFun hb (.inr j)
    · cases j; rfl
    · rfl
  have hrow (i : I) : _root_.AbcTwoNinths.ExteriorE2.project s (b (.inr i)) = P i := by
    ext j
    rfl
  have hspan : _root_.AbcTwoNinths.ExteriorE2.projected red s = Submodule.span ℤ (Set.range (fun i => P i)) := by
    have hold : Submodule.span ℤ (Set.range (fun i => (b i : _root_.AbcTwoNinths.ExteriorE2.Old I))) =
        red.ker.toIntSubmodule := by
      let b' : Basis (Unit ⊕ I) ℤ red.ker.toIntSubmodule := b
      change Submodule.span ℤ (Set.range (red.ker.toIntSubmodule.subtype ∘ b')) = _
      rw [Set.range_comp, ← Submodule.map_span, b'.span_eq, Submodule.map_top, Submodule.range_subtype]
    change (red.ker.toIntSubmodule.map (_root_.AbcTwoNinths.ExteriorE2.project s)) = _
    rw [← hold, Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i | i, rfl⟩
      · cases i
        change _root_.AbcTwoNinths.ExteriorE2.project s (b (.inl ())) ∈ Submodule.span ℤ (Set.range (fun i => P i))
        rw [hb, _root_.AbcTwoNinths.ExteriorE2.projectSource s hs]
        exact Submodule.zero_mem _
      · simp only [Function.comp_apply, hrow]
        exact Submodule.subset_span (Set.mem_range_self i)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨.inr i, hrow i⟩
  have hcast : (_root_.AbcTwoNinths.Basic.roofBlock k v c Y).map (Int.cast : ℤ → ℝ) =
      _root_.AbcTwoNinths.Basic.roofBlock (k : ℝ) (fun i => (v i : ℝ)) (fun i => (c i : ℝ))
        (Y.map (Int.cast : ℤ → ℝ)) := by
    ext (i | i) (j | j) <;> rfl
  have hval : |P.det| = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)| := by
    dsimp only [P]
    rw [_root_.AbcTwoNinths.Basic.absProject _ (by exact_mod_cast hs), ← hcast, ← Int.cast_det, _root_.AbcTwoNinths.Basic.indexOld red b, hblock]
    simp [k, ← Int.cast_abs]
  have hpos : (0 : ℝ) < Nat.card red.range := by exact_mod_cast (Nat.card_pos (α := red.range))
  have hn : P.det ≠ 0 := abs_pos.mp (hval ▸ div_pos hpos (abs_pos.mpr (by exact_mod_cast hs)))
  let pb := basisOfLinearIndependentOfCardEqFinrank' (fun i => P i)
    (Matrix.linearIndependent_rows_of_det_ne_zero hn) (Module.finrank_fintype_fun_eq_card ℝ).symm
  have hpb : ⇑pb = fun i => P i := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  refine ⟨ZSpan.fundamentalDomain pb, ?_, ZSpan.fundamentalDomain_measurableSet pb, ?_, ?_⟩
  · rw [hspan, ← hpb]
    exact ZSpan.isAddFundamentalDomain' pb volume
  · rw [ZSpan.volume_fundamentalDomain]
    exact ENNReal.ofReal_lt_top
  · rw [ZSpan.volume_real_fundamentalDomain, hpb]
    exact hval

end Coordinates

/--
Sum the absolute coordinates multiplied by their respective weights. This is used in the proof of Proposition 4.1 of the paper.
-/
def cost (weight : I → ℝ) (z : _root_.AbcTwoNinths.ExteriorE2.Coord I) : ℝ := ∑ j, weight j * |z j|

/--
The open sublevel set of weighted coordinate cost around a given center. This is used in the proof of Proposition 4.1 of the paper.
-/
def ball (weight : I → ℝ) (center : _root_.AbcTwoNinths.ExteriorE2.Coord I) (r : ℝ) : Set (_root_.AbcTwoNinths.ExteriorE2.Coord I) :=
  {z | _root_.AbcTwoNinths.ExteriorE2.cost weight (z - center) < r}

omit [DecidableEq I] in
/-- Every strict weighted coordinate ball is open. -/
theorem ballOpen (weight : I → ℝ) (center : _root_.AbcTwoNinths.ExteriorE2.Coord I) (r : ℝ) :
    IsOpen (_root_.AbcTwoNinths.ExteriorE2.ball weight center r) := by
  apply isOpen_lt _ continuous_const
  change Continuous (fun z : _root_.AbcTwoNinths.ExteriorE2.Coord I => ∑ j, weight j * |z j - center j|)
  exact continuous_finsetSum Finset.univ fun j _ =>
    (continuous_const : Continuous fun _ : _root_.AbcTwoNinths.ExteriorE2.Coord I => weight j).mul
      (((continuous_apply j).sub (continuous_const : Continuous fun _ : _root_.AbcTwoNinths.ExteriorE2.Coord I => center j)).abs)

omit [DecidableEq I] in
/-- For nonnegative weights the cost of a difference is at most the sum of the costs. -/
theorem costSubLe (weight : I → ℝ) (hweight : ∀ j, 0 ≤ weight j) (a b : _root_.AbcTwoNinths.ExteriorE2.Coord I) :
    _root_.AbcTwoNinths.ExteriorE2.cost weight (a - b) ≤ _root_.AbcTwoNinths.ExteriorE2.cost weight a + _root_.AbcTwoNinths.ExteriorE2.cost weight b := by
  simp only [_root_.AbcTwoNinths.ExteriorE2.cost, Pi.sub_apply, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_sub _ _) (hweight j)

omit [DecidableEq I] in
/--
Under separation at radius r, a projected kernel translation between points of the same open half-radius ball is zero.
-/
theorem ballOrbitInjective {G : Type*} [AddCommGroup G] (red : _root_.AbcTwoNinths.ExteriorE2.Old I →+ G)
    (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j) (center : _root_.AbcTwoNinths.ExteriorE2.Coord I) (r : ℝ)
    (hshort : ∀ w ∈ red.ker, _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project s w) < r → _root_.AbcTwoNinths.ExteriorE2.project s w = 0) :
    ∀ a ∈ _root_.AbcTwoNinths.ExteriorE2.ball weight center (r / 2), ∀ b ∈ _root_.AbcTwoNinths.ExteriorE2.ball weight center (r / 2),
      ∀ l : (_root_.AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup, l +ᵥ a = b → l = 0 := by
  intro a ha b hb l hl
  change (l : _root_.AbcTwoNinths.ExteriorE2.Coord I) + a = b at hl
  change _root_.AbcTwoNinths.ExteriorE2.cost weight (a - center) < r / 2 at ha
  change _root_.AbcTwoNinths.ExteriorE2.cost weight (b - center) < r / 2 at hb
  obtain ⟨w, hwr, heq⟩ := (_root_.AbcTwoNinths.ExteriorE2.memProjected red s _).mp l.property
  have hdiff : (l : _root_.AbcTwoNinths.ExteriorE2.Coord I) = (b - center) - (a - center) := by rw [← hl]; abel
  have horbit : _root_.AbcTwoNinths.ExteriorE2.cost weight (l : _root_.AbcTwoNinths.ExteriorE2.Coord I) < r := by
    rw [hdiff]
    exact (_root_.AbcTwoNinths.ExteriorE2.costSubLe weight hw _ _).trans_lt (by linarith)
  apply Subtype.ext
  exact heq.symm.trans (hshort w hwr (by rwa [heq]))

omit [DecidableEq I] in
/-- Translating a weighted coordinate ball preserves its real volume. -/
theorem ballMassEq (weight : I → ℝ) (center : _root_.AbcTwoNinths.ExteriorE2.Coord I) (r : ℝ) :
    (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight center r) =
      volume.real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 r) := by
  have hset : (fun a : _root_.AbcTwoNinths.ExteriorE2.Coord I => a - center) ⁻¹' _root_.AbcTwoNinths.ExteriorE2.ball weight 0 r = _root_.AbcTwoNinths.ExteriorE2.ball weight center r := by
    ext a
    simp [_root_.AbcTwoNinths.ExteriorE2.ball]
  rw [← hset]
  exact (measurePreserving_sub_right volume center).measureReal_preimage
    (_root_.AbcTwoNinths.ExteriorE2.ballOpen weight 0 r).measurableSet.nullMeasurableSet



/--
Reduce the prime monomial modulo an avoided prime and take its residue class modulo sign in additive notation. This is used in the proof of Proposition 4.1 of the paper.
-/
def residueLatticeReduction {p : ℕ} [Fact p.Prime] (base : Unit ⊕ I → ℕ)
    (prime : ∀ i, (base i).Prime) (avoid : ∀ i, p ≠ base i) :
    _root_.AbcTwoNinths.ExteriorE2.Old I →+ Additive (_root_.AbcTwoNinths.ExteriorE2.Label p) :=
  (_root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid)).toAdditive

/-- At an odd prime the subgroup of signs has order two. -/
theorem signsCard (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Nat.card (_root_.AbcTwoNinths.ExteriorE2.signs p) = 2 := by
  change Nat.card ↥({u : (ZMod p)ˣ | u = 1 ∨ u = -1} : Set (ZMod p)ˣ) = 2
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_pair _root_.AbcTwoNinths.ExteriorE2.minusNeOne.symm

/-- At an odd prime p the signed residue group has real cardinality (p - 1)/2. -/
theorem labelCardReal (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    (Nat.card (_root_.AbcTwoNinths.ExteriorE2.Label p) : ℝ) = ((p : ℝ) - 1) / 2 := by
  have h := (_root_.AbcTwoNinths.ExteriorE2.signs p).card_mul_index
  rw [_root_.AbcTwoNinths.ExteriorE2.signsCard, Subgroup.index_eq_card, Nat.card_eq_fintype_card (α := (ZMod p)ˣ),
    ZMod.card_units] at h
  have hh : (2 : ℝ) * Nat.card (_root_.AbcTwoNinths.ExteriorE2.Label p) = (p : ℝ) - 1 := by
    have hp : 1 ≤ p := Nat.Prime.one_le Fact.out
    exact_mod_cast h
  linarith

end

end
end AbcTwoNinths.ExteriorE2
