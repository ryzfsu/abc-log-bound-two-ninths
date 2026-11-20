/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePlane
public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import AbcTwoNinths.Paper.S5_Selection.SelectedPrime
public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimeProjectionSeparation
public import AbcTwoNinths.Paper.S6_Diamond.PivotFirstCoordinates
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Selected prime and separated exponent lattice

Constructs the primitive source line in the signed exponent lattice and proves a uniform lower
bound for nonzero weighted projections. This is Proposition 6.1 of the paper.

## Main results
* `AbcTwoNinths.Diamond.lineOfPowerPrimitive`
* `AbcTwoNinths.Diamond.squareLtHeight`
* `AbcTwoNinths.Diamond.selectedDeterminantInputs`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

noncomputable section

section





/--
A lattice point collinear with a power-primitive vector having a nonzero coordinate is an integer power of that vector. This is used in Section 6 of the paper.
-/
theorem lineOfPowerPrimitive {J : Type*} (K : Subgroup (_root_.AbcTwoNinths.ExteriorE2.Exponents J))
    (s : K) (j : J) (hj : s.val.toAdd j ≠ 0)
    (hprim : ∀ (g : ℕ) (v : K), 0 < g → s = v ^ g → g = 1) :
    ∀ (w : K) (a : ℝ), (∀ i, (w.val.toAdd i : ℝ) = a * s.val.toAdd i) →
      ∃ c : ℤ, w = s ^ c := by
  let L : Subgroup K := {
    carrier := {v | ∀ i, v.val.toAdd i * s.val.toAdd j = v.val.toAdd j * s.val.toAdd i}
    one_mem' := by simp
    mul_mem' := by
      intro u v hu hv i
      change (u.val.toAdd i + v.val.toAdd i) * s.val.toAdd j =
        (u.val.toAdd j + v.val.toAdd j) * s.val.toAdd i
      rw [add_mul, add_mul, hu i, hv i]
    inv_mem' := by
      intro u hu i
      change -u.val.toAdd i * s.val.toAdd j = -u.val.toAdd j * s.val.toAdd i
      rw [neg_mul, neg_mul, hu i] }
  let coord : L →* Multiplicative ℤ := {
    toFun := fun u => Multiplicative.ofAdd (u.val.val.toAdd j)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective coord := by
    intro u v h
    have he : u.val.val.toAdd j = v.val.val.toAdd j := Multiplicative.ofAdd.injective h
    apply Subtype.ext
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hu := u.property i
    have hv := v.property i
    exact mul_right_cancel₀ hj (hu.trans (he ▸ hv.symm))
  have : IsCyclic L := isCyclic_of_injective coord hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L)
  let S : L := ⟨s, fun _ => mul_comm _ _⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg S)
  have hs : g.val ^ n = s := congrArg Subtype.val hn
  have hsne : s ≠ 1 := by
    intro h
    exact hj (by simp [h])
  have hgen : ∃ d : ℤ, g.val = s ^ d := by
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
    · rw [hm, zpow_natCast] at hs
      have hp : 0 < m := by
        by_contra! h
        have hm0 : m = 0 := by omega
        exact hsne (by simpa [hm0] using hs.symm)
      have hm1 := hprim m g.val hp hs.symm
      exact ⟨1, by simpa [hm1] using hs⟩
    · rw [hm, zpow_neg, zpow_natCast, ← inv_pow] at hs
      have hp : 0 < m := by
        by_contra! h
        have hm0 : m = 0 := by omega
        exact hsne (by simpa [hm0] using hs.symm)
      have hm1 := hprim m g.val⁻¹ hp hs.symm
      have hi : g.val⁻¹ = s := by simpa [hm1] using hs
      exact ⟨-1, by simpa using congrArg Inv.inv hi⟩
  intro w a ha
  have hw : w ∈ L := by
    intro i
    exact_mod_cast (show (w.val.toAdd i : ℝ) * (s.val.toAdd j : ℝ) =
      (w.val.toAdd j : ℝ) * (s.val.toAdd i : ℝ) by rw [ha i, ha j]; ring)
  let W : L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (hg W)
  obtain ⟨d, hd⟩ := hgen
  have hc' : g.val ^ c = w := congrArg Subtype.val hc
  exact ⟨d * c, by rw [zpow_mul, ← hd, hc']⟩

/--
Beyond a common threshold the selected source has a nonzero maximal coordinate controlling the height and generates its lattice line.
-/
theorem selectedPeakAtCommonOnset {η : ℚ} {κ : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) :
    ∃ X : ℝ, 0 < X ∧ ∀ (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors),
    t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t →
    (1 - 2 * κ) * t.logHeight ≤ (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p →
    let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let old := _root_.AbcTwoNinths.ExteriorE2.base side.n side.d
    let pr := _root_.AbcTwoNinths.ExteriorE2.prime side.n side.d
    let av := _root_.AbcTwoNinths.Selection.avoidOfSide side
    let K := _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old pr av
    ∃ (s : K) (j : _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d),
      s.val = _root_.AbcTwoNinths.ExteriorE2.vec side.n side.d ∧ s.val.toAdd j ≠ 0 ∧
      t.logHeight ≤ 3 * t.thirdLogRadical * |(s.val.toAdd j : ℝ)| ∧
      (∀ i, (s.val.toAdd i).natAbs ≤ (s.val.toAdd j).natAbs) ∧
      (∀ (w : K) (a : ℝ), (∀ i, (w.val.toAdd i : ℝ) = a * s.val.toAdd i) →
        ∃ c : ℤ, w = s ^ c) ∧
      (_root_.AbcTwoNinths.Diamond.character old pr av s : ℚ) = _root_.AbcTwoNinths.Statement.selectedSource t := by
  classical
  obtain ⟨X, hX, select⟩ := _root_.AbcTwoNinths.Selection.selectedPrimeRoofBounds hη hκ
  refine ⟨X, hX, ?_⟩
  intro t p _ _ hp ho hh he hm side old pr av K
  obtain ⟨s, hs, hprim, hpeak⟩ := select t p hp ho hh he hm
  let f (i : _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d) := (s.val.toAdd i).natAbs
  let P := Finset.univ.sup f
  have hx : 0 < t.thirdLogRadical := hX.trans_le hh.1
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh.2
  have heta : 0 < (η : ℝ) := by exact_mod_cast hη.1
  have hcoef : (1 : ℝ) ≤ 2 - 2 * κ := by linarith [hκ.2]
  have hpeak' : (2 - 2 * κ) * t.logHeight ≤ (P : ℝ) * (3 * t.thirdLogRadical) :=
    (div_le_iff₀ (by positivity : 0 < 3 * t.thirdLogRadical)).mp hpeak
  have hbound : t.logHeight ≤ (P : ℝ) * (3 * t.thirdLogRadical) :=
    (by simpa using mul_le_mul_of_nonneg_right hcoef hH.le : t.logHeight ≤ (2 - 2 * κ) * t.logHeight).trans hpeak'
  have hP : (0 : ℝ) < P := by
    by_contra! hn
    linarith [mul_nonpos_of_nonpos_of_nonneg hn (show (0 : ℝ) ≤ 3 * t.thirdLogRadical by positivity)]
  have hnonempty : (Finset.univ : Finset (_root_.AbcTwoNinths.ExteriorE2.Support side.n side.d)).Nonempty := by
    by_contra h
    have hzero : P = 0 := by
      change (Finset.univ : Finset (_root_.AbcTwoNinths.ExteriorE2.Support side.n side.d)).sup f = 0
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty]
      rfl
    simp [hzero] at hP
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ hnonempty f
  change P = (s.val.toAdd j).natAbs at hj
  have hjne : s.val.toAdd j ≠ 0 := by
    intro h
    rw [hj, h] at hP
    norm_num at hP
  have hsbound : t.logHeight ≤ 3 * t.thirdLogRadical * |(s.val.toAdd j : ℝ)| := by
    rw [hj, Nat.cast_natAbs, Int.cast_abs] at hbound
    simpa only [mul_comm] using hbound
  obtain ⟨s', hs', hsource, _⟩ := _root_.AbcTwoNinths.Selection.selectedNative t hp
  have hEq : s = s' := Subtype.ext (hs.trans hs'.symm)
  exact ⟨s, j, hs, hjne, hsbound, fun i => hj ▸ Finset.le_sup (f := f) (Finset.mem_univ i),
    _root_.AbcTwoNinths.Diamond.lineOfPowerPrimitive _ s j hjne hprim, hEq ▸ hsource⟩

/--
The square of the log-radical parameter is below the height on the high tail starting at 64. This is used in Section 6 of the paper.
-/
theorem squareLtHeight {η : ℚ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) {t : _root_.AbcTwoNinths.Basic.Triple}
    (hh : _root_.AbcTwoNinths.Statement.High η 64 t) : t.thirdLogRadical ^ 2 < t.logHeight := by
  have hx : 0 ≤ t.thirdLogRadical := by linarith [hh.1]
  have hη' : (η : ℝ) < 1 / 9 := by simpa using (Rat.cast_lt (K := ℝ)).mpr hη.2
  have hr : (2 / 3 : ℝ) ≤ _root_.AbcTwoNinths.Statement.highRate η := by unfold _root_.AbcTwoNinths.Statement.highRate; linarith
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ (2 / 3 : ℝ) * t.thirdLogRadical by positivity) 4
  norm_num [Finset.sum_range_succ] at he
  have hpoly : t.thirdLogRadical^2 < Real.exp ((2 / 3 : ℝ) * t.thirdLogRadical) := by
    nlinarith [mul_nonneg (sq_nonneg t.thirdLogRadical) (sub_nonneg.mpr hh.1)]
  exact hpoly.trans_le ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr hx)).trans hh.2)

/--
Each prime in the support of the selected rational source divides the radical of the ordered triple.
-/
theorem selectedOldDvd (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (ho : t.a ≤ t.b) :
    let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    ∀ i : _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d, _root_.AbcTwoNinths.ExteriorE2.base side.n side.d i ∣ t.radical := by
  intro side i
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hn : t.a * t.b * t.c ≠ 0 :=
    mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc.ne'
  have hd := (_root_.AbcTwoNinths.PolyCap.selectedSideProjection t hp ho).2.2.2
  let q : ℕ := i.val
  have hi : q ∈ (side.n * side.d).primeFactors := by
    rw [Nat.primeFactors_mul side.hn side.hd]
    exact i.property
  exact Finset.dvd_prod_of_mem id (Nat.primeFactors_mono hd hn hi)

/-- Each prime dividing the least-radical side divides the radical of the triple. -/
theorem contactDvdRadical (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) : p ∣ t.radical := by
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hn : t.a * t.b * t.c ≠ 0 :=
    mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc.ne'
  have hside : _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t) ∣ t.a * t.b * t.c := by
    cases _root_.AbcTwoNinths.Statement.minRadicalSide t
    · exact ⟨t.b * t.c, by change t.a * t.b * t.c = t.a * (t.b * t.c); ring⟩
    · exact ⟨t.a * t.c, by change t.a * t.b * t.c = t.b * (t.a * t.c); ring⟩
    · exact ⟨t.a * t.b, by change t.a * t.b * t.c = t.c * (t.a * t.b); ring⟩
  exact Finset.dvd_prod_of_mem id (Nat.primeFactors_mono hside hn hp)



/--
Old lattice data for a single contact prime selected on the common high tail. This is used in Section 6 of the paper.
-/
structure SelectedDeterminantInput {I : Type} [Fintype I] (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ)
    [Fact p.Prime] [Fact (2 < p)] (η : ℚ) {κ : ℝ} (old : Unit ⊕ I → ℕ) where
  oldPrime : ∀ i, (old i).Prime
  oldAvoid : ∀ i, p ≠ old i
  source : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old oldPrime oldAvoid
  oldInjective : Function.Injective old
  oldDvd : ∀ i, old i ∣ t.radical
  contactDvd : p ∣ t.radical
  radicalPos : 0 < t.radical
  logRadical : Real.log (t.radical : ℝ) = 3 * t.thirdLogRadical
  shell : _root_.AbcTwoNinths.ExteriorE2.Admissible (p : ℝ) t.logHeight (η : ℝ) t.thirdLogRadical
  roofNonzero : source.val.toAdd (.inl ()) ≠ 0
  roofBound : t.logHeight ≤ 3 * t.thirdLogRadical * |(source.val.toAdd (.inl ()) : ℝ)|
  roofPeak : ∀ i, (source.val.toAdd i).natAbs ≤ (source.val.toAdd (.inl ())).natAbs
  line : ∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old oldPrime oldAvoid) (a : ℝ),
    (∀ i, (w.val.toAdd i : ℝ) = a * source.val.toAdd i) → ∃ c : ℤ, w = source ^ c
  separation : ∀ w ∈ (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old oldPrime oldAvoid).toAdditive.ker,
    _root_.AbcTwoNinths.ExteriorE2.cost (fun i => Real.log (old (.inr i) : ℝ)) (_root_.AbcTwoNinths.ExteriorE2.project source.val.toAdd w) <
      2 * t.thirdLogRadical / Real.log t.thirdLogRadical → _root_.AbcTwoNinths.ExteriorE2.project source.val.toAdd w = 0
  sourceCharacter : (_root_.AbcTwoNinths.Diamond.character old oldPrime oldAvoid source : ℚ) = _root_.AbcTwoNinths.Statement.selectedSource t
  squareLtHeight : t.thirdLogRadical ^ 2 < t.logHeight
  logX : (10 ^ 9 : ℝ) ≤ Real.log t.thirdLogRadical
  logP : t.thirdLogRadical / 2 ≤ Real.log p
  depth : (1 - 2 * κ) * t.logHeight ≤
    (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p

/-- Proposition 6.1 of the paper. -/
theorem selectedDeterminantInputs {η : ℚ} {σ κ : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) :
    ∃ X : ℝ, 0 < X ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b →
      _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t →
      ∃ (p : ℕ) (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
        (hp5 : 5 ≤ p),
        t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (p : ℝ) ∧
        (∀ q ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
          t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (q : ℝ) → q = p) ∧
        letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
        letI : Fact (2 < p) := ⟨by omega⟩
        let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
        ∃ j : _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d,
          Nonempty (_root_.AbcTwoNinths.Diamond.SelectedDeterminantInput (κ := κ) t p η (_root_.AbcTwoNinths.ExteriorE2.base side.n side.d ∘ _root_.AbcTwoNinths.Diamond.roofFirst j)) := by
  classical
  obtain ⟨Y, hY, peak⟩ := _root_.AbcTwoNinths.Diamond.selectedPeakAtCommonOnset hη hκ
  let cut := max 128 (16 * (1 + 6 / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))) / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)
  let onset := max (max (max Y 64) (Real.exp (10 ^ 9))) (max 1 cut)
  refine ⟨onset, hY.trans_le (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), ?_⟩
  intro t ho hh h1 h2
  obtain ⟨p, hp, hc, hu, hd, hadm, hh16, hlog, hell, hp5, hhalf, _⟩ :=
    _root_.AbcTwoNinths.Diamond.selectedOnsetShellSupply (X := max Y 64) hη hσ hκ ho hh h1 h2
  refine ⟨p, hp, hp5, hc, hu, ?_⟩
  dsimp only
  let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  let _ : Fact (2 < p) := ⟨by omega⟩
  let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
  have hsmall : max Y 64 ≤ t.thirdLogRadical := ((le_max_left _ _).trans (le_max_left _ _)).trans hh.1
  obtain ⟨s, j, hval, hroof, hbound, hpeak, hline, hchar⟩ :=
    peak t p hp ho ⟨(le_max_left _ _).trans hsmall, hh.2⟩ h1 hd
  let e := _root_.AbcTwoNinths.Diamond.roofFirst j
  let old := _root_.AbcTwoNinths.ExteriorE2.base side.n side.d
  let pr := _root_.AbcTwoNinths.ExteriorE2.prime side.n side.d
  let av := _root_.AbcTwoNinths.Selection.avoidOfSide side
  let v := _root_.AbcTwoNinths.Diamond.reindexLattice e old pr av s
  have hr : v.val.toAdd (.inl ()) ≠ 0 := hroof
  have hsep := _root_.AbcTwoNinths.Diamond.selectedProjectedSeparation t hp hadm.hx.le
    (by linarith) (_root_.AbcTwoNinths.Diamond.selectedShearBoundOf t hp hη hσ hκ ho hc
      hh16 hlog hell hp5 hhalf) e
    (show (_root_.AbcTwoNinths.ExteriorE2.vec side.n side.d).toAdd (e (.inl ())) ≠ 0 by rw [← hval]; exact hr)
  have hR : 0 < t.radical := Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hxR : Real.log (t.radical : ℝ) = 3 * t.thirdLogRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical
    ring
  refine ⟨j, ⟨⟨fun i => pr (e i), fun i => av (e i), v,
    Subtype.val_injective.comp e.injective, fun i => _root_.AbcTwoNinths.Diamond.selectedOldDvd t hp ho (e i),
    _root_.AbcTwoNinths.Diamond.contactDvdRadical t hp, hR, hxR, hadm, hr, hbound, fun i => hpeak (e i),
    _root_.AbcTwoNinths.Diamond.reindexLine e old pr av s hline, ?_, ?_,
    _root_.AbcTwoNinths.Diamond.squareLtHeight hη ⟨(le_max_right _ _).trans hsmall, hh.2⟩, hlog, hell, hd⟩⟩⟩
  · rw [← hval] at hsep
    exact hsep
  · rw [_root_.AbcTwoNinths.Diamond.reindexCharacter]
    exact hchar

end

end
end AbcTwoNinths.Diamond
