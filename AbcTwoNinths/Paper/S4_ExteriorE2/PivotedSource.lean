/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.TripleKernel
public import AbcTwoNinths.Paper.S4_ExteriorE2.MaximalPrimePowerPivot
public import AbcTwoNinths.Paper.S4_ExteriorE2.SourceSupport
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison

/-!
# Pivoted Source

Constructs exponent coordinates with a distinguished pivot from deep divisibility of the side
with least radical. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.actualSource`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section







/-- The source index. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev SourceIndex (S : Finset ℕ) (p : S) := Unit ⊕ {i : S // i ≠ p}

/-- The source primes. This is used in the proof of Proposition 4.1 of the paper. -/
noncomputable def sourcePrimes (S : Finset ℕ) (p : S) : _root_.AbcTwoNinths.ExteriorE2.SourceIndex S p → ℕ :=
  Subtype.val ∘ _root_.AbcTwoNinths.ExteriorE2.pivotEquiv p

/-- The actual source. This is used in the proof of Proposition 4.1 of the paper. -/
structure ActualSource (t : _root_.AbcTwoNinths.Basic.Triple) (M L : ℕ) where
  S : Finset ℕ
  pivot : S
  E : _root_.AbcTwoNinths.ExteriorE2.SourceIndex S pivot → ℤ
  hprime : ∀ j, (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot j).Prime
  hinj : Function.Injective (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot)
  hcop : ∀ j, (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot j).Coprime M
  hkernel : E ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) hcop).ker
  hroof : 0 < E (.inl ())
  hmax : ∀ j, (E j).natAbs ≤ (E (.inl ())).natAbs
  hheight :
    let h := _root_.AbcTwoNinths.ExteriorE1.height (fun j => Real.log (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot j : ℝ)) (fun j => (E j : ℝ))
    t.logHeight ≤ h ∧ h ≤ 2 * t.logHeight
  hweights : (∑ j, Real.log (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot j : ℝ)) ≤ 3 * t.thirdLogRadical
  hsupport : S ⊆ (t.a * t.b * t.c).primeFactors
  hparts :
    let P := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).1 ^ 2
    let D := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).2 ^ 2
    let A := _root_.AbcTwoNinths.PolyCap.posPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E
    let B := _root_.AbcTwoNinths.PolyCap.negPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E
    (A = P ∧ B = D) ∨ (A = D ∧ B = P)
  hcongr : Nat.ModEq (M ^ L) (_root_.AbcTwoNinths.PolyCap.posPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E)
    (_root_.AbcTwoNinths.PolyCap.negPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E)
  hdepth : (M : ℤ) ^ L ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E : ℤ) -
    (_root_.AbcTwoNinths.PolyCap.negPartNat (_root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot) E : ℤ)

/-- The actual source.i. This is used in the proof of Proposition 4.1 of the paper. -/
abbrev ActualSource.i {t M L} (a : _root_.AbcTwoNinths.ExteriorE2.ActualSource t M L) := {i : a.S // i ≠ a.pivot}

/-- The actual source.q. This is used in the proof of Proposition 4.1 of the paper. -/
noncomputable abbrev ActualSource.q {t M L} (a : _root_.AbcTwoNinths.ExteriorE2.ActualSource t M L) :
    Unit ⊕ a.i → ℕ := _root_.AbcTwoNinths.ExteriorE2.sourcePrimes a.S a.pivot

/--
The weighted height is the maximum of the logarithms of the positive and negative monomial parts.
-/
theorem heightEqLogParts {J : Type*} [Fintype J]
    (q : J → ℕ) (hq : ∀ j, (q j).Prime) (e : J → ℤ) :
    _root_.AbcTwoNinths.ExteriorE1.height (fun j => Real.log (q j : ℝ)) (fun j => (e j : ℝ)) =
      max (Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℝ)) (Real.log (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℝ)) := by
  have hpos (b : J → ℤ) : Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q b : ℝ) =
      _root_.AbcTwoNinths.ExteriorE1.positiveWeight (fun j => Real.log (q j : ℝ)) (fun j => (b j : ℝ)) := by
    simp only [_root_.AbcTwoNinths.PolyCap.posPartNat, Nat.cast_prod, Nat.cast_pow, _root_.AbcTwoNinths.ExteriorE1.positiveWeight]
    rw [Real.log_prod (fun j _ => pow_ne_zero _ (by exact_mod_cast (hq j).ne_zero))]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.log_pow]
    by_cases h : 0 ≤ b j
    · have hR : 0 ≤ (b j : ℝ) := by exact_mod_cast h
      have hcast : ((b j).toNat : ℝ) = (b j : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h
      rw [max_eq_left hR, hcast, mul_comm]
    · have hR : (b j : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge h
      simp [max_eq_right hR, Int.toNat_eq_zero.mpr (le_of_not_ge h)]
  have hneg : (fun j => ((-e) j : ℝ)) = -(fun j => (e j : ℝ)) := by
    funext j
    simp
  rw [_root_.AbcTwoNinths.ExteriorE1.height, _root_.AbcTwoNinths.PolyCap.negPartNat, hpos, hpos, hneg]

/--
For an ordered triple whose minimum-radical side is divisible by `M ^ L` , with `M ≥ 3` and
`L > 0` , the squared source pair admits a pivoted exponent chart satisfying the height,
support, and congruence conditions in `ActualSource` .
-/
theorem actualSource (t : _root_.AbcTwoNinths.Basic.Triple) (hord : t.a ≤ t.b)
    {M L : ℕ} (hM : 3 ≤ M) (hL : 0 < L)
    (hd : M ^ L ∣ _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : Nonempty (_root_.AbcTwoNinths.ExteriorE2.ActualSource t M L) := by
  classical
  let s := _root_.AbcTwoNinths.Statement.minRadicalSide t
  let P := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 ^ 2
  let D := (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2
  let S := (P * D).primeFactors
  have hm : M ∣ _root_.AbcTwoNinths.Statement.sideValue t s := (dvd_pow_self M hL.ne').trans hd
  obtain ⟨hb2, hordPD⟩ := _root_.AbcTwoNinths.ExteriorE2.sourceOrderOfModulus t s hord (show 2 < M by omega) hm
  have hDP : D < P := Nat.pow_lt_pow_left hordPD (by decide)
  have hD : 0 < D := by
    change 0 < (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 ^ 2
    have hpos : 0 < (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 := by
      cases s <;> first | exact t.apos | exact t.bpos
    positivity
  obtain ⟨e, heP, heD, hc, hker⟩ := _root_.AbcTwoNinths.ExteriorE2.tripleSourceKernel t s hm hordPD.le
  change S → ℤ at e
  change _root_.AbcTwoNinths.PolyCap.posPartNat Subtype.val e = P at heP
  change _root_.AbcTwoNinths.PolyCap.negPartNat Subtype.val e = D at heD
  have hne : e ≠ 0 := by
    intro he
    rw [he] at heP heD
    simp [_root_.AbcTwoNinths.PolyCap.posPartNat, _root_.AbcTwoNinths.PolyCap.negPartNat] at heP heD
    omega
  obtain ⟨pivot, b, _, hb, hbpos, hbmax⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.orientMaxPivot (⊤ : AddSubgroup (S → ℤ)) e (by simp) hne
  let f := _root_.AbcTwoNinths.ExteriorE2.pivotEquiv pivot
  let q := _root_.AbcTwoNinths.ExteriorE2.sourcePrimes S pivot
  let E := b ∘ f
  have hcop (j : _root_.AbcTwoNinths.ExteriorE2.SourceIndex S pivot) : (q j).Coprime M := hc (f j)
  have hprime (j : _root_.AbcTwoNinths.ExteriorE2.SourceIndex S pivot) : (q j).Prime :=
    Nat.prime_of_mem_primeFactors (f j).property
  have hkernel : E ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker := by
    change b ∘ f ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker
    have he : e ∘ f ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker := hker pivot
    rcases hb with hb | hb
    · rw [hb]
      exact he
    · rw [hb]
      exact (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker.neg_mem he
  have hparts : (_root_.AbcTwoNinths.PolyCap.posPartNat q E = P ∧ _root_.AbcTwoNinths.PolyCap.negPartNat q E = D) ∨
      (_root_.AbcTwoNinths.PolyCap.posPartNat q E = D ∧ _root_.AbcTwoNinths.PolyCap.negPartNat q E = P) := by
    have h := _root_.AbcTwoNinths.ExteriorE2.partsReindex f Subtype.val b
    change _root_.AbcTwoNinths.PolyCap.posPartNat q E = _root_.AbcTwoNinths.PolyCap.posPartNat Subtype.val b ∧
      _root_.AbcTwoNinths.PolyCap.negPartNat q E = _root_.AbcTwoNinths.PolyCap.negPartNat Subtype.val b at h
    rw [h.1, h.2]
    rcases hb with hb | hb
    · rw [hb]
      exact Or.inl ⟨heP, heD⟩
    · rw [hb]
      exact Or.inr ⟨heD, by simpa only [_root_.AbcTwoNinths.PolyCap.negPartNat, neg_neg] using heP⟩
  have hdifference : M ^ L ∣ P - D := _root_.AbcTwoNinths.ExteriorE2.sourceSqDepth t s hd
  have hmod : Nat.ModEq (M ^ L) P D :=
    ((Nat.modEq_iff_dvd' hDP.le).2 hdifference).symm
  have hcongr : Nat.ModEq (M ^ L) (_root_.AbcTwoNinths.PolyCap.posPartNat q E) (_root_.AbcTwoNinths.PolyCap.negPartNat q E) := by
    rcases hparts with ⟨hP, hD'⟩ | ⟨hP, hD'⟩
    · simpa only [hP, hD'] using hmod
    · simpa only [hP, hD'] using hmod.symm
  refine ⟨{
    S := S
    pivot := pivot
    E := E
    hprime := hprime
    hinj := Subtype.val_injective.comp f.injective
    hcop := hcop
    hkernel := hkernel
    hroof := hbpos
    hmax := ?_
    hheight := ?_
    hweights := ?_
    hsupport := _root_.AbcTwoNinths.ExteriorE2.squaredSourceSupportSubset t s
    hparts := hparts
    hcongr := hcongr
    hdepth := by simpa only [Nat.cast_pow] using Nat.modEq_iff_dvd.1 hcongr.symm }⟩
  · intro j
    change (b (f j)).natAbs ≤ (b pivot).natAbs
    rcases hb with hb | hb
    · simpa only [hb] using hbmax (f j)
    · simpa only [hb, Pi.neg_apply, Int.natAbs_neg] using hbmax (f j)
  · rw [_root_.AbcTwoNinths.ExteriorE2.heightEqLogParts q hprime E]
    have hlog : Real.log (D : ℝ) ≤ Real.log (P : ℝ) :=
      Real.log_le_log (by exact_mod_cast hD) (by exact_mod_cast hDP.le)
    have hP : Real.log (P : ℝ) = 2 * Real.log ((_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 : ℝ) := by
      simp [P, Real.log_pow]
    have hm : max (Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q E : ℝ)) (Real.log (_root_.AbcTwoNinths.PolyCap.negPartNat q E : ℝ)) =
        Real.log (P : ℝ) := by
      rcases hparts with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · rw [hA, hB, max_eq_left hlog]
      · rw [hA, hB, max_eq_right hlog]
    rw [hm, hP]
    exact _root_.AbcTwoNinths.ExteriorE2.sourceSqHeight t s hord hb2
  · calc
      (∑ j, Real.log (q j : ℝ)) = ∑ i : S, Real.log (i : ℝ) :=
        Fintype.sum_equiv f _ _ (fun _ => rfl)
      _ = ∑ i ∈ S, Real.log (i : ℝ) := Finset.sum_coe_sort S (fun i : ℕ => Real.log (i : ℝ))
      _ ≤ 3 * t.thirdLogRadical := _root_.AbcTwoNinths.ExteriorE2.squaredSourceSupportWeight t s

end

end AbcTwoNinths.ExteriorE2
