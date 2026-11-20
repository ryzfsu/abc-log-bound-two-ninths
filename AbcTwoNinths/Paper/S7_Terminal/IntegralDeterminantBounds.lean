/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantSource
public import AbcTwoNinths.Paper.S7_Terminal.IntegralJoin
public import AbcTwoNinths.Paper.S7_Terminal.InterpolationMinorNonvanishing
public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantBounds

/-!
# Integral Determinant Bounds

A single nonzero integral interpolation determinant satisfies both the archimedean height upper
bound and the p-adic valuation lower bound. This is Proposition 7.1 of the paper.

## Main results
* `AbcTwoNinths.Terminal.terminalBounds`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section


variable {p : ℕ} [Fact p.Prime]

/-- The lift unit. This is used in Section 7 of the paper. -/
private noncomputable def liftUnit (q : ℚˣ) (h : _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (q : ℚ)) : ℤ_[p]ˣ :=
  ((PadicInt.isUnit_iff (z := ⟨((q : ℚ) : ℚ_[p]), (_root_.AbcTwoNinths.Basic.principalNorm h).le⟩)).mpr
    (_root_.AbcTwoNinths.Basic.principalNorm h)).unit

private theorem liftCast (q : ℚˣ) (h : _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (q : ℚ)) :
    (((liftUnit q h : ℤ_[p]) : ℚ_[p])) = (q : ℚ) := by
  unfold liftUnit
  exact congrArg (fun u : ℤ_[p] => (u : ℚ_[p])) (IsUnit.unit_spec _)

/--
A principal plane character admits integral unit generators with the prescribed divisibility in the first coordinate.
-/
theorem nativeLocal (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter)
    (hp : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s))
    (m : ℕ) (hm : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1,0) - 1)) :
    ∃ z a : ℤ_[p]ˣ, (p : ℤ_[p]) ^ m ∣ (z : ℤ_[p]) - 1 ∧
      (p : ℤ_[p]) ∣ (a : ℤ_[p]) - 1 ∧
      ∀ s : _root_.AbcTwoNinths.Terminal.Site, ((↑(z ^ s.1 * a ^ s.2) : ℤ_[p]) : ℚ_[p]) = (_root_.AbcTwoNinths.Terminal.value γ s : ℚ_[p]) := by
  let L (s : _root_.AbcTwoNinths.Terminal.Site) := liftUnit (γ (Multiplicative.ofAdd s)) (hp s)
  have castL (s : _root_.AbcTwoNinths.Terminal.Site) : ((L s : ℤ_[p]) : ℚ_[p]) = (_root_.AbcTwoNinths.Terminal.value γ s : ℚ_[p]) := liftCast _ _
  refine ⟨L (1,0), L (0,1), ?_, ?_, ?_⟩
  · let b : ℤ_[p] := (L (1,0) : ℤ_[p]) - 1
    change (p : ℤ_[p]) ^ m ∣ b
    by_cases hb : b = 0
    · simp [hb]
    rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation b hb]
    have he : (b : ℚ_[p]) = ((_root_.AbcTwoNinths.Terminal.value γ (1,0) - 1 : ℚ) : ℚ_[p]) := by simp [b, castL]
    have hv : (b.valuation : ℤ) = padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1,0) - 1) := by
      rw [← PadicInt.valuation_coe, he, Padic.valuation_ratCast]
    exact_mod_cast (hm.trans_eq hv.symm)
  · apply (PadicInt.norm_lt_one_iff_dvd _).mp
    rw [← PadicInt.norm_coe]
    simpa only [PadicInt.coe_sub, PadicInt.coe_one, castL] using
      (show ‖((_root_.AbcTwoNinths.Terminal.value γ (0,1) : ℚ) : ℚ_[p]) - 1‖ < 1 from hp (0,1))
  · intro s
    have he : Multiplicative.ofAdd s =
        (Multiplicative.ofAdd ((1,0) : _root_.AbcTwoNinths.Terminal.Site)) ^ s.1 *
        (Multiplicative.ofAdd ((0,1) : _root_.AbcTwoNinths.Terminal.Site)) ^ s.2 := by
      apply Multiplicative.toAdd.injective
      simp
    change PadicInt.Coe.ringHom (↑(L (1,0) ^ s.1 * L (0,1) ^ s.2) : ℤ_[p]) =
      Rat.castHom ℚ_[p] (↑(γ (Multiplicative.ofAdd s)) : ℚ)
    rw [he, map_mul, map_zpow, map_zpow]
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀]
    have powL (t : _root_.AbcTwoNinths.Terminal.Site) (n : ℤ) :
        ((↑(L t ^ n) : ℤ_[p]) : ℚ_[p]) = (_root_.AbcTwoNinths.Terminal.value γ t : ℚ_[p]) ^ n := by
      change ((Units.map PadicInt.Coe.ringHom.toMonoidHom (L t ^ n) : ℚ_[p]ˣ) : ℚ_[p]) = _
      rw [map_zpow, Units.val_zpow_eq_zpow_val]
      exact congrArg (fun u : ℚ_[p] => u ^ n) (castL t)
    exact congrArg₂ (· * ·) (powL (1,0) _) (powL (0,1) _)

/-- Proposition 7.1 of the paper. This is used in Section 7 of the paper. -/
theorem terminalBounds {K m : ℕ} (hK : 0 < K) (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter)
    (hp : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s))
    (hm : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1,0) - 1))
    (w : _root_.AbcTwoNinths.Terminal.Site) (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1) (sites : Finset _root_.AbcTwoNinths.Terminal.Site)
    (hc : 2 * K - 1 ≤ sites.card) (hl : Function.Injective (fun s : sites => s.val.2))
    {U B : ℝ} (hB : 0 < B)
    (hb : ∀ s ∈ sites ∪ sites.image (fun s => s + w), ∀ k : Fin K,
      |((Ring.choose s.2 k.val : ℤ) : ℝ)| ≤ B)
    (hh : ∀ sel : _root_.AbcTwoNinths.Terminal.Row K ↪ _root_.AbcTwoNinths.Terminal.Site, (∀ i, sel i ∈ sites ∪ sites.image (fun s => s + w)) →
      (∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ (sel i)) : ℝ)) ≤ U) :
    ∃ sel : _root_.AbcTwoNinths.Terminal.Row K ↪ _root_.AbcTwoNinths.Terminal.Site, (∀ i, sel i ∈ sites ∪ sites.image (fun s => s + w)) ∧
      let D := _root_.AbcTwoNinths.Terminal.numerator γ sel
      D ≠ 0 ∧ Real.log (D.natAbs : ℝ) ≤ U + Real.log ((2*K).factorial : ℝ) +
        (2*K : ℝ) * Real.log B ∧ (4*K ≤ 3*m →
        (2/9 : ℝ) * (2*K : ℝ)^2 * Real.log (p : ℝ) ≤ Real.log (D.natAbs : ℝ)) := by
  obtain ⟨z,a,hz,ha,hr⟩ := _root_.AbcTwoNinths.Terminal.nativeLocal γ hp m hm
  apply _root_.AbcTwoNinths.Terminal.selectedNumeratorBounds hK γ w hw sites hc hl _ z a hz ha (fun s _ => hr s) hB hb hh
  intro s _
  have hn := _root_.AbcTwoNinths.Basic.principalNorm (hp s)
  have hne : _root_.AbcTwoNinths.Terminal.value γ s ≠ 0 := (γ (Multiplicative.ofAdd s)).ne_zero
  rw [Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr hne), Padic.valuation_ratCast,
    ← zpow_zero (p : ℝ)] at hn
  have hv := (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt :
    (1 : ℝ) < p)).injective hn
  omega

end

end AbcTwoNinths.Terminal
