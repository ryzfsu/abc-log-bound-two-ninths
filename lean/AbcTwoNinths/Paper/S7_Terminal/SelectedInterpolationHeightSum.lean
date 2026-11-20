/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.OverlapLatticeAxis
public import AbcTwoNinths.Paper.S4_ExteriorE2.SourceLattice
public import AbcTwoNinths.Basic.CellCount
public import Mathlib.Tactic
public import AbcTwoNinths.Paper.S7_Terminal.InterpolationMinorNonvanishing
public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantSource
public import AbcTwoNinths.Basic.ExactMonomialHeights

/-!
# Interpolation Row Heights

The logarithmic height of a distinct-prime monomial equals the weighted height of its exponent
vector. At the integral overlap sites in Section 7 of the paper, this identifies the logarithmic
interpolation row height with the plane height seminorm.

## Main results
* `AbcTwoNinths.Terminal.monomialRowHeight`
* `AbcTwoNinths.Terminal.overlapRowHeight`
-/

@[expose] public section
namespace AbcTwoNinths.Terminal

noncomputable section

section






private theorem logWeight (x : ℤ) (l : ℝ) (hl : 0 ≤ l) :
    (x.toNat : ℝ) * l = max ((x : ℝ) * l) 0 := by
  by_cases hx : 0 ≤ x
  · have hx' : 0 ≤ (x : ℝ) := by exact_mod_cast hx
    rw [max_eq_left (mul_nonneg hx' hl)]
    have hc : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
    rw [hc]
  · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hx)
    rw [Int.toNat_eq_zero.mpr (le_of_not_ge hx), Nat.cast_zero, zero_mul,
      max_eq_right (mul_nonpos_of_nonpos_of_nonneg hx' hl)]

/--
The logarithmic height of a distinct-prime monomial equals the height of its exponent vector. This is used in Section 7 of the paper.
-/
theorem monomialRowHeight {n : ℕ} (s : _root_.AbcTwoNinths.Basic.Shape n) (w : Fin n → ℤ) :
    Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Basic.planeDiamondMonomial s w) : ℝ) = _root_.AbcTwoNinths.ExteriorE2.exponentHeight s w := by
  classical
  let support := Finset.univ.image s.primeAt
  let b := fun q => if h : ∃ j, s.primeAt j = q then w (Classical.choose h) else 0
  have hb (j : Fin n) : b (s.primeAt j) = w j := by
    dsimp [b]
    rw [dite_eq_left ⟨j, rfl⟩]
    exact congrArg w (s.distinct (Classical.choose_spec (show ∃ k, s.primeAt k = s.primeAt j from ⟨j, rfl⟩)))
  have hp : ∀ q ∈ support, Nat.Prime q := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact s.prime j
  have hm : _root_.AbcTwoNinths.Basic.monomial support b 1 = _root_.AbcTwoNinths.Basic.planeDiamondMonomial s w := by
    simp only [support, _root_.AbcTwoNinths.Basic.monomial, _root_.AbcTwoNinths.Basic.planeDiamondMonomial, one_mul]
    rw [Finset.prod_image (fun a _ a' _ h => s.distinct h)]
    simp only [hb]
  rw [← hm]
  change _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.Basic.monomial support b 1) = _
  rw [_root_.AbcTwoNinths.Basic.exactLogHeight support b hp]
  unfold _root_.AbcTwoNinths.ExteriorE2.exponentHeight
  unfold support
  rw [Finset.sum_image (fun a _ a' _ h => s.distinct h),
    Finset.sum_image (fun a _ a' _ h => s.distinct h)]
  simp only [hb]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    have hl : 0 ≤ Real.log (s.primeAt j : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (s.prime j).one_le)
  · exact logWeight (w j) _ hl
  · simpa only [Int.cast_neg, neg_mul] using logWeight (-w j) _ hl

variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable (base : (ι ⊕ Bool) → ℕ) (prime : ∀ j, (base j).Prime)
variable (avoid : ∀ j, p ≠ base j) (hi : Function.Injective base)
variable (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun j => base (.inl j)) (fun j => prime (.inl j))
  (fun j => avoid (.inl j))) (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid)
variable (k : ι) (hroof : v.val.toAdd k ≠ 0) (hu : u.val.toAdd (.inr false) = 1)

/--
The logarithmic height of the signed plane character at an integral site equals the height seminorm of its lift.
-/
theorem overlapRowHeight (c : _root_.AbcTwoNinths.Basic.Sites) :
    let s := _root_.AbcTwoNinths.Terminal.overlapShape base prime avoid hi v u k hroof hu
    let V := _root_.AbcTwoNinths.Diamond.extension base prime avoid v
    let γ := _root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid V u
    Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (γ (Multiplicative.ofAdd c) : ℚ) : ℝ) =
      _root_.AbcTwoNinths.Basic.heightSeminorm s (_root_.AbcTwoNinths.Basic.lift c) := by
  let s := _root_.AbcTwoNinths.Terminal.overlapShape base prime avoid hi v u k hroof hu
  let V := _root_.AbcTwoNinths.Diamond.extension base prime avoid v
  let a := V ^ c.1 * u ^ c.2
  let e := (Fintype.equivFin (ι ⊕ Bool)).symm
  have hm : (_root_.AbcTwoNinths.ExteriorE2.monomial base prime a.val : ℚ) = _root_.AbcTwoNinths.Basic.planeDiamondMonomial s (_root_.AbcTwoNinths.ExteriorE2.siteExponent s c) := by
    change ((∏ j, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime j ^ a.val.toAdd j : ℚˣ) : ℚ) = _
    rw [show ((∏ j, _root_.AbcTwoNinths.ExteriorE2.ratUnit base prime j ^ a.val.toAdd j : ℚˣ) : ℚ) =
        ∏ j, ((_root_.AbcTwoNinths.ExteriorE2.ratUnit base prime j ^ a.val.toAdd j : ℚˣ) : ℚ) from
      map_prod (Units.coeHom ℚ) _ _]
    simp only [Units.val_zpow_eq_zpow_val, _root_.AbcTwoNinths.ExteriorE2.ratUnit,
      Units.val_mk0, _root_.AbcTwoNinths.Basic.planeDiamondMonomial]
    symm
    apply Fintype.prod_equiv e
    intro j
    change (base (e j) : ℚ) ^ _root_.AbcTwoNinths.ExteriorE2.siteExponent s c j = (base (e j) : ℚ) ^
      (_root_.AbcTwoNinths.Diamond.along V.val u.val c).toAdd (e j)
    rw [_root_.AbcTwoNinths.Diamond.alongApply]
    rfl
  change Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Diamond.character base prime avoid a : ℚ) : ℝ) = _
  have hs := (_root_.AbcTwoNinths.ExteriorE2.signCharacterization (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid)
    (_root_.AbcTwoNinths.ExteriorE2.monomial base prime) a).2
  change _root_.AbcTwoNinths.Diamond.character base prime avoid a = _ at hs
  rw [hs]
  split <;> simp only [Units.val_neg, hm, _root_.AbcTwoNinths.Terminal.rowHeightMax, Rat.neg_num, Int.natAbs_neg, Rat.neg_den] <;>
    change Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Basic.planeDiamondMonomial s (_root_.AbcTwoNinths.ExteriorE2.siteExponent s c)) : ℝ) = _root_.AbcTwoNinths.Basic.height s (_root_.AbcTwoNinths.Basic.lift c) <;>
    rw [_root_.AbcTwoNinths.Terminal.monomialRowHeight, _root_.AbcTwoNinths.ExteriorE2.exponentHeightSiteExponent]

end

end
end AbcTwoNinths.Terminal
