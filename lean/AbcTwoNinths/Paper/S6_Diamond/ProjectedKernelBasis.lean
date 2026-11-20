/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.OrderedRadicalData
public import AbcTwoNinths.Basic.RectLink
public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Projected Kernel Basis

The module lifts projected collision vectors to signed kernel columns and bounds their heights. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.collisionKernelColumns`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



variable {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {r : _root_.AbcTwoNinths.ExteriorE2.Exponents I →* (ZMod p)ˣ}

/--
Form the signed kernel element specified by an integer coefficient pair on two generating rows. This is used in Section 6 of the paper.
-/
def kernelColumn (s w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) (x : _root_.AbcTwoNinths.Basic.ZPair) : _root_.AbcTwoNinths.ExteriorE2.Kernel r :=
  s ^ x.1 * w ^ x.2

set_option linter.unusedSectionVars false in
/-- The exponent row of a signed kernel column is the indicated integral linear combination. -/
theorem kernelColumnRow (s w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) (x : _root_.AbcTwoNinths.Basic.ZPair) :
    (_root_.AbcTwoNinths.Diamond.kernelColumn s w x).val.toAdd = _root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd x := by
  funext i
  change ((s ^ x.1 * w ^ x.2).val.toAdd) i = _
  simp only [Subgroup.coe_mul, Subgroup.coe_zpow, toAdd_mul, toAdd_zpow,
    Pi.add_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_id, zsmul_eq_mul, _root_.AbcTwoNinths.Basic.eval]

/--
The rational height of a signed monomial on distinct primes is bounded by the logarithmically weighted mass of its exponent row.
-/
theorem signedKernelHeight (q : I → ℕ) (hq : ∀ i, (q i).Prime)
    (hi : Function.Injective q) (u : _root_.AbcTwoNinths.ExteriorE2.Kernel r) :
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.ExteriorE2.gammaStar r (_root_.AbcTwoNinths.ExteriorE2.monomial q hq) u : ℚ) ≤
      _root_.AbcTwoNinths.Basic.mass (fun i => Real.log (q i : ℝ)) u.val.toAdd := by
  have hm : (_root_.AbcTwoNinths.ExteriorE2.monomial q hq u.val : ℚ) =
      _root_.AbcTwoNinths.PolyCap.prodMonomial q u.val.toAdd := by
    simp [_root_.AbcTwoNinths.ExteriorE2.monomial, _root_.AbcTwoNinths.ExteriorE2.eval, _root_.AbcTwoNinths.ExteriorE2.ratUnit,
      _root_.AbcTwoNinths.PolyCap.prodMonomial]
  have hb := (_root_.AbcTwoNinths.PolyCap.ratHeightProdMonomial q hq hi u.val.toAdd).2
  change _root_.AbcTwoNinths.Basic.rationalHeight (↑(_root_.AbcTwoNinths.ExteriorE2.signUnit r u * _root_.AbcTwoNinths.ExteriorE2.monomial q hq u.val) : ℚ) ≤ _
  by_cases hr : r u.val = 1
  · simpa [_root_.AbcTwoNinths.ExteriorE2.signUnit, hr, hm, _root_.AbcTwoNinths.Basic.mass] using hb
  · simpa [_root_.AbcTwoNinths.ExteriorE2.signUnit, hr, hm, _root_.AbcTwoNinths.Basic.mass, _root_.AbcTwoNinths.Basic.rationalHeight] using hb

/--
A determinant-one change of columns recovers the first generator, preserves injectivity, and bounds both signed heights by their row masses.
-/
theorem kernelColumns (q : I → ℕ) (hq : ∀ i, (q i).Prime)
    (hi : Function.Injective q) (s w : _root_.AbcTwoNinths.ExteriorE2.Kernel r)
    (hind : Function.Injective (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd))
    (x y : _root_.AbcTwoNinths.Basic.ZPair) (hdet : _root_.AbcTwoNinths.Basic.det x y = 1) :
    let U := _root_.AbcTwoNinths.Diamond.kernelColumn s w x
    let V := _root_.AbcTwoNinths.Diamond.kernelColumn s w y
    let gamma := _root_.AbcTwoNinths.ExteriorE2.gammaStar r (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)
    let W := fun i => Real.log (q i : ℝ)
    s = U ^ y.2 * V ^ (-x.2) ∧
      Function.Injective (_root_.AbcTwoNinths.Basic.eval U.val.toAdd V.val.toAdd) ∧
      _root_.AbcTwoNinths.Basic.rationalHeight (gamma U : ℚ) ≤ _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd x) ∧
      _root_.AbcTwoNinths.Basic.rationalHeight (gamma V : ℚ) ≤ _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd y) := by
  intro U V gamma W
  have hx : U.val.toAdd = _ := _root_.AbcTwoNinths.Diamond.kernelColumnRow s w x
  have hy : V.val.toAdd = _ := _root_.AbcTwoNinths.Diamond.kernelColumnRow s w y
  have heval (z : _root_.AbcTwoNinths.Basic.ZPair) :
      _root_.AbcTwoNinths.Basic.eval U.val.toAdd V.val.toAdd z =
        _root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd
          (z.1 * x.1 + z.2 * y.1, z.1 * x.2 + z.2 * y.2) := by
    rw [hx, hy]
    funext i
    simp only [_root_.AbcTwoNinths.Basic.eval]
    ring
  have h1 : y.2 * x.1 + (-x.2) * y.1 = 1 := by
    unfold _root_.AbcTwoNinths.Basic.det at hdet
    linarith
  have h2 : y.2 * x.2 + (-x.2) * y.2 = 0 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change s.val = (_root_.AbcTwoNinths.Diamond.kernelColumn U V (y.2, -x.2)).val
    change s.val.toAdd = (_root_.AbcTwoNinths.Diamond.kernelColumn U V (y.2, -x.2)).val.toAdd
    rw [_root_.AbcTwoNinths.Diamond.kernelColumnRow, heval]
    simp only [h1, h2]
    funext i
    simp [_root_.AbcTwoNinths.Basic.eval]
  · intro a b hab
    rw [heval, heval] at hab
    have h := hind hab
    have hf := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    change a.1 * x.1 + a.2 * y.1 = b.1 * x.1 + b.2 * y.1 at hf
    change a.1 * x.2 + a.2 * y.2 = b.1 * x.2 + b.2 * y.2 at hs
    unfold _root_.AbcTwoNinths.Basic.det at hdet
    apply Prod.ext
    · linear_combination y.2 * hf - y.1 * hs - (a.1 - b.1) * hdet
    · linear_combination x.1 * hs - x.2 * hf - (a.2 - b.2) * hdet
  · rw [← hx]
    exact _root_.AbcTwoNinths.Diamond.signedKernelHeight q hq hi U
  · rw [← hy]
    exact _root_.AbcTwoNinths.Diamond.signedKernelHeight q hq hi V

/--
Independent kernel rows with small weighted shear admit a determinant-one basis with bounded heights, mass product, and coefficient-weighted masses. This is used in Section 6 of the paper.
-/
theorem collisionKernelColumns (q : I → ℕ) (hq : ∀ i, (q i).Prime)
    (hi : Function.Injective q) (s w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) {j : I}
    (hj : s.val.toAdd j ≠ 0)
    (hind : ¬ ∃ a : ℚ, ∀ i, (w.val.toAdd i : ℚ) = a * (s.val.toAdd i : ℚ))
    {t T : ℝ}
    (herr : ∑ i, |(w.val.toAdd i : ℝ) - t * (s.val.toAdd i : ℝ)| *
      Real.log (q i : ℝ) < T) :
    ∃ x y : _root_.AbcTwoNinths.Basic.ZPair, _root_.AbcTwoNinths.Basic.det x y = 1 ∧
      let U := _root_.AbcTwoNinths.Diamond.kernelColumn s w x
      let V := _root_.AbcTwoNinths.Diamond.kernelColumn s w y
      let gamma := _root_.AbcTwoNinths.ExteriorE2.gammaStar r (_root_.AbcTwoNinths.ExteriorE2.monomial q hq)
      let W := fun i => Real.log (q i : ℝ)
      let A := _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd x)
      let B := _root_.AbcTwoNinths.Basic.mass W (_root_.AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd y)
      s = U ^ y.2 * V ^ (-x.2) ∧
      Function.Injective (_root_.AbcTwoNinths.Basic.eval U.val.toAdd V.val.toAdd) ∧
      _root_.AbcTwoNinths.Basic.rationalHeight (gamma U : ℚ) ≤ A ∧ _root_.AbcTwoNinths.Basic.rationalHeight (gamma V : ℚ) ≤ B ∧
      A * B < 12 * _root_.AbcTwoNinths.Basic.mass W s.val.toAdd * T ∧
      |(y.2 : ℝ)| * A ≤ 3 * _root_.AbcTwoNinths.Basic.mass W s.val.toAdd ∧
      |(x.2 : ℝ)| * B ≤ 2 * _root_.AbcTwoNinths.Basic.mass W s.val.toAdd := by
  have hW (i : I) : 0 < Real.log (q i : ℝ) :=
    Real.log_pos (by exact_mod_cast (hq i).one_lt)
  obtain ⟨x, y, hdet, hprod, hx, hy⟩ := _root_.AbcTwoNinths.Basic.collisionRectangle hj hind hW herr
  obtain ⟨hrep, hinj, hU, hV⟩ := _root_.AbcTwoNinths.Diamond.kernelColumns q hq hi s w (_root_.AbcTwoNinths.Basic.evalInjective hj hind) x y hdet
  exact ⟨x, y, hdet, hrep, hinj, hU, hV, hprod, hx, hy⟩

end

end AbcTwoNinths.Diamond
