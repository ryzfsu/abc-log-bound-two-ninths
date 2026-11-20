/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.MonomialQuotientValuation

/-!
# Signed Basis Units

Evaluating a signed exponent vector in the residue kernel gives a positive principal unit whose
logarithmic height equals the height of the corresponding plane vector. This supports Proposition
2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.signedBasisUnit`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section


/--
A signed residue-kernel basis monomial is a principal unit with the height of its plane vector. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem signedBasisUnit {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : p.Prime) (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hqi : Function.Injective q)
    (haway : ∀ j, ¬ p ∣ q j) {e v : ι → ℤ}
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hv : v ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (w : ℤ × ℤ) (s : ℤ) (hs : |s| = 1) :
    _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p (_root_.AbcTwoNinths.PolyCap.prodMonomial q (s • _root_.AbcTwoNinths.PolyCap.planeMap e v w)) ∧
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q (s • _root_.AbcTwoNinths.PolyCap.planeMap e v w)) = _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) := by
  let K := (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker
  have hk : _root_.AbcTwoNinths.PolyCap.planeMap e v w ∈ K := by
    change w.1 • e + w.2 • v ∈ K
    exact K.add_mem (K.zsmul_mem he _) (K.zsmul_mem hv _)
  refine ⟨(_root_.AbcTwoNinths.PolyCap.memResidueKerIffGp hp q hq hqi haway _).mp (K.zsmul_mem hk _), ?_⟩
  have hm : s • _root_.AbcTwoNinths.PolyCap.planeMap e v w = _root_.AbcTwoNinths.PolyCap.planeMap e v (s • w) := by
    funext j
    change s * (w.1 * e j + w.2 * v j) = (s * w.1) * e j + (s * w.2) * v j
    ring
  have hr : _root_.AbcTwoNinths.PolyCap.realPair (s • w) = (s : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w := by
    apply Prod.ext
    · change ((s * w.1 : ℤ) : ℝ) = (s : ℝ) * w.1
      exact Int.cast_mul _ _
    · change ((s * w.2 : ℤ) : ℝ) = (s : ℝ) * w.2
      exact Int.cast_mul _ _
  have hs' : |(s : ℝ)| = 1 := by exact_mod_cast hs
  rw [hm, _root_.AbcTwoNinths.PolyCap.planeHeightEqRatHeight q hq hqi]
  change _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair (s • w)) = _
  rw [hr, _root_.AbcTwoNinths.PolyCap.planeHeightSmul, hs', one_mul]

end

end AbcTwoNinths.PolyCap
