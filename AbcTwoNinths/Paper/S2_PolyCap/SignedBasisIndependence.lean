/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.MonomialPowerLaws
public import AbcTwoNinths.Paper.S2_PolyCap.KernelLinesAndCramerProduct

/-!
# Signed Basis Independence

The module proves that monomials along a signed exponent basis are multiplicatively independent. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.signedBasisIndependent`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section


/-- The plane map preserves integer linear combinations of two vectors. -/
theorem planeMapSmulAdd {ι : Type*} (e v : ι → ℤ)
    (w m : ℤ × ℤ) (a b : ℤ) :
    _root_.AbcTwoNinths.PolyCap.planeMap e v (a • w + b • m) = a • _root_.AbcTwoNinths.PolyCap.planeMap e v w + b • _root_.AbcTwoNinths.PolyCap.planeMap e v m := by
  funext j
  change (a*w.1+b*m.1)*e j + (a*w.2+b*m.2)*v j =
    a*(w.1*e j+w.2*v j)+b*(m.1*e j+m.2*v j)
  ring

/--
Nonzero integer multiples of two independent plane vectors give multiplicatively independent prime monomials under an injective plane map. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem signedBasisIndependent {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hqi : Function.Injective q)
    {e v : ι → ℤ} (hi : Function.Injective (_root_.AbcTwoNinths.PolyCap.planeMap e v)) {w m : ℤ × ℤ}
    (hd : _root_.AbcTwoNinths.PolyCap.det2 w m ≠ 0) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    _root_.AbcTwoNinths.Basic.RatMulIndependent (_root_.AbcTwoNinths.PolyCap.prodMonomial q (a • _root_.AbcTwoNinths.PolyCap.planeMap e v w))
      (_root_.AbcTwoNinths.PolyCap.prodMonomial q (b • _root_.AbcTwoNinths.PolyCap.planeMap e v m)) := by
  intro s t h
  rw [← _root_.AbcTwoNinths.PolyCap.prodMonomialSmul, ← _root_.AbcTwoNinths.PolyCap.prodMonomialSmul, ← _root_.AbcTwoNinths.PolyCap.prodMonomialAdd q hq,
    smul_smul, smul_smul, ← _root_.AbcTwoNinths.PolyCap.planeMapSmulAdd] at h
  have hz : (s*a) • w + (t*b) • m = 0 := by
    apply hi
    exact funext (by simpa [_root_.AbcTwoNinths.PolyCap.planeMap] using (_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff q hq hqi _).mp h)
  have h1 := congrArg Prod.fst hz
  have h2 := congrArg Prod.snd hz
  change (s*a)*w.1 + (t*b)*m.1 = 0 at h1
  change (s*a)*w.2 + (t*b)*m.2 = 0 at h2
  have hs : (s*a)*_root_.AbcTwoNinths.PolyCap.det2 w m = 0 := by
    unfold _root_.AbcTwoNinths.PolyCap.det2
    linear_combination m.2 * h1 - m.1 * h2
  have ht : (t*b)*_root_.AbcTwoNinths.PolyCap.det2 w m = 0 := by
    unfold _root_.AbcTwoNinths.PolyCap.det2
    linear_combination w.1 * h2 - w.2 * h1
  exact ⟨(mul_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hd)).resolve_right ha,
    (mul_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hd)).resolve_right hb⟩

end

end AbcTwoNinths.PolyCap
