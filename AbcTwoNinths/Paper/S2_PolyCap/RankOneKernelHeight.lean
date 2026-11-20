/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PrimitiveCyclicExponent
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationMonomialHeight
public import AbcTwoNinths.Basic.ExponentResidue
public import AbcTwoNinths.Paper.S2_PolyCap.RankOneHeight

/-!
# Rank One Kernel Height

The module bounds height in the rank-one kernel case by using its primitive cyclic generator. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.singletonHeight`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The depth hypothesis for a primitive kernel exponent on singleton support gives the strict bound H < 4 R cubed. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem singletonHeight {ι : Type*} [Unique ι] [Fintype ι] {p : ℕ} [Fact p.Prime]
    (q : ι → ℕ) (hq : ∀ i, Nat.Coprime (q i) p) (hq1 : ∀ i, 1 < q i)
    {e : ι → ℤ} (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q hq).ker)
    (hprim : ∀ (n : ℕ) (v : ι → ℤ), v ∈ (_root_.AbcTwoNinths.Basic.residue q hq).ker →
      n • v = e → n = 1) {H r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hpqR : (p : ℝ) * q default ≤ R)
    (hdepth : H / (4 * r) < _root_.AbcTwoNinths.Basic.padicRationalHeight (∏ i, (q i : ℚ) ^ e i)) :
    H < 4 * R ^ 3 := by
  let u := ZMod.unitOfCoprime (q default) (hq default)
  have hmem (v : ι → ℤ) : v ∈ (_root_.AbcTwoNinths.Basic.residue q hq).ker ↔ u ^ v default = 1 := by
    change (∏ i, ZMod.unitOfCoprime (q i) (hq i) ^ v i) = 1 ↔ _
    rw [Fintype.prod_unique]
  have habs : (e default).natAbs = orderOf u :=
    _root_.AbcTwoNinths.Basic.primitiveCyclicExponent u ((hmem _).mp he) (by
      intro n v hv hnv
      apply hprim n (fun _ => v) ((hmem _).mpr hv)
      funext i
      rw [Unique.eq_default i]
      exact hnv)
  have hd : orderOf u ≤ p - 1 := by
    have hh := orderOf_le_card_univ (x := u)
    rwa [ZMod.card_units] at hh
  have hheight := _root_.AbcTwoNinths.PolyCap.monomialHeightLe q e (fun i => (hq1 i).trans' Nat.zero_lt_one)
  rw [Fintype.sum_unique] at hheight
  have hcast : |(e default : ℝ)| = (orderOf u : ℝ) := by
    have hi : |e default| = (orderOf u : ℤ) := by rw [← Int.natCast_natAbs, habs]
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun z : ℤ => (z : ℝ)) hi
  rw [hcast] at hheight
  exact _root_.AbcTwoNinths.PolyCap.rankOneHeight hr hrR (Fact.out : p.Prime).one_le
    (hq1 _) hpqR hd (hdepth.trans_le hheight)

end

end AbcTwoNinths.PolyCap
