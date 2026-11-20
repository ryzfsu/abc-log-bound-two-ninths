/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.PrimitiveTail
public import AbcTwoNinths.Paper.S5_Selection.RoofMass
public import AbcTwoNinths.Paper.S5_Selection.RoofPeak

/-!
# Primitive source vector at the selected prime

Proves that the signed source vector is primitive in the residue kernel at the selected prime and
gives a lower bound for its largest absolute coordinate. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.nativeRoof`
-/

@[expose] public section


namespace AbcTwoNinths.Selection


open scoped BigOperators

section

private theorem contactLog (t : _root_.AbcTwoNinths.Basic.Triple) {κ : ℝ} (h : _root_.AbcTwoNinths.Statement.RealContactBound κ t) :
    (1 - κ) * t.logHeight ≤ Real.log (t.a : ℝ) := by
  have ha : (0 : ℝ) < t.a := by exact_mod_cast t.apos
  have hcn : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hc : (0 : ℝ) < t.c := by exact_mod_cast hcn
  unfold _root_.AbcTwoNinths.Statement.RealContactBound at h
  rw [Real.log_div hc.ne' ha.ne'] at h
  change (1 - κ) * Real.log (t.c : ℝ) ≤ _
  change _ ≤ κ * Real.log (t.c : ℝ) at h
  linarith

/--
The residue kernel of the selected side contains its signed valuation vector as a primitive element with an explicit lower bound on its largest absolute coordinate. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem nativeRoof (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    {κ : ℝ} (hk : κ < 1 / 4) (hh : _root_.AbcTwoNinths.Basic.contactHeightOnset κ ≤ t.logHeight)
    (hm : (1 - 2 * κ) * t.logHeight ≤
      (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p)
    (he : _root_.AbcTwoNinths.Statement.RealContactBound κ t) (hx : 0 < t.thirdLogRadical)
    (hside : let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
      s.n.Coprime s.d ∧ t.a ≤ s.n ∧ t.a ≤ s.d ∧ s.n * s.d ∣ t.a * t.b * t.c) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let r := _root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s)
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
      (∀ (g : ℕ) (v : _root_.AbcTwoNinths.ExteriorE2.Kernel r), 0 < g → w = v ^ g → g = 1) ∧
      (2 - 2 * κ) * t.logHeight / (3 * t.thirdLogRadical) ≤
        ((Finset.univ.sup (fun i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d => (w.val.toAdd i).natAbs) : ℕ) : ℝ) := by
  classical
  intro s r
  obtain ⟨w, hw, _, _⟩ := _root_.AbcTwoNinths.Selection.selectedNative t hp
  refine ⟨w, hw, ?_, ?_⟩
  · intro g v hg hv
    obtain ⟨z, hz, h⟩ := _root_.AbcTwoNinths.Selection.nativeIndexEqOne t hp hg hk hh hm
    have eq : w = z := Subtype.ext (hw.trans hz.symm)
    exact h v (eq ▸ hv)
  · obtain ⟨hc, hn, hd, hdiv⟩ := hside
    have ht : t.a * t.b * t.c ≠ 0 := by
      have hc' : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
      exact mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc'.ne'
    have hS : s.n.primeFactors ∪ s.d.primeFactors ⊆
        (t.a * t.b * t.c).primeFactors := by
      rw [← Nat.primeFactors_mul s.hn s.hd]
      exact Nat.primeFactors_mono hdiv ht
    let P := Finset.univ.sup (fun i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d => ((_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d).toAdd i).natAbs)
    have hpeak : ∀ i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d, ((_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d).toAdd i).natAbs ≤ P :=
      fun i => Finset.le_sup (f := fun j => ((_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d).toAdd j).natAbs) (Finset.mem_univ i)
    have hupper := _root_.AbcTwoNinths.Selection.peakMassSubtypeLe t hS (_root_.AbcTwoNinths.ExteriorE2.vec s.n s.d).toAdd hpeak
    have hl : (0 : ℝ) < t.a := by exact_mod_cast t.apos
    have ha := contactLog t he
    have hln := Real.log_le_log hl (show (t.a : ℝ) ≤ s.n by exact_mod_cast hn)
    have hld := Real.log_le_log hl (show (t.a : ℝ) ≤ s.d by exact_mod_cast hd)
    have hmass := _root_.AbcTwoNinths.Selection.roofMass s.hn s.hd hc
    rw [Real.log_mul (by exact_mod_cast s.hn) (by exact_mod_cast s.hd)] at hmass
    have hup : Real.log (s.n : ℝ) + Real.log (s.d : ℝ) ≤ (P : ℝ) * (3 * t.thirdLogRadical) := by
      rw [← hmass]
      simpa [_root_.AbcTwoNinths.ExteriorE2.base] using hupper
    rw [hw]
    apply (div_le_iff₀ (by positivity : 0 < 3 * t.thirdLogRadical)).mpr
    change _ ≤ (P : ℝ) * (3 * t.thirdLogRadical)
    linarith

end

end AbcTwoNinths.Selection
