/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TailScalar
public import AbcTwoNinths.Basic.ValuationHeightBound
public import AbcTwoNinths.Paper.S1_Statement.LogarithmicHeight
public import AbcTwoNinths.Paper.S5_Selection.RootPowerValuation

/-!
# Primitive Tail

The module shows that the primitive and rational-root indices equal one under the stated tail hypotheses. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.primitiveIndexEqOne`
* `AbcTwoNinths.Selection.rationalRootIndexEqOne`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section

/--
Above the contact-height threshold, the root and index depth bounds force the positive power index to equal one. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem primitiveIndexEqOne {g : ℕ} {H κ L rootDepth indexDepth rawDepth : ℝ}
    (hg : 0 < g) (hk : κ < 1 / 4) (hH : _root_.AbcTwoNinths.Basic.contactHeightOnset κ ≤ H)
    (hcontact : (1 - 2 * κ) * H ≤ rawDepth * L)
    (hlte : rawDepth = rootDepth + indexDepth)
    (hroot : rootDepth * L ≤ H / g + Real.log 2)
    (hindex : indexDepth * L ≤ Real.log (H / Real.log 2)) :
    g = 1 := by
  by_contra h
  have hg2 : 2 ≤ g := by omega
  have hg2' : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hs := _root_.AbcTwoNinths.Basic.positiveContactTail hk hg2' hH
  rw [hlte, add_mul] at hcontact
  linarith

/--
The valuation identity, contact lower bound and height bounds force the power index of the rational root to equal one. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem rationalRootIndexEqOne {p g : ℕ} {u : ℚ} {H κ : ℝ} {m : ℕ}
    (hp : p.Prime) (hg : 0 < g) (hu : u ≠ 1) (hunit : ¬ p ∣ u.den)
    (hk : κ < 1 / 4) (hH : _root_.AbcTwoNinths.Basic.contactHeightOnset κ ≤ H)
    (hcontact : (1 - 2 * κ) * H ≤ (m : ℝ) * Real.log p)
    (hlte : (m : ℤ) = padicValRat p (u - 1) + (padicValNat p g : ℤ))
    (hroot : Real.log (max u.num.natAbs u.den : ℝ) ≤ H / (g : ℝ))
    (hindex : (g : ℝ) ≤ H / Real.log 2) :
    g = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  obtain ⟨ha, hb⟩ := _root_.AbcTwoNinths.Basic.valHeight hp hu hunit
  have hcast : (p : ℝ) ^ (padicValRat p (u - 1)).toNat ≤
      2 * max (u.num.natAbs : ℝ) u.den := by
    exact_mod_cast ha.trans hb
  have hM : 0 < max (u.num.natAbs : ℝ) u.den :=
    (show (0 : ℝ) < u.den by exact_mod_cast u.den_pos).trans_le (le_max_right _ _)
  have hA := Real.log_le_log (pow_pos hpp _) hcast
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hM.ne'] at hA
  have hr : (padicValRat p (u - 1) : ℝ) * Real.log p ≤ H / (g : ℝ) + Real.log 2 := by
    have hz : padicValRat p (u - 1) ≤ ((padicValRat p (u - 1)).toNat : ℤ) := by omega
    have hz' : (padicValRat p (u - 1) : ℝ) ≤
        ((padicValRat p (u - 1)).toNat : ℝ) := by exact_mod_cast hz
    linarith [mul_le_mul_of_nonneg_right hz' hlp]
  have hd := Real.log_le_log (pow_pos hpp (padicValNat p g))
    (show ((p : ℝ) ^ padicValNat p g) ≤ (g : ℝ) by
      exact_mod_cast Nat.le_of_dvd hg pow_padicValNat_dvd)
  rw [Real.log_pow] at hd
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hlte' := congrArg (fun z : ℤ => (z : ℝ)) hlte
  simp only [Int.cast_add, Int.cast_natCast] at hlte'
  exact _root_.AbcTwoNinths.Selection.primitiveIndexEqOne hg hk hH hcontact hlte' hr
    (hd.trans (Real.log_le_log hg' hindex))



/--
For a prescribed positive index, the selected exponent vector has a signed lift whose representation as a power of that index forces the index to equal one.
-/
theorem nativeIndexEqOne (t : _root_.AbcTwoNinths.Basic.Triple) {p g : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (hg : 0 < g)
    {κ : ℝ} (hk : κ < 1 / 4) (hH : _root_.AbcTwoNinths.Basic.contactHeightOnset κ ≤ t.logHeight)
    (hcontact : (1 - 2 * κ) * t.logHeight ≤
      (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let r := _root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s)
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
      ∀ v : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w = v ^ g → g = 1 := by
  intro s r
  let m := _root_.AbcTwoNinths.ExteriorE2.monomial (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d)
  obtain ⟨w, hv, hw, he⟩ := _root_.AbcTwoNinths.Selection.nativeRootLte t hp hg
  refine ⟨w, hv, ?_⟩
  intro v hvg
  let u := (_root_.AbcTwoNinths.ExteriorE2.gammaStar r m v : ℚ)
  obtain ⟨N, D, hN, hD, hdiff, hrat, hval⟩ := he v hvg
  have hrat' : u = (N : ℚ) / (D : ℚ) := hrat
  have hDz : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDz
  have hu : u ≠ 0 := by
    rw [hrat']
    exact div_ne_zero (by exact_mod_cast (show N ≠ 0 from fun h => hN (h ▸ dvd_zero _))) hDq
  have hn : u ≠ -1 := by
    intro h
    have hEq := (div_eq_iff hDq).mp (hrat'.symm.trans h)
    have hEq' : N = -D := by exact_mod_cast (show (N : ℚ) = -(D : ℚ) by linarith)
    have h2D : (p : ℤ) ∣ 2 * D := by
      rw [hEq', show -D - D = -(2 * D) by ring, dvd_neg] at hdiff
      exact hdiff
    have hP : p.Prime := Fact.out
    have hp2 : 2 < p := Fact.out
    have hnat : p ∣ 2 * D.natAbs := by
      simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h2D
    rcases hP.dvd_mul.mp hnat with h2 | hd
    · exact (not_le_of_gt hp2) (Nat.le_of_dvd (by decide) h2)
    · exact hD (Int.natAbs_dvd_natAbs.mp (by simpa using hd))
  have hunit : ¬ p ∣ u.den := by
    intro h
    apply hD
    have hd : (u.den : ℤ) ∣ D := by
      rw [hrat', Rat.intCast_div_eq_divInt]
      exact Rat.den_dvd N D
    exact (show (p : ℤ) ∣ (u.den : ℤ) by exact_mod_cast h).trans hd
  have hpow : _root_.AbcTwoNinths.Statement.selectedSource t = u ^ g := by
    rw [← hw, hvg, map_pow, Units.val_pow_eq_pow_val]
  have h1 : u ≠ 1 := by
    intro hu1
    have hs : _root_.AbcTwoNinths.Statement.selectedSource t = 1 := by simpa [hu1] using hpow
    have ha : (0 : ℚ) < t.a := by exact_mod_cast t.apos
    have hb : (0 : ℚ) < t.b := by exact_mod_cast t.bpos
    have hc : (t.a : ℚ) + t.b = t.c := by exact_mod_cast t.add
    unfold _root_.AbcTwoNinths.Statement.selectedSource at hs
    cases hside : _root_.AbcTwoNinths.Statement.minRadicalSide t <;> simp only [hside] at hs
    · linarith [(div_eq_iff hb.ne').mp hs]
    · linarith [(div_eq_iff ha.ne').mp hs]
    · linarith [(div_eq_iff hb.ne').mp hs]
  have hmul := _root_.AbcTwoNinths.Statement.mulHeightSelectedSourceLe t
  rw [hpow, _root_.AbcTwoNinths.Statement.mulHeightPow] at hmul
  have hbase : 0 < (_root_.AbcTwoNinths.Statement.mulHeight u : ℝ) := by
    exact_mod_cast (u.den_pos.trans_le (le_max_right u.num.natAbs u.den))
  have hlog := Real.log_le_log (pow_pos hbase g)
    (show (_root_.AbcTwoNinths.Statement.mulHeight u : ℝ) ^ g ≤ t.c by exact_mod_cast hmul)
  rw [Real.log_pow] at hlog
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hroot : Real.log (max u.num.natAbs u.den : ℝ) ≤ t.logHeight / (g : ℝ) :=
    (le_div_iff₀ hg').mpr (by simpa [_root_.AbcTwoNinths.Statement.mulHeight, _root_.AbcTwoNinths.Basic.Triple.logHeight, mul_comm] using hlog)
  have hval' : (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) =
      padicValRat p (u - 1) + (padicValNat p g : ℤ) := by simpa only [show u = _ from hrat] using hval
  exact _root_.AbcTwoNinths.Selection.rationalRootIndexEqOne Fact.out hg h1 hunit hk hH hcontact hval' hroot
    (_root_.AbcTwoNinths.Statement.exponentLeHeight hu h1 hn hpow)

end

end AbcTwoNinths.Selection
