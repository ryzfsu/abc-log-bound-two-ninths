/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.OrderedRadicalData
public import AbcTwoNinths.Paper.S5_Selection.SelectedLTE

/-!
# Root Power Valuation

The module splits signed root exponents and uses power lifting to recover the source's local valuation depth. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.nativeRootLte`
-/

@[expose] public section


namespace AbcTwoNinths.Selection



section

private theorem evalSplit {ι K : Type*} [Fintype ι] [Field K]
    (b : ι → Kˣ) (x : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) :
    _root_.AbcTwoNinths.ExteriorE2.eval b x * (∏ i, b i ^ (-x.toAdd i).toNat) = ∏ i, b i ^ (x.toAdd i).toNat := by
  change (∏ i, b i ^ x.toAdd i) * _ = _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
  congr 1
  omega

private theorem signedPair {ι : Type*} [Fintype ι] {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (b : ι → ℕ) (hb : ∀ i, (b i).Prime) (avoid : ∀ i, p ≠ b i)
    (v : _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid)) :
    ∃ N D : ℤ, ¬(p : ℤ) ∣ N ∧ ¬(p : ℤ) ∣ D ∧ (p : ℤ) ∣ N - D ∧
      (_root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid)
        (_root_.AbcTwoNinths.ExteriorE2.monomial b hb) v : ℚ) = (N : ℚ) / (D : ℚ) := by
  classical
  let n := ∏ i, b i ^ (v.val.toAdd i).toNat
  let d := ∏ i, b i ^ (-v.val.toAdd i).toNat
  have hu (i : ι) : (b i : ZMod p) ≠ 0 :=
    (_root_.AbcTwoNinths.ExteriorE2.residueUnit b hb avoid i).ne_zero
  have hn : (n : ZMod p) ≠ 0 := by
    simp only [n, Nat.cast_prod, Nat.cast_pow]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hu i)
  have hd : (d : ZMod p) ≠ 0 := by
    simp only [d, Nat.cast_prod, Nat.cast_pow]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hu i)
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 from fun h => hd (by simp [h]))
  have rq : (_root_.AbcTwoNinths.ExteriorE2.monomial b hb v.val : ℚ) = n / d := by
    apply (eq_div_iff hdq).2
    simpa [_root_.AbcTwoNinths.ExteriorE2.monomial, _root_.AbcTwoNinths.ExteriorE2.ratUnit, n, d,
      Units.coe_prod, Units.val_pow_eq_pow_val] using
      congrArg Units.val (evalSplit (_root_.AbcTwoNinths.ExteriorE2.ratUnit b hb) v.val)
  have rz : (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid v.val : ZMod p) * d = n := by
    simpa [_root_.AbcTwoNinths.ExteriorE2.residue, _root_.AbcTwoNinths.ExteriorE2.residueUnit, n, d,
      Units.coe_prod, Units.val_pow_eq_pow_val] using
      congrArg Units.val (evalSplit (_root_.AbcTwoNinths.ExteriorE2.residueUnit b hb avoid) v.val)
  have hsign := _root_.AbcTwoNinths.ExteriorE2.signCharacterization (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid)
    (_root_.AbcTwoNinths.ExteriorE2.monomial b hb) v
  let neg := _root_.AbcTwoNinths.ExteriorE2.chooseNegative (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid) v
  change (if neg then -_ else _) = 1 ∧ _ = (if neg then -_ else _) at hsign
  cases hneg : neg
  · have hres := congrArg Units.val hsign.1
    rw [hneg] at hres
    have hh : (_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid v.val : ZMod p) = 1 := by
      simpa using hres
    have he : (n : ZMod p) = d := by rw [← rz, hh, one_mul]
    refine ⟨n, d, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hn ((ZMod.natCast_eq_zero_iff n p).2 (by exact_mod_cast h))
    · intro h
      exact hd ((ZMod.natCast_eq_zero_iff d p).2 (by exact_mod_cast h))
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.mpr he
    · have hq := congrArg Units.val hsign.2
      simpa [hneg, rq] using hq
  · have hres := congrArg Units.val hsign.1
    rw [hneg] at hres
    have he : -(n : ZMod p) = d := by
      rw [← rz, ← neg_mul]
      have hh : -(_root_.AbcTwoNinths.ExteriorE2.residue b hb avoid v.val : ZMod p) = 1 := by simpa using hres
      rw [hh, one_mul]
    refine ⟨-(n : ℤ), d, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hn ((ZMod.natCast_eq_zero_iff n p).2 (by exact_mod_cast (dvd_neg.mp h)))
    · intro h
      exact hd ((ZMod.natCast_eq_zero_iff d p).2 (by exact_mod_cast h))
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.mpr he
    · have hq := congrArg Units.val hsign.2
      simpa [hneg, rq, neg_div] using hq



/--
Every positive-index root of the selected lift represents a principal rational unit whose depth plus the valuation of the index equals the selected-side depth. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem nativeRootLte (t : _root_.AbcTwoNinths.Basic.Triple) {p g : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (hg : 0 < g) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let r := _root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s)
    let m := _root_.AbcTwoNinths.ExteriorE2.monomial (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d)
    ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
      (_root_.AbcTwoNinths.ExteriorE2.gammaStar r m w : ℚ) = _root_.AbcTwoNinths.Statement.selectedSource t ∧
      ∀ v : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w = v ^ g →
        ∃ N D : ℤ, ¬(p : ℤ) ∣ N ∧ ¬(p : ℤ) ∣ D ∧ (p : ℤ) ∣ N - D ∧
          (_root_.AbcTwoNinths.ExteriorE2.gammaStar r m v : ℚ) = (N : ℚ) / (D : ℚ) ∧
          (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℤ) =
            padicValRat p ((N : ℚ) / (D : ℚ) - 1) + (padicValNat p g : ℤ) := by
  intro s r m
  obtain ⟨w, hv, hw, _⟩ := _root_.AbcTwoNinths.Selection.selectedNative t hp
  refine ⟨w, hv, hw, ?_⟩
  intro v hgvec
  obtain ⟨N, D, hN, hD, hdiff, hrat⟩ :=
    signedPair (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s) v
  have hz : _root_.AbcTwoNinths.Statement.selectedSource t = ((N : ℚ) / (D : ℚ)) ^ g := by
    rw [← hw, hgvec, map_pow, Units.val_pow_eq_pow_val, hrat]
  have hne : _root_.AbcTwoNinths.Statement.selectedSource t ≠ 1 := by
    have ha : (0 : ℚ) < t.a := by exact_mod_cast t.apos
    have hb : (0 : ℚ) < t.b := by exact_mod_cast t.bpos
    have hc : (t.a : ℚ) + t.b = t.c := by exact_mod_cast t.add
    unfold _root_.AbcTwoNinths.Statement.selectedSource
    cases _root_.AbcTwoNinths.Statement.minRadicalSide t <;> intro h
    · exact (not_lt_of_ge (le_of_eq ((div_eq_iff hb.ne').mp h))) (by linarith)
    · exact (not_lt_of_ge (le_of_eq ((div_eq_iff ha.ne').mp h))) (by linarith)
    · have he := (div_eq_iff hb.ne').mp h
      linarith
  have hd0 : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hpow : N ^ g - D ^ g ≠ 0 := by
    intro h
    have he : (N : ℚ)^g = (D : ℚ)^g := by exact_mod_cast sub_eq_zero.mp h
    apply hne
    rw [hz, div_pow, he, div_self (pow_ne_zero _ hdq)]
  have hroot : N - D ≠ 0 := by
    intro h
    exact hpow (by rw [sub_eq_zero.mp h, sub_self])
  have hprime : p.Prime := Fact.out
  have hgt : 2 < p := Fact.out
  exact ⟨N, D, hN, hD, hdiff, hrat, _root_.AbcTwoNinths.Selection.selectedSourceDepthPower t hprime
    (hprime.odd_of_ne_two (by omega)) hp hg hD hN hdiff hroot hpow hz⟩

end

end AbcTwoNinths.Selection
