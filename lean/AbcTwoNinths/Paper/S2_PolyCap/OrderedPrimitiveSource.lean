/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.OddSideKernelSource
public import AbcTwoNinths.Paper.S2_PolyCap.KernelDepthDichotomy
public import AbcTwoNinths.Paper.S2_PolyCap.MaximalPowerDivisorLength

/-!
# Ordered Primitive Source

The module supplies an ordered primitive source for the odd-side analysis. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.orderedPrimitiveSource`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
An ordered triple of height above two has a quadratic support-size bound or a primitive residue-kernel vector with controlled depth and height. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem orderedPrimitiveSource (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hH : 2 < t.logHeight) :
    let r := (t.a * t.b * t.c).primeFactors.card
    t.logHeight ≤ 192 * (r : ℝ)^2 ∨
      ∃ (p : ℕ) (S : Finset ℕ) (w : S → ℤ) (hq : ∀ q : S, Nat.Coprime q.val p),
        p.Prime ∧ 2 < p ∧ p ∣ t.radical ∧ 1 ≤ r ∧ S.card ≤ r ∧ S ⊆ t.radical.primeFactors ∧
        (∀ q ∈ S, q.Prime ∧ q ∣ t.a * t.b * t.c) ∧
        w ∈ (_root_.AbcTwoNinths.Basic.residue (fun q : S => q.val) hq).ker ∧
        (∀ (n : ℕ) (u : S → ℤ), u ∈ (_root_.AbcTwoNinths.Basic.residue (fun q : S => q.val) hq).ker →
          n • u = w → n = 1) ∧
        let z := ∏ q : S, (q.val : ℚ) ^ w q
        z ≠ 1 ∧ t.logHeight / (4 * (r : ℝ)) ≤ (padicValRat p (z - 1) : ℝ) * Real.log p ∧
        t.logHeight / (4 * (r : ℝ)) < _root_.AbcTwoNinths.Basic.padicRationalHeight z ∧ _root_.AbcTwoNinths.Basic.padicRationalHeight z ≤ 4 * t.logHeight := by
  let N := t.a * t.b * t.c
  let r := N.primeFactors.card
  have ha := t.apos
  have hb := t.bpos
  have habc := t.add
  have hc : 0 < t.c := by omega
  have hN : N ≠ 0 := by dsimp [N]; positivity
  obtain ⟨M, p, S, e, hq, hM, hpM, hp, hp2, hs, he, hg, hv, hL, hbound⟩ :=
    _root_.AbcTwoNinths.PolyCap.oddKernelSource t hab hH
  let _ : Fact p.Prime := ⟨hp⟩
  have hMN : M ∣ N := by
    rcases hM with rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · exact dvd_mul_left _ _
  have hpN := (Nat.dvd_of_mem_primeFactors hpM).trans hMN
  have hsub : M.primeFactors ⊆ N.primeFactors := by
    intro q hq'
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq',
      (Nat.dvd_of_mem_primeFactors hq').trans hMN, hN⟩
  have hr : 0 < r := Finset.card_pos.mpr ⟨p, hsub hpM⟩
  have hSN : S ⊆ N.primeFactors := fun j hj =>
    Nat.mem_primeFactors.mpr ⟨(hs j hj).1, (hs j hj).2, hN⟩
  have hSR : S ⊆ t.radical.primeFactors := by
    simpa only [_root_.AbcTwoNinths.Basic.Triple.radical, _root_.AbcTwoNinths.Basic.radical, Nat.primeFactors_prod_primeFactors] using hSN
  have hpR : p ∣ t.radical := Finset.dvd_prod_of_mem id (hsub hpM)
  let v : S → ℤ := fun q => e q.val
  let q : S → ℕ := fun q => q.val
  have hprod : (∏ i : S, (q i : ℚ) ^ v i) = ∏ i ∈ S, (i : ℚ) ^ e i :=
    Finset.prod_coe_sort S (fun i : ℕ => (i : ℚ) ^ e i)
  have hsum : (∑ i : S, |(v i : ℝ)| * Real.log (q i)) ≤ 4 * t.logHeight := by
    change (∑ i : S, (fun j : ℕ => |(e j : ℝ)| * Real.log j) i.val) ≤ _
    rwa [Finset.sum_coe_sort S (fun j : ℕ => |(e j : ℝ)| * Real.log j)]
  have hz : (∏ i : S, (q i : ℚ) ^ v i) ≠ 1 := by
    rw [hprod]
    intro hh
    simp [hh, padicValRat.zero] at hv
    have hf := hp.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hpM).2.2
      (Nat.dvd_of_mem_primeFactors hpM)
    omega
  have hvne : v ≠ 0 := by
    intro hh
    exact hz (by rw [hh]; simp)
  have hlog (i : S) : (2 : ℝ) / 3 ≤ Real.log (q i) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast (hs i.val i.property).1.two_le : (2 : ℝ) ≤ q i)
    linarith [Real.log_two_gt_d9]
  obtain ⟨k, w, hk, hkH, hw, hkw, hprim, hwL⟩ :=
    _root_.AbcTwoNinths.PolyCap.maximalDivisorLength (_root_.AbcTwoNinths.Basic.residue q hq).ker he hvne (fun i => Real.log (q i)) hlog hsum
  have hH0 : 0 < t.logHeight := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hdepth : t.logHeight / (2 * (r : ℝ)) ≤
      (padicValRat p ((∏ i : S, (q i : ℚ) ^ v i) - 1) : ℝ) * Real.log p := by
    rw [hprod]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mpr
    have hcard : (M.primeFactors.card : ℝ) ≤ r := by exact_mod_cast Finset.card_le_card hsub
    have hd0 : 0 ≤ (padicValRat p ((∏ i ∈ S, (i : ℚ) ^ e i) - 1) : ℝ) * Real.log p := by
      rw [hv]
      exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hp.one_le))
    calc
      _ ≤ 2 * (M.primeFactors.card : ℝ) * _ := hbound
      _ ≤ 2 * (r : ℝ) * _ := mul_le_mul_of_nonneg_right (by linarith) hd0
      _ = _ := mul_comm _ _
  rcases _root_.AbcTwoNinths.PolyCap.kernelDepthOrShallow hpOdd hk q hq (fun i => (hs i.val i.property).1.pos)
    v w hkw hw hH0 hr0 hkH hz hdepth hwL with hsh | hd
  · exact Or.inl hsh
  right
  refine ⟨p, S, w, hq, hp, hp2, hpR, hr, Finset.card_le_card hSN, hSR, hs, hw, hprim, ?_, hd⟩
  intro hh
  apply hz
  change k • w = v at hkw
  change (∏ i : S, (q i : ℚ) ^ w i) = 1 at hh
  rw [← hkw, _root_.AbcTwoNinths.PolyCap.monomialNsmul, hh, one_pow]

end

end AbcTwoNinths.PolyCap
