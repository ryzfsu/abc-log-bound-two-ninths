/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.RankTwoCollisionBound
public import AbcTwoNinths.Paper.S2_PolyCap.PrimeSupportCount
public import AbcTwoNinths.Paper.S2_PolyCap.LogarithmicCountingBound

/-!
# Rank Two Height Inequality

The module proves the logarithmic height inequality in the rank-at-least-two case. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.masterInequalityOfRankGeTwo`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
A support of at least two primes yields a bounded support parameter satisfying the logarithmic height inequality. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem masterInequalityOfRankGeTwo (t : _root_.AbcTwoNinths.Basic.Triple) {p r : ℕ}
    (hp : p.Prime) (ho : 2 < p) (hr : 1 ≤ r) (hH : 2 < t.logHeight)
    (hW : 1 < t.logRadical) (hrW : (r : ℝ) ≤ 2 * t.logRadical) (hpR : p ∣ t.radical)
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (hSr : S.card ≤ r)
    (hS : S ⊆ t.radical.primeFactors) (haway : ∀ j : S, ¬ p ∣ j.val) (e : S → ℤ)
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue Subtype.val (_root_.AbcTwoNinths.Basic.awayCoprime hp Subtype.val haway)).ker)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn (_root_.AbcTwoNinths.Basic.residue Subtype.val (_root_.AbcTwoNinths.Basic.awayCoprime hp Subtype.val haway)).ker e)
    (hne : _root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e ≠ 1)
    (hh : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e) ≤ 4 * t.logHeight)
    (hlt : t.logHeight / (4 * (r : ℝ)) < _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e))
    (hdepth : t.logHeight / (4 * (r : ℝ)) ≤
      (padicValRat p (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e - 1) : ℝ) * log (p : ℝ)) :
    ∃ s : ℝ, 1 < t.logRadical ∧ 0 ≤ s ∧ s ≤ 2 * t.logRadical ∧ s ≤ 3 * t.logRadical / log t.logRadical ∧
      let Z := 1 + log (20 * t.logHeight)
      Z - (2 * s) * log Z ≤ 9 + 2 * log t.logRadical + t.logRadical + s * (24 + 3 * log t.logRadical) := by
  classical
  have hneS : (Finset.univ : Finset S).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_coe]
    omega
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j : S => (e j).natAbs) hneS
  let I := {j : S // j ≠ i}
  let E := (e i).natAbs
  have hI : Fintype.card I + 1 = S.card := by
    simpa only [Fintype.card_option, Fintype.card_coe] using
      Fintype.card_congr (Equiv.optionSubtypeNe i)
  have hi : 1 ≤ Fintype.card I := by omega
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hRpos : 0 < t.radical := Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hR3 : 3 ≤ t.radical := (show 3 ≤ p by omega).trans (Nat.le_of_dvd hRpos hpR)
  have hprime (j : S) : j.val.Prime := Nat.prime_of_mem_primeFactors (hS j.property)
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
    linarith [log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num), log_inv (2 : ℝ)]
  have hlogs : (∑ j : S, log (j.val : ℝ)) ≤ t.logRadical := by
    rw [Finset.sum_coe_sort S (fun q : ℕ => log (q : ℝ))]
    have h : (∑ q ∈ S, log (q : ℝ)) ≤ ∑ q ∈ t.radical.primeFactors, log (q : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro q hq _
      exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le)
    unfold _root_.AbcTwoNinths.Basic.Triple.logRadical _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical
    rw [Nat.cast_prod, log_prod]
    · unfold _root_.AbcTwoNinths.Basic.Triple.radical _root_.AbcTwoNinths.Basic.radical at h
      simpa only [Nat.primeFactors_prod_primeFactors] using h
    · exact fun q hq => by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hheight : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial Subtype.val e) ≤ (E : ℝ) * t.logRadical := by
    refine (_root_.AbcTwoNinths.PolyCap.ratHeightProdMonomial _ hprime Subtype.val_injective e).2.trans ?_
    calc
      _ ≤ ∑ j : S, (E : ℝ) * log (j.val : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hm := hmax j hj
        refine mul_le_mul_of_nonneg_right ?_ (log_nonneg (by exact_mod_cast (hprime j).one_le))
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
        exact_mod_cast hm
      _ ≤ _ := by rw [← Finset.mul_sum]; gcongr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hsize : t.logHeight < 4 * (r : ℝ) * t.logRadical * E := by
    have h := (div_lt_iff₀ (by positivity : 0 < 4 * (r : ℝ))).mp (hlt.trans_le hheight)
    nlinarith
  have hEp : 0 < (E : ℝ) := by
    by_contra! hz
    have hpos : 0 ≤ 4 * (r : ℝ) * t.logRadical := by positivity
    linarith [mul_nonpos_of_nonneg_of_nonpos hpos hz]
  have hcount := _root_.AbcTwoNinths.PolyCap.collisionCountBound hp ho hr hH Subtype.val hprime Subtype.val_injective
    haway e i he hprim hne hh hdepth
  have hcount' : (E : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * ∏ j : I,
      (⌈(Fintype.card I : ℝ) * log (j.val.val : ℝ) /
        (1 / (1920000 * (r : ℝ) * (1 + log (20 * t.logHeight)) ^ 2))⌉₊ : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using (Nat.cast_le.mpr hcount : (E : ℝ) ≤ _)
  have hcount'' : (E : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * ∏ j : I,
      (⌈1920000 * (r : ℝ) * (1 + log (20 * t.logHeight)) ^ 2 *
        (Fintype.card I : ℝ) * log (j.val.val : ℝ)⌉₊ : ℝ) := by
    convert hcount' using 3
    rw [div_div_eq_mul_div, div_one]
    congr 2
    ring
  have hple : ((p - 1 : ℕ) : ℝ) ≤ exp t.logRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.logRadical
    rw [exp_log (by exact_mod_cast hRpos)]
    exact_mod_cast (Nat.sub_le p 1).trans (Nat.le_of_dvd hRpos hpR)
  have hsr : (Fintype.card I : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (show Fintype.card I ≤ r by omega)
  have hsW := hsr.trans hrW
  have hsupp : (Fintype.card I : ℝ) ≤ 3 * t.logRadical / log t.logRadical := by
    have hsc := Finset.card_le_card hS
    exact (show (Fintype.card I : ℝ) ≤ (t.radical.primeFactors.card : ℝ) by
      exact_mod_cast (show Fintype.card I ≤ t.radical.primeFactors.card by omega)).trans
        (_root_.AbcTwoNinths.PolyCap.omegaLeThreeWDivLogW hR3)
  refine ⟨Fintype.card I, hW, by positivity, hsW, hsupp, ?_⟩
  apply _root_.AbcTwoNinths.PolyCap.masterRow r hH hW hrW hr hEp (by positivity) hple hsize
    (fun j : I => log (j.val.val : ℝ)) ?_ ?_ hcount'' hi hsW
  · intro j
    exact hlog2.trans (log_le_log (by norm_num) (by exact_mod_cast (hprime j.val).two_le))
  · intro j
    exact (Finset.single_le_sum (f := fun k : S => log (k.val : ℝ))
      (fun k _ => log_nonneg (by exact_mod_cast (hprime k).one_le)) (Finset.mem_univ j.val)).trans hlogs

end

end AbcTwoNinths.PolyCap
