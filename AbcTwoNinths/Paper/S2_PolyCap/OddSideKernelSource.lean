/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.OddSidePrincipalUnit
public import AbcTwoNinths.Paper.S2_PolyCap.FactorizationResidues

/-!
# Odd Side Kernel Source

The module constructs an odd-side source in the residue kernel from a primitive triple. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddKernelSource`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open scoped BigOperators

/--
An ordered triple of height greater than two supplies an odd prime and a residue-kernel monomial with prescribed depth and bounded weighted length. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem oddKernelSource (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hH : 2 < t.logHeight) :
    ∃ (M p : ℕ) (S : Finset ℕ) (e : ℕ → ℤ) (hq : ∀ q : S, Nat.Coprime q.val p),
      (M = t.b ∨ M = t.c) ∧ p ∈ M.primeFactors ∧ p.Prime ∧ 2 < p ∧
      (∀ q ∈ S, q.Prime ∧ q ∣ t.a * t.b * t.c) ∧
      (fun q : S => e q.val) ∈ (_root_.AbcTwoNinths.Basic.residue (fun q : S => q.val) hq).ker ∧
      _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p (∏ q ∈ S, (q : ℚ) ^ e q) ∧
      padicValRat p ((∏ q ∈ S, (q : ℚ) ^ e q) - 1) = (M.factorization p : ℤ) ∧
      (∑ q ∈ S, |(e q : ℝ)| * Real.log q) ≤ 4 * t.logHeight ∧
      t.logHeight ≤ 2 * (M.primeFactors.card : ℝ) *
        ((padicValRat p ((∏ q ∈ S, (q : ℚ) ^ e q) - 1) : ℝ) * Real.log p) := by
  obtain ⟨M, p, x, y, hM, hpM, hp, hp2, hx, hy, hxy, hpx, hpy, hxc, hyc,
    hxN, hyN, hg, hv, hb⟩ := _root_.AbcTwoNinths.PolyCap.oddPrincipalSource t hab hH
  let _ : Fact p.Prime := ⟨hp⟩
  let S := x.primeFactors ∪ y.primeFactors
  have hs (q : ℕ) (hq : q ∈ S) : q.Prime ∧ q ∣ t.a * t.b * t.c ∧ q ≠ p := by
    rcases Finset.mem_union.mp hq with hxq | hyq
    · have hqP := Nat.prime_of_mem_primeFactors hxq
      have hqd := Nat.dvd_of_mem_primeFactors hxq
      exact ⟨hqP, hqP.dvd_of_dvd_pow (hqd.trans hxN), fun h => hpx (h ▸ hqd)⟩
    · have hqP := Nat.prime_of_mem_primeFactors hyq
      have hqd := Nat.dvd_of_mem_primeFactors hyq
      exact ⟨hqP, hqP.dvd_of_dvd_pow (hqd.trans hyN), fun h => hpy (h ▸ hqd)⟩
  have hq (q : S) : Nat.Coprime q.val p := by
    apply (hs q.val q.property).1.coprime_iff_not_dvd.mpr
    exact fun h => (hs q.val q.property).2.2
      ((Nat.prime_dvd_prime_iff_eq (hs q.val q.property).1 hp).mp h)
  have hne : (x : ℚ) / y ≠ 1 := by
    intro h
    have he := (div_eq_iff (by positivity : (y : ℚ) ≠ 0)).mp h
    rw [one_mul] at he
    exact hxy (by exact_mod_cast he)
  have hdepth := hg.2.2.2.resolve_left hne
  obtain ⟨e, he, heq, hlen⟩ := _root_.AbcTwoNinths.PolyCap.kernelMonomialOfDepth hx.ne' hy.ne' hpy hdepth
    S (fun _ hh => hh) hq (fun q hh => (hs q hh).1.one_le)
  refine ⟨M, p, S, e, hq, hM, hpM, hp, hp2,
    fun q hh => ⟨(hs q hh).1, (hs q hh).2.1⟩, he, heq ▸ hg, heq ▸ hv, ?_, heq ▸ hb⟩
  change _ ≤ 4 * Real.log (t.c : ℝ)
  have hcx := Real.log_le_log (by exact_mod_cast hx : 0 < (x : ℝ))
    (by exact_mod_cast hxc : (x : ℝ) ≤ (t.c : ℝ) ^ 2)
  have hcy := Real.log_le_log (by exact_mod_cast hy : 0 < (y : ℝ))
    (by exact_mod_cast hyc : (y : ℝ) ≤ (t.c : ℝ) ^ 2)
  rw [Real.log_pow] at hcx hcy
  norm_num at hcx hcy
  linarith

end

end AbcTwoNinths.PolyCap
