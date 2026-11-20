/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Prime Support Count

The module bounds the prime-support count using a factorial comparison and a logarithmic mass estimate. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.omegaLeThreeWDivLogW`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
The factorial of the cardinality of a finite set of positive integers is at most their product.
-/
theorem cardFactorialLeProd (S : Finset ℕ) (hpos : ∀ x ∈ S, 1 ≤ x) :
    S.card.factorial ≤ ∏ x ∈ S, x := by
  generalize h : S.card = n
  induction n generalizing S with
  | zero => simp [Finset.card_eq_zero.mp h]
  | succ n ih =>
    have hn : S.Nonempty := Finset.card_pos.mp (by omega)
    let m := S.max' hn
    have hm : m ∈ S := S.max'_mem hn
    have hsubset : S ⊆ Finset.Icc 1 m := fun x hx =>
      Finset.mem_Icc.mpr ⟨hpos x hx, S.le_max' x hx⟩
    have hnm : n + 1 ≤ m := by
      simpa [h] using Finset.card_le_card hsubset
    have herase : (S.erase m).card = n := by
      rw [Finset.card_erase_of_mem hm, h]
      omega
    have hprod := ih (S.erase m) (fun x hx => hpos x (Finset.mem_of_mem_erase hx)) herase
    rw [Nat.factorial_succ, ← Finset.mul_prod_erase S (fun x => x) hm]
    exact Nat.mul_le_mul hnm hprod

/--
An integer $N\ge3$ has at most $3\log N/\log\log N$ distinct prime factors. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem omegaLeThreeWDivLogW {N : ℕ} (hN : 3 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ 3 * log (N : ℝ) / log (log (N : ℝ)) := by
  let W := log (N : ℝ)
  let L := log W
  let s := N.primeFactors.card
  change (s : ℝ) ≤ 3 * W / L
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hW : 1 < W := (lt_log_iff_exp_lt hNpos).2
    ((exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).trans_le
      (by exact_mod_cast hN : (3 : ℝ) ≤ N))
  have hL : 0 < L := log_pos hW
  by_contra! hbad
  have hs : 0 < (s : ℝ) := (by positivity : 0 < 3 * W / L).trans hbad
  have hfactN : s.factorial ≤ N :=
    (_root_.AbcTwoNinths.PolyCap.cardFactorialLeProd _ fun q hq => (Nat.prime_of_mem_primeFactors hq).one_le).trans
      (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N))
  have hfact : (s.factorial : ℝ) ≤ N := by exact_mod_cast hfactN
  have hpow : (s : ℝ) ^ s ≤ (N : ℝ) * exp (s : ℝ) :=
    ((div_le_iff₀ (by exact_mod_cast Nat.factorial_pos s : (0 : ℝ) < s.factorial)).mp
      (pow_div_factorial_le_exp (s : ℝ) hs.le s)).trans (by
        rw [mul_comm (exp (s : ℝ))]
        exact mul_le_mul_of_nonneg_right hfact (exp_pos _).le)
  have hlogpow := (log_le_log (pow_pos hs s) hpow)
  rw [log_pow, log_mul hNpos.ne' (exp_pos _).ne', log_exp] at hlogpow
  have hhalf : log L ≤ L / 2 := by
    have heq : L = (L / 2) * 2 := by ring
    conv_lhs => rw [heq, log_mul (by positivity) (by norm_num)]
    linarith [log_le_sub_one_of_pos (show 0 < L / 2 by positivity),
      log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)]
  have hlogbad := log_lt_log (by positivity : 0 < 3 * W / L) hbad
  rw [log_div (by positivity) hL.ne', log_mul (by norm_num) (by linarith : W ≠ 0)] at hlogbad
  have hlog3 : 1 < log (3 : ℝ) :=
    (lt_log_iff_exp_lt (by norm_num)).2 (exp_one_lt_d9.trans (by norm_num))
  have hlower : 1 + L / 2 < log (s : ℝ) := by
    change log 3 + L - log L < log (s : ℝ) at hlogbad
    linarith
  have hbig : 3 * W < (s : ℝ) * L := (div_lt_iff₀ hL).mp hbad
  change (s : ℝ) * log (s : ℝ) ≤ W + (s : ℝ) at hlogpow
  nlinarith [mul_lt_mul_of_pos_left hlower hs]

end

end AbcTwoNinths.PolyCap
