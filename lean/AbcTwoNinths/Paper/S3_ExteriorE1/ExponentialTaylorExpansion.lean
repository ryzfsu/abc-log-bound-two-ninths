/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialSumDerivatives

/-!
# Exponential Taylor Expansion

The module gives the exact Taylor expansion used for the interpolation exponential sum. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.taylorExponentialSumExactExpansion`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The exponential sum at one equals its derivative of the prescribed order at a point of the closed unit interval divided by the factorial of that order. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem taylorExponentialSumExactExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) :
    let E := s.card * (s.card - 1) / 2 - ∑ i ∈ s, d i
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d 0 1 = _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d E t / (E.factorial : ℝ) := by
  intro E
  by_cases hE : E = 0
  · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [hE]⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hE
  let f := _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d 0
  have hf : ContDiff ℝ (n+1 : ℕ) f := by
    unfold f _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum
    fun_prop
  have h01 : (0 : ℝ) ≠ 1 := zero_ne_one
  have hu := uniqueDiffOn_uIcc h01
  have hz : taylorWithinEval f n (Set.uIcc 0 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro m hm
    have hm' : m < E := by simpa only [hn, Nat.succ_eq_add_one] using Finset.mem_range.mp hm
    have hc : ContDiffAt ℝ (m : ℕ) f 0 :=
      (hf.of_le (by exact_mod_cast (show m ≤ n+1 from by omega))).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hc (Set.left_mem_uIcc),
      _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumIteratedDerivAtZero s u l ε γ d m hm', smul_zero]
  obtain ⟨t, ht, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv h01 hf.contDiffOn
  refine ⟨t, ?_, ?_⟩
  · rw [Set.uIoo_of_le zero_le_one] at ht
    exact ⟨ht.1.le, ht.2.le⟩
  · rw [hz, sub_zero, sub_zero, one_pow, mul_one] at he
    rw [_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSumIteratedDeriv] at he
    simpa only [hn, Nat.succ_eq_add_one] using he

end

end AbcTwoNinths.ExteriorE1
