/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Adaptive Shell

The module constructs a positive shell margin and checks the numerical inequalities of the adaptive shell. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.shellSlack`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE2

section

/--
The auxiliary-prime scale M is the larger of one and p/H multiplied by exp(e x). This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def m (p H e x : ℝ) := max 1 (p/H) * Real.exp (e*x)

/--
The gap D0 is one third minus three times eta. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def gap (η : ℝ) := 1/3 - 3*η
/--
The auxiliary-prime margin e is one hundredth of D0. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def margin (η : ℝ) := _root_.AbcTwoNinths.ExteriorE2.gap η / 100
/--
The lower coefficient for the selected prime logarithm is one minus three times eta minus six times e. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def c₀ (η : ℝ) := 1 - 3*η - 6*_root_.AbcTwoNinths.ExteriorE2.margin η

/--
Collects the positivity, eta range, height and prime-logarithm bounds for the auxiliary-prime shell. This is used in the proof of Proposition 4.1 of the paper.
-/
structure Admissible (p H η x : ℝ) : Prop where
  hp : 0 < p
  hH : 0 < H
  hx : 0 < x
  eta_pos : 0 < η
  eta_lt : η < 1/9
  log_height : (1-3*η)*x ≤ Real.log H
  log_lo : _root_.AbcTwoNinths.ExteriorE2.c₀ η*x ≤ Real.log p
  log_hi : Real.log p ≤ x

/-- The auxiliary-prime margin is positive for eta below one ninth. -/
theorem marginPos {η : ℝ} (h : η < 1/9) : 0 < _root_.AbcTwoNinths.ExteriorE2.margin η := by
  unfold _root_.AbcTwoNinths.ExteriorE2.margin _root_.AbcTwoNinths.ExteriorE2.gap
  linarith

/--
The lower coefficient for the selected prime logarithm exceeds two thirds for eta below one ninth.
-/
theorem c₀Lower {η : ℝ} (h : η < 1/9) : 2/3 < _root_.AbcTwoNinths.ExteriorE2.c₀ η := by
  unfold _root_.AbcTwoNinths.ExteriorE2.c₀ _root_.AbcTwoNinths.ExteriorE2.margin _root_.AbcTwoNinths.ExteriorE2.gap
  linarith

/-- The auxiliary-prime scale is positive for all real inputs. -/
theorem MPos (p H e x : ℝ) : 0 < _root_.AbcTwoNinths.ExteriorE2.m p H e x := by
  exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Real.exp_pos _)

/-- The two orderings of p and H give the two logarithmic formulas for M. -/
theorem logBranches {p H e x : ℝ} (hp : 0 < p) (hH : 0 < H) :
    (p ≤ H → Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H e x) = e*x) ∧
    (H ≤ p → Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H e x) = Real.log p - Real.log H + e*x) := by
  constructor
  · intro h
    have h' : p / H ≤ 1 := (div_le_one hH).2 h
    simp [_root_.AbcTwoNinths.ExteriorE2.m, max_eq_left h']
  · intro h
    have h' : 1 ≤ p / H := (one_le_div hH).2 h
    rw [_root_.AbcTwoNinths.ExteriorE2.m, max_eq_right h', Real.log_mul (div_pos hp hH).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_div hp.ne' hH.ne']

/--
At the chosen margin, the logarithm of M lies above or at e x and strictly below half the prime logarithm minus e x. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem shellSlack {p H η x : ℝ} (a : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x) :
    _root_.AbcTwoNinths.ExteriorE2.margin η*x ≤ Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) ∧
    Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) + _root_.AbcTwoNinths.ExteriorE2.margin η*x < Real.log p/2 := by
  obtain ⟨hlo,hhi⟩ := _root_.AbcTwoNinths.ExteriorE2.logBranches (e := _root_.AbcTwoNinths.ExteriorE2.margin η) (x := x) a.hp a.hH
  rcases le_total p H with h | h
  · rw [hlo h]
    refine ⟨le_rfl, ?_⟩
    have hgap : 4*_root_.AbcTwoNinths.ExteriorE2.margin η < _root_.AbcTwoNinths.ExteriorE2.c₀ η := by
      unfold _root_.AbcTwoNinths.ExteriorE2.c₀ _root_.AbcTwoNinths.ExteriorE2.margin _root_.AbcTwoNinths.ExteriorE2.gap
      linarith [a.eta_pos, a.eta_lt]
    linarith [mul_lt_mul_of_pos_right hgap a.hx, a.log_lo]
  · rw [hhi h]
    refine ⟨by linarith [Real.log_le_log a.hH h], ?_⟩
    have hgap : 1/2 + 2*_root_.AbcTwoNinths.ExteriorE2.margin η < 1 - 3*η := by
      unfold _root_.AbcTwoNinths.ExteriorE2.margin _root_.AbcTwoNinths.ExteriorE2.gap
      linarith [a.eta_lt]
    linarith [mul_lt_mul_of_pos_right hgap a.hx, a.log_height, a.log_hi]

/--
The two shell comparisons bound the transverse slope ratio between half the margin and an explicit upper bound below one third.
-/
theorem transverseRatio {p H η x α t : ℝ} (a : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x)
    (hα : 0 ≤ α) (hαe : α < _root_.AbcTwoNinths.ExteriorE2.margin η)
    (htlo : Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x)/2 < t)
    (hthi : t ≤ α*x + Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x)) :
    _root_.AbcTwoNinths.ExteriorE2.margin η/2 < t / Real.log p ∧
    t / Real.log p ≤ 3*η + (α + _root_.AbcTwoNinths.ExteriorE2.margin η)/_root_.AbcTwoNinths.ExteriorE2.c₀ η ∧
    3*η + (α + _root_.AbcTwoNinths.ExteriorE2.margin η)/_root_.AbcTwoNinths.ExteriorE2.c₀ η < 3*η + _root_.AbcTwoNinths.ExteriorE2.gap η/2 ∧
    3*η + _root_.AbcTwoNinths.ExteriorE2.gap η/2 < 1/3 := by
  have hc : 0 < _root_.AbcTwoNinths.ExteriorE2.c₀ η := by linarith [_root_.AbcTwoNinths.ExteriorE2.c₀Lower a.eta_lt]
  have hl : 0 < Real.log p := lt_of_lt_of_le (mul_pos hc a.hx) a.log_lo
  have he := _root_.AbcTwoNinths.ExteriorE2.marginPos a.eta_lt
  have hsum : 0 ≤ α + _root_.AbcTwoNinths.ExteriorE2.margin η := by linarith
  have hscale : (α + _root_.AbcTwoNinths.ExteriorE2.margin η)*x ≤ ((α + _root_.AbcTwoNinths.ExteriorE2.margin η)/_root_.AbcTwoNinths.ExteriorE2.c₀ η)*Real.log p := by
    calc
      _ = ((α + _root_.AbcTwoNinths.ExteriorE2.margin η)/_root_.AbcTwoNinths.ExteriorE2.c₀ η)*(_root_.AbcTwoNinths.ExteriorE2.c₀ η*x) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left a.log_lo (div_nonneg hsum hc.le)
  refine ⟨(lt_div_iff₀ hl).2 ?_, (div_le_iff₀ hl).2 ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left a.log_hi he.le, (_root_.AbcTwoNinths.ExteriorE2.shellSlack a).1]
  · obtain ⟨hlo,hhi⟩ := _root_.AbcTwoNinths.ExteriorE2.logBranches (e := _root_.AbcTwoNinths.ExteriorE2.margin η) (x := x) a.hp a.hH
    rcases le_total p H with h | h
    · rw [hlo h] at hthi
      linarith [mul_nonneg a.eta_pos.le hl.le]
    · rw [hhi h] at hthi
      have hcoeff : 0 ≤ 1 - 3*η := by linarith [a.eta_lt]
      linarith [mul_le_mul_of_nonneg_left a.log_hi hcoeff, a.log_height]
  · apply add_lt_add_right
    apply (div_lt_iff₀ hc).2
    have hD : 0 < _root_.AbcTwoNinths.ExteriorE2.gap η := by unfold _root_.AbcTwoNinths.ExteriorE2.gap; linarith [a.eta_lt]
    have hbound := mul_lt_mul_of_pos_left (_root_.AbcTwoNinths.ExteriorE2.c₀Lower a.eta_lt) (half_pos hD)
    unfold _root_.AbcTwoNinths.ExteriorE2.margin at hαe ⊢
    linarith
  · unfold _root_.AbcTwoNinths.ExteriorE2.gap
    linarith [a.eta_lt]

/--
The fresh shell consists of primes above the square root of the scale and at most the scale that do not divide twice the radical. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def fresh (R : ℕ) (S : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊S⌋₊ + 1)).filter (fun q =>
    q.Prime ∧ Real.sqrt S < (q : ℝ) ∧ ¬ q ∣ 2*R)

/--
Membership in a shell of nonnegative scale is equivalent to primality, the two interval bounds and exclusion from the divisors of twice the radical.
-/
theorem memFresh {R q : ℕ} {S : ℝ} (hS : 0 ≤ S) :
    q ∈ _root_.AbcTwoNinths.ExteriorE2.fresh R S ↔ q.Prime ∧ Real.sqrt S < (q : ℝ) ∧ (q : ℝ) ≤ S ∧ ¬ q ∣ 2*R := by
  classical
  simp only [_root_.AbcTwoNinths.ExteriorE2.fresh, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hS]
  tauto

/--
A shell count at least S divided by four times log S supplies a fresh prime when S exceeds one.
-/
theorem freshWitness {R : ℕ} {S : ℝ} (h : 1 < S)
    (hcount : S/(4*Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ)) :
    ∃ q ∈ _root_.AbcTwoNinths.ExteriorE2.fresh R S, q.Prime ∧ Real.sqrt S < (q : ℝ) ∧ (q : ℝ) ≤ S ∧ ¬ q ∣ 2*R := by
  have hpos : (0 : ℝ) < (_root_.AbcTwoNinths.ExteriorE2.fresh R S).card :=
    lt_of_lt_of_le (div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos h))) hcount
  have hnat : 0 < (_root_.AbcTwoNinths.ExteriorE2.fresh R S).card := by exact_mod_cast hpos
  obtain ⟨q,hq⟩ := Finset.card_pos.mp hnat
  exact ⟨q,hq,(_root_.AbcTwoNinths.ExteriorE2.memFresh (by linarith)).1 hq⟩

end

end AbcTwoNinths.ExteriorE2
