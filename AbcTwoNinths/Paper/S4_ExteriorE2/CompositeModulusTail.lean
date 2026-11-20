/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffBudget
public import AbcTwoNinths.Paper.S4_ExteriorE2.TailOnset

/-!
# Composite Modulus Tail

Derives the eventual small-prime valuation bound from the exclusion of deep composite moduli. It
supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.e2TailOfTightModulusExclusion`
* `AbcTwoNinths.ExteriorE2.generatorLossLe`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/-- The tight modulus exclusion. This is used in the proof of Proposition 4.1 of the paper. -/
def TightModulusExclusion (η : ℚ) (σ κ X : ℝ) : Prop :=
  ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t →
    ∀ M L : ℕ, 2 ≤ M → 0 < L →
      M ^ L ∣ _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t) →
      (¬ 2 ∣ M ∨ 4 ∣ M) →
      (M : ℝ) ≤ t.logHeight * Real.exp (-σ * t.thirdLogRadical) →
      (Real.log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ Real.log (M : ℝ) →
      κ * t.logHeight / 16 ≤ (L : ℝ) * Real.log (M : ℝ) → False

/--
Excluding tight moduli at height threshold `X` gives a uniform small-prime mass bound for
ordered high triples beyond some nonnegative threshold.
-/
theorem compositeModulusTailE2TailOfTightModulusExclusion {η : ℚ} {σ κ X : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ)
    (hκ : 0 < κ)
    (hlocal : _root_.AbcTwoNinths.ExteriorE2.TightModulusExclusion η σ κ X) :
    ∃ Y : ℝ, 0 ≤ Y ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η Y t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t := by
  let X' := max X (2 * Real.log (4 : ℝ))
  obtain ⟨Y, hY, _, htail⟩ := _root_.AbcTwoNinths.ExteriorE2.enlargeHighForHeight hη X' ((16 / κ) ^ 2)
  refine ⟨Y, hY, fun t hord ht => ?_⟩
  obtain ⟨ht', hstart⟩ := htail t ht
  by_contra hb
  obtain ⟨M, L, hM, hL, _, hd, hp, hc, hlo, hm⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.e2ViolationTightModulus t hη hσ hκ (le_max_right _ _) ht' hstart hb
  have htX : _root_.AbcTwoNinths.Statement.High η X t := ⟨(le_max_left _ _).trans ht'.1, ht'.2⟩
  exact hlocal t hord htX M L hM hL hd hp hc hlo hm

/--
Tight modulus exclusion at the prescribed cutoff and margin for every admissible `η` yields
admissible parameters and a threshold for the eventual small-prime mass bound.
-/
theorem e2TailOfTightModulusExclusion
    (hlocal : ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
      ∃ X : ℝ, _root_.AbcTwoNinths.ExteriorE2.TightModulusExclusion η (_root_.AbcTwoNinths.Statement.cutoffBudget η)
        ((1 - 9 * (η : ℝ)) / 32) X) :
    ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
      ∃ σ κ X : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ ∧ _root_.AbcTwoNinths.Statement.admissibleMargin η κ ∧
        0 ≤ X ∧
        (∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) := by
  intro η hη
  have hη' : (η : ℝ) < 1 / 9 := by
    have hq := (Rat.cast_lt (K := ℝ)).2 hη.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η (_root_.AbcTwoNinths.Statement.cutoffBudget η) := by
    refine ⟨?_, le_rfl⟩
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget _root_.AbcTwoNinths.Statement.highRate
    linarith
  have hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η ((1 - 9 * (η : ℝ)) / 32) := by
    unfold _root_.AbcTwoNinths.Statement.admissibleMargin
    constructor <;> linarith
  obtain ⟨X, hX⟩ := hlocal η hη
  obtain ⟨Y, hY, htail⟩ := _root_.AbcTwoNinths.ExteriorE2.compositeModulusTailE2TailOfTightModulusExclusion hη hσ hκ.1 hX
  exact ⟨_root_.AbcTwoNinths.Statement.cutoffBudget η, _, Y, hσ, hκ, hY, htail⟩

/--
If the logarithm `l` is at most `log H` and `L * l` carries mass at least `κ * H / 16` ,
then `H ≥ (32 * N / κ) ^ 2` forces `L ≥ N` .
-/
theorem depthGeOfHeightOnset {κ H l N : ℝ} {L : ℕ}
    (hκ : 0 < κ) (hH : 0 < H) (hN : 0 ≤ N) (hl : l ≤ Real.log H)
    (hstart : (32 * N / κ) ^ 2 ≤ H)
    (hmass : κ * H / 16 ≤ (L : ℝ) * l) : N ≤ (L : ℝ) := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.2 hH
  have hsq := Real.sq_sqrt hH.le
  have hlog : Real.log H ≤ 2 * Real.sqrt H := by
    calc
      Real.log H = Real.log ((Real.sqrt H) ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt H) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * Real.sqrt H := by linarith [Real.log_le_sub_one_of_pos hs]
  have hroot : 32 * N / κ ≤ Real.sqrt H :=
    (Real.le_sqrt (by positivity) hH.le).2 hstart
  have hbudget := (div_le_iff₀ hκ).1 hroot
  have hmass' : κ * H / 16 ≤ (L : ℝ) * (2 * Real.sqrt H) :=
    hmass.trans (mul_le_mul_of_nonneg_left (hl.trans hlog) (by positivity))
  apply (mul_le_mul_iff_right₀ hs).1
  nlinarith [mul_le_mul_of_nonneg_right hbudget hs.le]

/--
Beyond a uniform height threshold, the two-sided cutoff and mass bounds on `M, L` imply
`M ≥ 3` , `t.thirdLogRadical ≤ 4 * log M` , and `L ≥ N` .
-/
theorem e2ModulusNumericOnset {η : ℚ} {σ κ X N : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : 0 < κ) (hN : 0 ≤ N) :
    ∃ Y : ℝ, X ≤ Y ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, _root_.AbcTwoNinths.Statement.High η Y t →
      ∀ M L : ℕ, 2 ≤ M →
        (M : ℝ) ≤ t.logHeight * Real.exp (-σ * t.thirdLogRadical) →
        (Real.log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ Real.log (M : ℝ) →
        κ * t.logHeight / 16 ≤ (L : ℝ) * Real.log (M : ℝ) →
        3 ≤ M ∧ t.thirdLogRadical ≤ 4 * Real.log (M : ℝ) ∧ N ≤ (L : ℝ) := by
  let X' := max X (4 * Real.log (3 : ℝ))
  obtain ⟨Y, _, hXY, htail⟩ := _root_.AbcTwoNinths.ExteriorE2.enlargeHighForHeight hη X' ((32 * N / κ) ^ 2)
  refine ⟨Y, (le_max_left _ _).trans hXY, fun t ht M L hM hc hlo hm => ?_⟩
  obtain ⟨ht', hstart⟩ := htail t ht
  have hx := (le_max_right X (4 * Real.log (3 : ℝ))).trans ht'.1
  have hx0 : 0 ≤ t.thirdLogRadical :=
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))).trans hx
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le ht'.2
  have hη' : (η : ℝ) < 1 / 9 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 hη.2
  have hrate : (1 : ℝ) / 2 ≤ _root_.AbcTwoNinths.Statement.highRate η - σ := by
    have hs := hσ.2
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget at hs
    unfold _root_.AbcTwoNinths.Statement.highRate at hs ⊢
    linarith
  have hlogH := (Real.le_log_iff_exp_le hH).2 ht'.2
  have hxl : t.thirdLogRadical ≤ 4 * Real.log (M : ℝ) := by
    linarith [mul_le_mul_of_nonneg_right hrate hx0]
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM3 : 3 ≤ M := by
    have h : Real.log 3 ≤ Real.log (M : ℝ) := by linarith
    exact_mod_cast (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 3) hMp).1 h
  have hMle : (M : ℝ) ≤ t.logHeight := by
    have hexp : Real.exp (-σ * t.thirdLogRadical) ≤ 1 := Real.exp_le_one_iff.2 (by
      have hp := mul_nonneg hσ.1.le hx0
      linarith)
    exact hc.trans (mul_le_of_le_one_right hH.le hexp)
  exact ⟨hM3, hxl, _root_.AbcTwoNinths.ExteriorE2.depthGeOfHeightOnset hκ hH hN
    (Real.log_le_log hMp hMle) hstart hm⟩

/--
An upper bound `64 / κ` on the multiplicity `g` also bounds its integer base-two logarithm.
-/
theorem generatorLossLe {g : ℕ} {κ : ℝ} (hg : (g : ℝ) ≤ 64 / κ) :
    (Nat.log 2 g : ℝ) ≤ 64 / κ := by
  have h : Nat.log 2 g ≤ g :=
    (Nat.log_le_self (b := 2) (x := g))
  exact (show (Nat.log 2 g : ℝ) ≤ (g : ℝ) by exact_mod_cast h).trans hg

end

end AbcTwoNinths.ExteriorE2
