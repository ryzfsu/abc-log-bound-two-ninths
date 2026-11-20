/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.LogarithmicHeight
public import AbcTwoNinths.Paper.S1_Statement.LeastRadicalSide
public import AbcTwoNinths.Paper.S7_Terminal.IntegerDeterminantBounds

/-!
# Selected Axial Growth

The module computes the height along the selected direction and derives its lower bound from the axial growth estimate. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.selectedHeightExact`
* `AbcTwoNinths.Terminal.selectedAxialGrowth`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section



private theorem heightDiv {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    _root_.AbcTwoNinths.Terminal.rowHeightMax ((a : ℚ) / b) = max a b := by
  have hd : (0 : ℤ) < b := by exact_mod_cast hb
  have hc : Nat.Coprime (a : ℤ).natAbs (b : ℤ).natAbs := by simpa using hab
  have hn := Rat.num_div_eq_of_coprime hd hc
  have hden := Rat.den_div_eq_of_coprime hd hc
  push_cast at hn
  have hden' : ((a : ℚ) / b).den = b := Int.ofNat.inj hden
  simp [_root_.AbcTwoNinths.Terminal.rowHeightMax, hn, hden']

/--
The reduced height of the selected rational equals the larger summand when the selected side is c and equals c otherwise. This is used in Section 7 of the paper.
-/
theorem selectedHeightExact (t : _root_.AbcTwoNinths.Basic.Triple) :
    _root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Statement.selectedSource t) =
      if _root_.AbcTwoNinths.Statement.minRadicalSide t = .c then max t.a t.b else t.c := by
  have ha : t.a ≤ t.c := by rw [← t.add]; omega
  have hb : t.b ≤ t.c := by rw [← t.add]; omega
  have hca : t.c.Coprime t.a := by
    rw [← t.add, Nat.add_comm, Nat.coprime_add_self_left]
    exact t.coprime.symm
  have hcb : t.c.Coprime t.b := by
    rw [← t.add, Nat.coprime_add_self_left]
    exact t.coprime
  unfold _root_.AbcTwoNinths.Statement.selectedSource
  cases _root_.AbcTwoNinths.Statement.minRadicalSide t with
  | a => simp [heightDiv t.bpos hcb, max_eq_left hb]
  | b => simp [heightDiv t.apos hca, max_eq_left ha]
  | c =>
    rw [neg_div]
    have hn (z : ℚ) : _root_.AbcTwoNinths.Terminal.rowHeightMax (-z) = _root_.AbcTwoNinths.Terminal.rowHeightMax z := by simp [_root_.AbcTwoNinths.Terminal.rowHeightMax]
    simp [hn, heightDiv t.bpos t.coprime]

/-- The logarithmic height of the selected rational is at least H minus log 2. -/
theorem selectedHeightLower (t : _root_.AbcTwoNinths.Basic.Triple) :
    t.logHeight - Real.log 2 ≤ Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Statement.selectedSource t) : ℝ) := by
  have hnat : t.c ≤ 2 * _root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Statement.selectedSource t) := by
    rw [_root_.AbcTwoNinths.Terminal.selectedHeightExact]
    have := t.add
    have := le_max_left t.a t.b
    have := le_max_right t.a t.b
    split <;> omega
  have hc : 0 < (t.c : ℝ) := by exact_mod_cast (t.add ▸ Nat.add_pos_left t.apos t.b)
  have h := Real.log_le_log hc (show (t.c : ℝ) ≤ 2 * _root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Statement.selectedSource t) by
    exact_mod_cast hnat)
  rw [Real.log_mul (by norm_num) (by exact_mod_cast (_root_.AbcTwoNinths.Terminal.rowHeightMaxPos _).ne')] at h
  exact sub_le_iff_le_add'.mpr h

/--
At a common threshold, every eligible prime exceeds the prescribed lower bounds on its logarithm and on the ratio of selected logarithmic height to its logarithm. This is used in Section 7 of the paper.
-/
theorem selectedAxialGrowth {η : ℚ} {σ : ℝ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (L N : ℝ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ (t : _root_.AbcTwoNinths.Basic.Triple), _root_.AbcTwoNinths.Statement.High η X t →
      ∀ p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
        t.logHeight * Real.exp (-σ*t.thirdLogRadical) < (p : ℝ) →
          L ≤ Real.log p ∧
          N ≤ Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Statement.selectedSource t) : ℝ) / Real.log p := by
  let B := max 1 N
  let X := max (16 * B) (2 * L)
  have hB : 1 ≤ B := le_max_left _ _
  have hη' : (η : ℝ) < 1 / 9 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 hη.2
  have hr : 2/3 < _root_.AbcTwoNinths.Statement.highRate η := by unfold _root_.AbcTwoNinths.Statement.highRate; linarith
  have hrs : 1/2 ≤ _root_.AbcTwoNinths.Statement.highRate η - σ := by
    have := hσ.2
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget at this
    linarith
  refine ⟨X, (by dsimp [X]; apply le_trans _ (le_max_left _ _); linarith), ?_⟩
  intro t ht p hp hcut
  have hxB := (le_max_left (16 * B) (2 * L)).trans ht.1
  have hxL := (le_max_right (16 * B) (2 * L)).trans ht.1
  have hx : 0 ≤ t.thirdLogRadical := by linarith
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hℓ : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp'.one_lt)
  have hdiv : p ∣ _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) := Finset.dvd_prod_of_mem id hp
  have hrad : 0 < _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hpRad : (p : ℝ) ≤ _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) := by
    exact_mod_cast Nat.le_of_dvd hrad hdiv
  have hℓx := (Real.log_le_iff_le_exp (by exact_mod_cast hp'.pos)).2
    (hpRad.trans (_root_.AbcTwoNinths.Statement.minSideLeScale t))
  have hlow : Real.exp ((_root_.AbcTwoNinths.Statement.highRate η-σ)*t.thirdLogRadical) < (p : ℝ) := by
    rw [sub_mul, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    simpa [neg_mul] using
      (mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos (-σ*t.thirdLogRadical)).le).trans_lt hcut
  refine ⟨?_, (le_div_iff₀ hℓ).2 ?_⟩
  · have h := (Real.lt_log_iff_exp_lt (by exact_mod_cast hp'.pos)).2 hlow
    linarith [mul_le_mul_of_nonneg_right hrs hx]
  · have hlin := Real.add_one_le_exp (t.thirdLogRadical/4)
    have hs := mul_self_le_mul_self (by linarith : 0 ≤ t.thirdLogRadical/4+1) hlin
    rw [← Real.exp_add] at hs
    have he : t.thirdLogRadical/4 + t.thirdLogRadical/4 ≤ _root_.AbcTwoNinths.Statement.highRate η*t.thirdLogRadical := by
      linarith [mul_le_mul_of_nonneg_right hr.le hx]
    have hh := hs.trans ((Real.exp_le_exp.2 he).trans ht.2)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have htarget : B*t.thirdLogRadical ≤ t.logHeight - Real.log 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxB) hx]
    exact ((mul_le_mul_of_nonneg_right (le_max_right 1 N) hℓ.le).trans
      (mul_le_mul_of_nonneg_left hℓx (by linarith : 0 ≤ B))).trans
      (htarget.trans (_root_.AbcTwoNinths.Terminal.selectedHeightLower t))

end

end AbcTwoNinths.Terminal
