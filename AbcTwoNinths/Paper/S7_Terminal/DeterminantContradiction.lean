/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.IntegralDeterminantBounds
public import AbcTwoNinths.Paper.S7_Terminal.DiamondRowHeightSum
public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Determinant Contradiction

The module bounds generalized binomial entries and compares the two determinant estimates to derive a contradiction. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.engineFalse`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section

/--
The absolute binomial coefficient with integer argument is at most two to the sum of its absolute argument and its index.
-/
theorem chooseAbsLeTwoPow (y : ℤ) (k : ℕ) :
    |(Ring.choose y k : ℤ)| ≤ (2 : ℤ) ^ (y.natAbs + k) := by
  cases y with
  | ofNat n =>
    change |Ring.choose (n : ℤ) k| ≤ 2 ^ (n + k)
    rw [Ring.choose_natCast, abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (Nat.choose_le_two_pow n k).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right n k))
  | negSucc n =>
    change |Ring.choose (-(↑(n + 1) : ℤ)) k| ≤ 2 ^ (n + 1 + k)
    rw [Ring.choose_neg, show ((↑(n + 1) : ℤ) + ↑k - 1) = ↑(n + k) by push_cast; omega,
      Ring.choose_natCast, Units.smul_def]
    change |(↑(Int.negOnePow k) : ℤ) * (↑((n + k).choose k) : ℤ)| ≤ 2 ^ (n + 1 + k)
    rw [abs_mul]
    have hs : |(↑(Int.negOnePow k) : ℤ)| = 1 := by
      have h := Int.units_eq_one_or (Int.negOnePow k)
      rcases h with h | h <;> simp [h]
    rw [hs, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (Nat.choose_le_two_pow (n + k) k).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n + k ≤ n + 1 + k))




/--
Bounds an integer binomial coefficient in real norm using a height bound on its argument and a strict upper bound on its index.
-/
theorem chooseBoundOfHeight {y : ℤ} {k K : ℕ} {r : ℝ}
    (hy : |(y : ℝ)| ≤ r) (hk : k < K) :
    |((Ring.choose y k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (r + K) := by
  have h := _root_.AbcTwoNinths.Terminal.chooseAbsLeTwoPow y k
  have h' : |((Ring.choose y k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (y.natAbs + k) := by
    exact_mod_cast h
  rw [← Real.rpow_natCast] at h'
  apply h'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
  push_cast
  have he : (y.natAbs : ℝ) = |(y : ℝ)| := by
    cases y with
    | ofNat n => simp
    | negSucc n =>
      simp only [Int.natAbs_negSucc, Nat.cast_succ, Int.cast_negSucc]
      rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n])]
      ring
  rw [he]
  exact add_le_add hy (by exact_mod_cast hk.le)

/--
The row height budget contradicts the upper and lower bounds on the same nonzero determinant.
-/
theorem engineFalseOfRows {p K m : ℕ} [Fact p.Prime]
    (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter) (hp : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s))
    (hm : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1))
    (w : _root_.AbcTwoNinths.Terminal.Site) (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1) (sites : Finset _root_.AbcTwoNinths.Terminal.Site)
    (hc : 2*K-1 ≤ sites.card) (hl : Function.Injective (fun s : sites => s.val.2))
    {r U : ℝ} (hK : 0 < K) (hKm : 4*K ≤ 3*m)
    (hy : ∀ s ∈ sites ∪ sites.image (fun s => s + w), |(s.2 : ℝ)| ≤ r)
    (hh : ∀ sel : _root_.AbcTwoNinths.Terminal.Row K ↪ _root_.AbcTwoNinths.Terminal.Site, (∀ i, sel i ∈ sites ∪ sites.image (fun s => s + w)) →
      (∑ i, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ (sel i)) : ℝ)) ≤ U)
    (budget : U + Real.log ((2*K).factorial : ℝ) + (2*K : ℝ) * ((r + K) * Real.log 2)
      < (2/9 : ℝ) * (2*K : ℝ)^2 * Real.log (p : ℝ)) : False := by
  obtain ⟨sel, _, _, hupper, hlower⟩ :=
    _root_.AbcTwoNinths.Terminal.terminalBounds hK γ hp hm w hw sites hc hl
      (B := (2 : ℝ) ^ (r + K)) (Real.rpow_pos_of_pos (by norm_num) _)
      (fun s hs k => _root_.AbcTwoNinths.Terminal.chooseBoundOfHeight (hy s hs) k.isLt) hh
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hupper
  exact (not_lt_of_ge ((hlower hKm).trans hupper)) budget

/--
Ball counts, distinct second coordinates and a strict height budget exclude the translated row configuration. This is used in Section 7 of the paper.
-/
theorem engineFalse {p K m J : ℕ} [Fact p.Prime]
    (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter) (hp : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s))
    (hm : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1))
    (w : _root_.AbcTwoNinths.Terminal.Site) (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1)
    (ball : ℝ → Finset _root_.AbcTwoNinths.Terminal.Site) (g : _root_.AbcTwoNinths.Terminal.Site → ℝ)
    {A δ ρ t₀ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (ht : 0 < t₀)
    (mono : Monotone ball) (height : ∀ r s, s ∈ ball r → g s ≤ r)
    (heightY : ∀ s, |(s.2 : ℝ)| * t₀ ≤ g s)
    (HB : ∀ s, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ s) : ℝ) ≤ g s)
    (lower : ∀ r ≥ 0, A * (max (r-δ) 0)^2 ≤ ((ball r).card : ℝ))
    (upper : ∀ r ≥ 0, ((ball r).card : ℝ) ≤ A * (r+δ)^2)
    (translate : ∀ s ∈ ball ρ, s + w ∈ ball (ρ+δ))
    (labels : Function.Injective (fun s : ball ρ => s.val.2))
    (hK : 0 < K) (hKm : 4*K ≤ 3*m) (hJ : 0 < J)
    (hcount : ((2*K-1 : ℕ) : ℝ) ≤ A * (ρ-δ)^2)
    (budget : let S := ρ+δ
      A * (S*(S+δ)^2 - S^3/3 + S^3/(2*J) + δ*S^2) +
        Real.log ((2*K).factorial : ℝ) + (2*K : ℝ) * ((S/t₀ + K) * Real.log 2) <
        (2/9 : ℝ) * (2*K : ℝ)^2 * Real.log (p : ℝ)) : False := by
  classical
  let S := ρ+δ
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hS : 0 < S := by dsimp [S]; linarith
  have hc := lower ρ hρ
  rw [max_eq_left (sub_nonneg.mpr hδρ)] at hc
  have sub : ball ρ ∪ (ball ρ).image (fun s => s+w) ⊆ ball S := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact mono (show ρ ≤ S by dsimp [S]; linarith) hs
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      exact translate a ha
  refine _root_.AbcTwoNinths.Terminal.engineFalseOfRows γ hp hm w hw (ball ρ) (by exact_mod_cast hcount.trans hc)
    labels hK hKm (r := S/t₀) ?_ ?_ budget
  · intro s hs
    exact (le_div_iff₀ ht).mpr ((heightY s).trans (height S s (sub hs)))
  · intro sel hsel
    let F := Finset.univ.image sel
    have hF : F ⊆ ball S := by
      intro s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact sub (hsel i)
    have hsum := _root_.AbcTwoNinths.Terminal.ballRowSum ball g hA hδ.le hS mono height
      (fun s _ => (mul_nonneg (abs_nonneg _) ht.le).trans (heightY s))
      lower (upper S hS.le) J hJ F hF
    have hgg : (∑ i, g (sel i)) = ∑ s ∈ F, g s := by
      symm
      exact Finset.sum_image (fun a _ b _ hab => sel.injective hab)
    exact (Finset.sum_le_sum (fun i _ => HB (sel i))).trans (hgg ▸ hsum)

end

end AbcTwoNinths.Terminal
