/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.VariableGridMinor
public import AbcTwoNinths.Basic.VariableGridBounds
public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Primitive Grid

The module proves the variable-grid depth estimate for primitive exponent pairs.

## Main results
* `AbcTwoNinths.Basic.unboundedPrimitiveGrid`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

/--
For coprime positive exponents, either the valuation is small or sufficient depth gives the grid determinant inequality.
-/
theorem unboundedPrimitiveGrid
    (p c d L J : ℕ) (a b : ℚ) (A B : ℝ) (hp : p.Prime) (hp' : 2 < p)
    (ha : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p b)
    (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent a b) (hc : c.Coprime d)
    (hc0 : 0 < c) (hd0 : 0 < d) (hL : 0 < L) (hJ : 0 < J)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (haH : _root_.AbcTwoNinths.Basic.rationalHeight a ≤ A * log p)
    (hbH : _root_.AbcTwoNinths.Basic.rationalHeight b ≤ B * log p) :
    let m0 := (padicValRat p (a^c-b^d) : ℝ)
    let V := (1 + sqrt (J : ℝ)) * sqrt ((L : ℝ)*(A*B))
    let N := ((J : ℝ)+1)*(L : ℝ)
    let U := (c : ℝ)/B + (d : ℝ)/A
    m0 < 1 + 2 * sqrt ((J : ℝ)*L*(A*B)) ∨
      (N ≤ m0 → ∃ M C : ℝ, 0 < M ∧ M ≤ V * U ∧ C ≤ V ∧
        ((J : ℝ)+1)*((L : ℝ)-1) <
          2 * log N / log p + (J : ℝ) * (log (exp 2 * M / J) / log p) + L*C) := by
  dsimp only
  let : Fact p.Prime := ⟨hp⟩
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  let R := _root_.AbcTwoNinths.Basic.edge L B A
  let S := _root_.AbcTwoNinths.Basic.edge L A B
  let R' := _root_.AbcTwoNinths.Basic.edge (J*L) B A
  let S' := _root_.AbcTwoNinths.Basic.edge (J*L) A B
  have hz₁ : L ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S) := by
    simpa [_root_.AbcTwoNinths.Basic.Rectangle, R, S] using (_root_.AbcTwoNinths.Basic.rectCard L B A hBp hAp).le
  have hz₂ : L*J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S') := by
    simpa [_root_.AbcTwoNinths.Basic.Rectangle, R', S', Nat.mul_comm L J] using _root_.AbcTwoNinths.Basic.rectCard (J*L) B A hBp hAp
  by_cases hz : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') c d)
  · right
    intro hm
    let M : ℝ := ((R+R')*d+(S+S')*c : ℕ)
    let C : ℝ := (((R+R' : ℕ) : ℝ)*A+((S+S' : ℕ) : ℝ)*B)/2
    have hM : 0 < (R+R')*d+(S+S')*c := by
      by_contra! h
      have hr : R' = 0 := by nlinarith
      have hs : S' = 0 := by nlinarith
      simp [hr, hs, _root_.AbcTwoNinths.Basic.Rectangle] at hz₂
      have hh := Nat.mul_pos hL hJ
      omega
    have hcost := _root_.AbcTwoNinths.Basic.variableCombinedCosts L J c d A B hAp hBp
    refine ⟨M, C, by dsimp [M]; exact_mod_cast hM, hcost.2, hcost.1, ?_⟩
    have hi₁ : log (max (a.num.natAbs : ℝ) (a.den : ℝ)) ≤ A * log p := by
      simpa [_root_.AbcTwoNinths.Basic.rationalHeight, Nat.cast_max] using haH
    have hi₂ : log (max (b.num.natAbs : ℝ) (b.den : ℝ)) ≤ B * log p := by
      simpa [_root_.AbcTwoNinths.Basic.rationalHeight, Nat.cast_max] using hbH
    have hm' : (((J+1)*L : ℕ) : ℤ) ≤ padicValRat p (a^c-b^d) := by
      exact_mod_cast hm
    have hh := _root_.AbcTwoNinths.Basic.injectiveBranchVar p J L c d R S R' S' a b ha.2 hb.2 hi hc hJ hL hz₁ hz₂ hz
      hm' C hM (by
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left hi₁ (Nat.cast_nonneg (R+R')),
          mul_le_mul_of_nonneg_left hi₂ (Nat.cast_nonneg (S+S'))])
    have hpJ : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    have hMp : M ≠ 0 := by dsimp [M]; exact_mod_cast hM.ne'
    have hlog : log (exp 2 * M / J) = 2 + log (M / J) := by
      rw [mul_div_assoc, log_mul (exp_ne_zero _) (div_ne_zero hMp hpJ), log_exp]
    rw [hlog]
    push_cast at hh
    simpa only [M, Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_div_assoc] using hh
  · left
    have hn : a^c ≠ b^d := by
      intro eq
      have he : a^(c : ℤ)*b^(-(d : ℤ)) = 1 := by
        rw [zpow_neg, zpow_natCast, zpow_natCast, eq, mul_inv_cancel₀ (pow_ne_zero _ hb.2.1)]
      exact hc0.ne' (by exact_mod_cast (hi _ _ he).1)
    have hex : ∃ i j : _root_.AbcTwoNinths.Basic.Rectangle R' S', _root_.AbcTwoNinths.Basic.nodeZ c d i = _root_.AbcTwoNinths.Basic.nodeZ c d j ∧ i ≠ j := by
      by_contra! h
      exact hz (fun _ _ he => h _ _ he)
    obtain ⟨i,j,hij,hne⟩ := hex
    apply _root_.AbcTwoNinths.Basic.variableDuplicateValuation (L := L) (J := J) a b A B hAp hBp hp' ha.2 hb.2
      haH hbH hc hc0 hd0 hn
      (Nat.le_of_lt_succ i.1.isLt) (Nat.le_of_lt_succ j.1.isLt)
      (Nat.le_of_lt_succ i.2.isLt) (Nat.le_of_lt_succ j.2.isLt) _ hij
    intro h
    exact hne (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))

end

end AbcTwoNinths.Basic
