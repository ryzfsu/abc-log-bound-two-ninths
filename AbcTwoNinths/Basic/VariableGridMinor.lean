/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.InterpolationDeterminantDepth
public import AbcTwoNinths.Basic.LocalDepthHeightComparison
public import AbcTwoNinths.Basic.DeterminantLogBound
public import AbcTwoNinths.Basic.BinomialMinorNonvanishing
public import AbcTwoNinths.Basic.CenteredIndexWidth

/-!
# Variable Grid Minor

A nonzero selected variable-grid minor can be cleared to an integer with the same p-adic
valuation and an explicit logarithmic height bound. For injective labels, sufficiently deep
contact yields an inequality on the grid dimensions.

## Main results
* `AbcTwoNinths.Basic.selectedMinorLogVar`
* `AbcTwoNinths.Basic.injectiveBranchVar`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open scoped BigOperators
open Real

/--
Under the centered-sum bound, permuting the grid changes the weighted exponent sum by at most the quarter-width bound.
-/
theorem exactWidthVar (K L R : ℕ) (r : Fin K × Fin L → ℕ)
    (hr : ∀ j, r j ≤ R)
    (hcenter : (∑ j : Fin L, |(j.val : ℝ) - ((L : ℝ)-1)/2|) ≤ (L : ℝ)^2/4)
    (σ τ : Equiv.Perm (Fin K × Fin L)) :
    (∑ j, (σ j).2.val * r j) ≤ (∑ j, (τ j).2.val * r j) + (K*L*L*R)/4 := by
  have h := _root_.AbcTwoNinths.Basic.permutationExponentWidth (fun i : Fin K × Fin L => (i.2.val : ℝ))
    (fun i => (r i : ℝ)) (((L : ℝ)-1)/2) R σ.symm τ.symm
    (fun i => ⟨by positivity, by exact_mod_cast hr i⟩)
  have hc : (∑ i : Fin K × Fin L, |(i.2.val : ℝ) - ((L : ℝ)-1)/2|) ≤
      (K : ℝ) * ((L : ℝ)^2/4) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hcenter (by positivity)
  have hx (perm : Equiv.Perm (Fin K × Fin L)) :
      (∑ j, ((perm j).2.val : ℝ) * (r j : ℝ)) =
      ∑ i, (i.2.val : ℝ) * (r (perm.symm i) : ℝ) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp perm (fun i => (i.2.val : ℝ) * (r (perm.symm i) : ℝ)))
  have hle := (abs_le.mp h).2.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  rw [← hx σ, ← hx τ] at hle
  have hB : 4 * (∑ j, (σ j).2.val * r j) ≤ 4 * (∑ j, (τ j).2.val * r j) + K*L*L*R := by
    exact_mod_cast (show 4 * (∑ j, ((σ j).2.val : ℝ) * (r j : ℝ)) ≤
      4 * (∑ j, ((τ j).2.val : ℝ) * (r j : ℝ)) + (K : ℝ)*L*L*R by
      nlinarith only [hle])
  omega

open Real in
/--
A nonzero selected grid minor admits an integer with the same p-adic valuation and an explicit logarithmic height bound.
-/
theorem selectedMinorLogVar (p K L c d R S : ℕ) (hp : p.Prime)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0)
    (r s : Fin K × Fin L → ℕ) (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (hcenter : (∑ j : Fin L, |(j.val : ℝ) - ((L : ℝ)-1)/2|) ≤ (L : ℝ)^2/4)
    (hM : 0 < R*d+S*c)
    (hD : (_root_.AbcTwoNinths.Basic.actualEntry a b (fun j => j.1.val) (fun j => j.2.val) r s c d).det ≠ 0) :
    let D := (_root_.AbcTwoNinths.Basic.actualEntry a b (fun j => j.1.val) (fun j => j.2.val) r s c d).det
    let M := ((R*d+S*c : ℕ) : ℝ)
    ∃ Z : ℤ, Z ≠ 0 ∧ padicValRat p (Z : ℚ) = padicValRat p D ∧
      log (Z.natAbs : ℝ) ≤ log ((K*L).factorial : ℝ) +
        (L : ℝ) * ∑ i : Fin K, ((i.val : ℝ) * log M - log (i.val.factorial : ℝ)) +
        ((K : ℝ) * L^2 / 4) * ((R : ℝ) * log (max (a.num.natAbs : ℝ) (a.den : ℝ)) +
          (S : ℝ) * log (max (b.num.natAbs : ℝ) (b.den : ℝ))) := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  obtain ⟨la, ua, hea, hwa⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * r j) _ (_root_.AbcTwoNinths.Basic.exactWidthVar K L R r hr hcenter)
  obtain ⟨lb, ub, heb, hwb⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * s j) _ (_root_.AbcTwoNinths.Basic.exactWidthVar K L S s hs hcenter)
  obtain ⟨Z, hZ, hZb⟩ := _root_.AbcTwoNinths.Basic.selectedMinorBound a b ha hb
    (fun j => j.1.val) (fun j => j.2.val) r s c d R S la ua lb ub hr hs hea heb
  obtain ⟨hna, hpa⟩ := _root_.AbcTwoNinths.Basic.clearingUnit p hp a ha hva la ua
  obtain ⟨hnb, hpb⟩ := _root_.AbcTwoNinths.Basic.clearingUnit p hp b hb hvb lb ub
  have hZq : (Z : ℚ) ≠ 0 := by rw [hZ]; exact mul_ne_zero (mul_ne_zero hna hnb) hD
  have hZi : Z ≠ 0 := by exact_mod_cast hZq
  refine ⟨Z, hZi, ?_, ?_⟩
  · rw [hZ, padicValRat.mul (mul_ne_zero hna hnb) hD, padicValRat.mul hna hnb,
      hpa, hpb, zero_add, zero_add]
  · let M : ℝ := ((R*d+S*c : ℕ) : ℝ)
    let A := log (max (a.num.natAbs : ℝ) (a.den : ℝ))
    let B := log (max (b.num.natAbs : ℝ) (b.den : ℝ))
    let F (j : Fin K × Fin L) := M^(j.1.val) / (j.1.val.factorial : ℝ)
    have hMp : 0 < M := by dsimp [M]; exact_mod_cast hM
    have hFp (j : Fin K × Fin L) : 0 < F j := by
      dsimp [F]
      exact div_pos (pow_pos hMp _) (by positivity)
    have hprod : 0 < ∏ j, F j := Finset.prod_pos (fun j _ => hFp j)
    have hfac : 0 < ((K*L).factorial : ℝ) := by positivity
    have hZa : (0 : ℝ) < Z.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hZi
    change (Z.natAbs : ℝ) ≤ ((Fintype.card (Fin K × Fin L)).factorial : ℝ) *
      (∏ j, F j) * exp ((ua-la : ℕ) * A + (ub-lb : ℕ) * B) at hZb
    simp only [Fintype.card_prod, Fintype.card_fin] at hZb
    have hlog := log_le_log hZa hZb
    rw [log_mul (mul_ne_zero hfac.ne' hprod.ne') (exp_ne_zero _),
      log_mul hfac.ne' hprod.ne', log_exp, log_prod (fun j _ => (hFp j).ne')] at hlog
    have hgroup : (∑ j, log (F j)) =
        (L : ℝ) * ∑ i : Fin K, ((i.val : ℝ) * log M - log (i.val.factorial : ℝ)) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [F, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [log_div (pow_ne_zero _ hMp.ne') (by positivity), log_pow]
    rw [hgroup] at hlog
    have hA : 0 ≤ A := log_nonneg ((by exact_mod_cast a.den_pos : (1 : ℝ) ≤ a.den).trans
      (le_max_right _ _))
    have hB : 0 ≤ B := log_nonneg ((by exact_mod_cast b.den_pos : (1 : ℝ) ≤ b.den).trans
      (le_max_right _ _))
    have hwa' : ((ua-la : ℕ) : ℝ) ≤ ((K : ℝ)*L^2/4)*(R : ℝ) := by
      have hx : 4 * (ua-la) ≤ K*L*L*R := by omega
      have hx' : 4 * ((ua-la : ℕ) : ℝ) ≤ (K : ℝ)*L*L*R := by exact_mod_cast hx
      nlinarith only [hx']
    have hwb' : ((ub-lb : ℕ) : ℝ) ≤ ((K : ℝ)*L^2/4)*(S : ℝ) := by
      have hx : 4 * (ub-lb) ≤ K*L*L*S := by omega
      have hx' : 4 * ((ub-lb : ℕ) : ℝ) ≤ (K : ℝ)*L*L*S := by exact_mod_cast hx
      nlinarith only [hx']
    change log (Z.natAbs : ℝ) ≤ log ((K*L).factorial : ℝ) +
      (L : ℝ) * ∑ i : Fin K, ((i.val : ℝ) * log M - log (i.val.factorial : ℝ)) +
      ((K : ℝ)*L^2/4)*((R : ℝ)*A+(S : ℝ)*B)
    nlinarith [mul_le_mul_of_nonneg_right hwa' hA, mul_le_mul_of_nonneg_right hwb' hB]

/--
For positive grid length, twice the determinant depth exponent equals the grid size times the number of first-coordinate indices times one less than the length.
-/
theorem twiceEJL (J L : ℕ) (hL : 0 < L) :
    2 * (_root_.AbcTwoNinths.Basic.Ejl J L : ℝ) = (((J+1)*L : ℕ) : ℝ)*(J+1)*((L : ℝ)-1) := by
  let N := (J+1)*L
  have hN : J+1 ≤ N := by
    dsimp [N]
    simpa using Nat.mul_le_mul_left (J+1) (show 1 ≤ L by omega)
  have even_consec (n : ℕ) : (n*(n-1)) % 2 = 0 := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [Nat.mul_mod, Nat.add_mod n 1]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with h | h <;> simp [h]
  have h1 : 2*(N*(N-1)/2) = N*(N-1) := by
    have := even_consec N
    omega
  have h2 : 2*((J+1)*J/2) = (J+1)*J := by
    have := even_consec (J+1)
    rw [Nat.add_sub_cancel] at this
    omega
  have h3 : L*((J+1)*J/2) ≤ N*(N-1)/2 := by
    have hh : 2 * (L*((J+1)*J/2)) ≤ 2 * (N*(N-1)/2) := by
      rw [← mul_assoc, mul_comm 2 L, mul_assoc, h1, h2]
      calc
        L * ((J+1)*J) = N*J := by dsimp [N]; ring
        _ ≤ _ := Nat.mul_le_mul_left N (by omega)
    exact Nat.le_of_mul_le_mul_left hh (by decide)
  have h4 : 2 * _root_.AbcTwoNinths.Basic.Ejl J L + N*J = N*(N-1) := by
    change 2*(N*(N-1)/2 - L*((J+1)*J/2)) + N*J = _
    have hh : 2*(L*((J+1)*J/2)) = N*J := by
      rw [← mul_assoc, mul_comm 2 L, mul_assoc, h2]
      dsimp [N]
      ring
    rw [Nat.mul_sub, h1, hh]
    omega
  have hN0 : 1 ≤ N := by omega
  have hc := congrArg (fun x : ℕ => (x : ℝ)) h4
  push_cast [Nat.cast_sub hN0] at hc
  change 2 * (_root_.AbcTwoNinths.Basic.Ejl J L : ℝ) = (N : ℝ)*(J+1)*((L : ℝ)-1)
  have hNe : (N : ℝ) = ((J : ℝ)+1)*L := by simp [N]
  rw [hNe] at hc ⊢
  linarith only [hc]

/--
Injectivity on the second rectangle and sufficient p-adic contact give a strict logarithmic bound for the variable grid dimensions.
-/
theorem injectiveBranchVar (p J L c d R S R' S' : ℕ) [Fact p.Prime]
    (a b : ℚ) (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (hi : ∀ m n : ℤ, a ^ m * b ^ n = 1 → m = 0 ∧ n = 0)
    (hc : c.Coprime d) (hJ : 0 < J) (hL : 0 < L)
    (h₁ : L ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S))
    (h₂ : L*J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S'))
    (hz : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') c d))
    (hN : (((J+1)*L : ℕ) : ℤ) ≤ padicValRat p (a^c-b^d))
    (W : ℝ) (hM : 0 < (R+R')*d+(S+S')*c)
    (hW : ((R+R' : ℕ) : ℝ) * log (max (a.num.natAbs : ℝ) (a.den : ℝ)) +
      ((S+S' : ℕ) : ℝ) * log (max (b.num.natAbs : ℝ) (b.den : ℝ)) ≤ 2*W*log p) :
    ((J : ℝ)+1)*((L : ℝ)-1) <
      2*log (((J+1)*L : ℕ) : ℝ)/log p +
      (J : ℝ)*(2+log (((((R+R')*d+(S+S')*c : ℕ) : ℝ))/J))/log p + (L : ℝ)*W := by
  classical
  have hp : p.Prime := Fact.out
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  obtain ⟨f,hf⟩ := _root_.AbcTwoNinths.Basic.rectangleBinomialMinor a b ha.1 hb.1 hi h₁ h₂ hz
  let r : _root_.AbcTwoNinths.Basic.Rows J L → ℕ := fun i => (f i).1.val
  let s : _root_.AbcTwoNinths.Basic.Rows J L → ℕ := fun i => (f i).2.val
  let D := (_root_.AbcTwoNinths.Basic.actualEntry a b (fun i : _root_.AbcTwoNinths.Basic.Rows J L => i.1.val) (fun i => i.2.val) r s c d).det
  have hD : D ≠ 0 := by
    convert hf using 2
    apply Matrix.ext
    intro i j
    change (Nat.choose (r j*d+s j*c) i.1.val : ℚ) * a^(i.2.val*r j) * b^(i.2.val*s j) =
      (Nat.choose (r j*d+s j*c) i.1.val : ℚ) * (a^(r j)*b^(s j))^i.2.val
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc,
      mul_comm (r j) i.2.val, mul_comm (s j) i.2.val]
  have hr (i : _root_.AbcTwoNinths.Basic.Rows J L) : r i ≤ R+R' := Nat.le_of_lt_succ (f i).1.isLt
  have hs (i : _root_.AbcTwoNinths.Basic.Rows J L) : s i ≤ S+S' := Nat.le_of_lt_succ (f i).2.isLt
  have hcontact : _root_.AbcTwoNinths.Basic.RatCongruent p ((J+1)*L) (a^c) (b^d) := Or.inr hN
  have hv := _root_.AbcTwoNinths.Basic.actualDetDepth p J L c d a b hc ha hb hcontact r s
  have hvD : (_root_.AbcTwoNinths.Basic.Ejl J L : ℤ) ≤ padicValRat p D := by
    simpa [sub_zero] using hv.resolve_left hD
  obtain ⟨Z,hZ,hZv,hZlog⟩ := _root_.AbcTwoNinths.Basic.selectedMinorLogVar p (J+1) L c d (R+R') (S+S') hp
    a b ha.1 hb.1 ha.2.1 hb.2.1 r s hr hs (_root_.AbcTwoNinths.Basic.widthBound L) hM hD
  have hd := _root_.AbcTwoNinths.Basic.integerLogOfDepth p (_root_.AbcTwoNinths.Basic.Ejl J L) hp Z hZ (hZv.symm ▸ hvD)
  apply _root_.AbcTwoNinths.Basic.archBridge J L (_root_.AbcTwoNinths.Basic.Ejl J L) p _ W _ hJ hL hp1
    (by exact_mod_cast hM) (_root_.AbcTwoNinths.Basic.twiceEJL J L hL) ?_ (hd.trans hZlog)
  have hnonneg : 0 ≤ (((J+1 : ℕ) : ℝ) * (L : ℝ)^2/4) := by positivity
  convert mul_le_mul_of_nonneg_left hW hnonneg using 1
  push_cast
  ring

end

end AbcTwoNinths.Basic
