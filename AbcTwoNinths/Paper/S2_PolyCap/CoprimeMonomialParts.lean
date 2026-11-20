/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ExactMonomialHeights
public import AbcTwoNinths.Basic.PrincipalUnitLengthFloor

/-!
# Coprime Monomial Parts

The module writes signed prime monomials as coprime quotients and computes their rational heights. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.logLtRatHeightOfGp`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- The prod monomial. This is used in the proof of Proposition 2.1 of the paper. -/
noncomputable def prodMonomial {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℤ) : ℚ :=
  ∏ j, (q j : ℚ) ^ e j

/-- The pos part nat. This is used in the proof of Proposition 2.1 of the paper. -/
def posPartNat {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℤ) : ℕ :=
  ∏ j, q j ^ (e j).toNat

/-- The neg part nat. This is used in the proof of Proposition 2.1 of the paper. -/
def negPartNat {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℤ) : ℕ :=
  _root_.AbcTwoNinths.PolyCap.posPartNat q (-e)

/-- The positive and negative exponent products of distinct primes are positive and coprime
and give the numerator and denominator of the monomial in lowest terms. -/
theorem prodMonomialEqDivCoprime {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) (e : ι → ℤ) :
    let P := _root_.AbcTwoNinths.PolyCap.posPartNat q e
    let Q := _root_.AbcTwoNinths.PolyCap.negPartNat q e
    0 < P ∧ 0 < Q ∧ P.Coprime Q ∧
    _root_.AbcTwoNinths.PolyCap.prodMonomial q e = (P : ℚ) / (Q : ℚ) ∧
    (_root_.AbcTwoNinths.PolyCap.prodMonomial q e).num.natAbs = P ∧ (_root_.AbcTwoNinths.PolyCap.prodMonomial q e).den = Q := by
  dsimp only
  have hpos (b : ι → ℤ) : 0 < _root_.AbcTwoNinths.PolyCap.posPartNat q b :=
    Finset.prod_pos fun j _ => pow_pos (hq j).pos _
  have hcop : (_root_.AbcTwoNinths.PolyCap.posPartNat q e).Coprime (_root_.AbcTwoNinths.PolyCap.negPartNat q e) := by
    unfold _root_.AbcTwoNinths.PolyCap.negPartNat _root_.AbcTwoNinths.PolyCap.posPartNat
    apply Nat.coprime_prod_left_iff.mpr
    intro i _
    apply Nat.coprime_prod_right_iff.mpr
    intro j _
    by_cases h : i = j
    · subst j
      by_cases hs : 0 ≤ e i
      · simp [Int.toNat_eq_zero.mpr (show -e i ≤ 0 by omega)]
      · simp [Int.toNat_eq_zero.mpr (show e i ≤ 0 by omega)]
    · exact (((Nat.coprime_primes (hq i) (hq j)).mpr (fun he => h (hinj he))).pow_left _).pow_right _
  have hsplit : _root_.AbcTwoNinths.PolyCap.prodMonomial q e = (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℚ) / (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℚ) := by
    simp only [_root_.AbcTwoNinths.PolyCap.prodMonomial, _root_.AbcTwoNinths.PolyCap.posPartNat, _root_.AbcTwoNinths.PolyCap.negPartNat, Nat.cast_prod, Nat.cast_pow,
      ← Finset.prod_div_distrib, Pi.neg_apply]
    apply Finset.prod_congr rfl
    intro j _
    have hne : (q j : ℚ) ≠ 0 := by exact_mod_cast (hq j).ne_zero
    have he : e j = ((e j).toNat : ℤ) - ((-e j).toNat : ℤ) := by omega
    conv_lhs => rw [he, zpow_sub₀ hne]
    simp only [zpow_natCast]
  have hd : 0 < (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℤ) := by exact_mod_cast hpos (-e)
  have hc : (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℤ).natAbs.Coprime (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℤ).natAbs := by simpa using hcop
  refine ⟨hpos e, hpos (-e), hcop, hsplit, ?_, ?_⟩
  · rw [hsplit]
    simpa using congrArg Int.natAbs (Rat.num_div_eq_of_coprime hd hc)
  · rw [hsplit]
    have hden := Rat.den_div_eq_of_coprime hd hc
    simp only [Int.cast_natCast] at hden
    exact_mod_cast hden

/-- A rational monomial on distinct primes is one exactly when every exponent is zero. -/
theorem prodMonomialEqOneIff {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) (e : ι → ℤ) :
    _root_.AbcTwoNinths.PolyCap.prodMonomial q e = 1 ↔ ∀ j, e j = 0 := by
  constructor
  · intro h j
    obtain ⟨_, _, _, _, hp, hn⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime q hq hinj e
    rw [h] at hp hn
    norm_num at hp hn
    by_contra hj
    have aux (b : ι → ℤ) (hb : 0 < b j) : q j ∣ _root_.AbcTwoNinths.PolyCap.posPartNat q b := by
      unfold _root_.AbcTwoNinths.PolyCap.posPartNat
      exact (dvd_pow_self _ (by omega)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact (hq j).not_dvd_one (hn ▸ (show q j ∣ _root_.AbcTwoNinths.PolyCap.negPartNat q e from aux (-e) (by simpa using hlt)))
    · exact (hq j).not_dvd_one (hp ▸ aux e hgt)
  · intro h
    simp [_root_.AbcTwoNinths.PolyCap.prodMonomial, h]

open Real

/-- The logarithmic height of a monomial on distinct primes is the larger of its positive
and negative logarithmic contributions and is bounded by their sum. -/
theorem ratHeightProdMonomial {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) (e : ι → ℤ) :
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) =
      max (∑ j, max ((e j : ℝ) * log (q j : ℝ)) 0)
          (∑ j, max (-((e j : ℝ) * log (q j : ℝ))) 0) ∧
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) ≤ ∑ j, |(e j : ℝ)| * log (q j : ℝ) := by
  obtain ⟨hp, hn, _, _, hnum, hden⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime q hq hinj e
  have hlog (j : ι) : 0 ≤ log (q j : ℝ) :=
    log_nonneg (by exact_mod_cast (hq j).one_le)
  have hs (b : ι → ℤ) : log (_root_.AbcTwoNinths.PolyCap.posPartNat q b : ℝ) =
      ∑ j, max ((b j : ℝ) * log (q j : ℝ)) 0 := by
    simp only [_root_.AbcTwoNinths.PolyCap.posPartNat, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun j _ => pow_ne_zero _ (by exact_mod_cast (hq j).ne_zero))]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.log_pow]
    by_cases h : 0 ≤ b j
    · rw [max_eq_left (mul_nonneg (by exact_mod_cast h) (hlog j))]
      exact congrArg (fun x : ℝ => x * log (q j : ℝ)) (by exact_mod_cast Int.toNat_of_nonneg h)
    · rw [max_eq_right (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_ge h) (hlog j))]
      simp [Int.toNat_eq_zero.mpr (le_of_not_ge h)]
  have heq : _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q e) =
      max (log (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℝ)) (log (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℝ)) := by
    rw [_root_.AbcTwoNinths.Basic.rationalHeight, hnum, hden]
    rcases le_total (_root_.AbcTwoNinths.PolyCap.posPartNat q e) (_root_.AbcTwoNinths.PolyCap.negPartNat q e) with h | h
    · rw [max_eq_right h, max_eq_right (log_le_log (by exact_mod_cast hp) (by exact_mod_cast h))]
    · rw [max_eq_left h, max_eq_left (log_le_log (by exact_mod_cast hn) (by exact_mod_cast h))]
  rw [_root_.AbcTwoNinths.PolyCap.negPartNat, hs, hs] at heq
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul] at heq
  refine ⟨heq, ?_⟩
  rw [heq]
  refine max_le (Finset.sum_le_sum fun j _ => max_le ?_ ?_)
    (Finset.sum_le_sum fun j _ => max_le ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (le_abs_self _) (hlog j)
  · exact mul_nonneg (abs_nonneg _) (hlog j)
  · rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_le_abs _) (hlog j)
  · exact mul_nonneg (abs_nonneg _) (hlog j)

/--
A positive principal unit at a prime `p` that differs from one has logarithmic height strictly greater than `log p`.
-/
theorem logLtRatHeightOfGp {p : ℕ} {x : ℚ}
    (hp : p.Prime) (hx : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p x) (hne : x ≠ 1) :
    log (p : ℝ) < _root_.AbcTwoNinths.Basic.rationalHeight x := by
  have hf := (_root_.AbcTwoNinths.Basic.lengthFloor p x hp hx hne).1
  apply log_lt_log (by exact_mod_cast hp.pos)
  exact_mod_cast (show p < max x.num.natAbs x.den by omega)

end

end AbcTwoNinths.PolyCap
