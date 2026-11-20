/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Interpolation Minor Nonvanishing

The module selects a nonzero binomial interpolation minor from sites with sufficiently many distinct labels. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.elimination`
* `AbcTwoNinths.Terminal.existsNonzeroMinor`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section

open Polynomial
open scoped BigOperators

/--
The two translates of the interpolation relation have trivial joint kernel. This is used in Section 7 of the paper.
-/
theorem elimination {K : ℕ} (hK : 0 < K) {ι : Type*} [Fintype ι]
    {y : ι → ℚ} (hy : Function.Injective y) (hc : 2 * K - 1 ≤ Fintype.card ι)
    {r : ι → ℚ} (hr : ∀ i, r i ≠ 0) {g d : ℚ} (hg : g ≠ 1)
    {P Q : ℚ[X]} (hP : P.natDegree < K) (hQ : Q.natDegree < K)
    (hbase : ∀ i, P.eval (y i) + r i * Q.eval (y i) = 0)
    (hshift : ∀ i, P.eval (y i + d) + r i * g * Q.eval (y i + d) = 0) :
    P = 0 ∧ Q = 0 := by
  have root_zero (F : ℚ[X]) (hF : F.natDegree < Fintype.card ι)
      (h : ∀ i, F.eval (y i) = 0) : F = 0 :=
    F.eq_zero_of_natDegree_lt_card_of_eval_eq_zero hy h hF
  have hp_root (hq : Q = 0) : P = 0 := by
    apply root_zero P (by omega)
    intro i
    simpa [hq] using hbase i
  by_cases hp : P = 0
  · refine ⟨hp, root_zero Q (by omega) fun i ↦ ?_⟩
    have hi : r i * Q.eval (y i) = 0 := by simpa [hp] using hbase i
    exact (mul_eq_zero.mp hi).resolve_left (hr i)
  by_cases hq : Q = 0
  · exact ⟨hp_root hq, hq⟩
  let shift (F : ℚ[X]) := F.comp (X + C d)
  have hd (F : ℚ[X]) : (shift F).natDegree = F.natDegree := by
    simp [shift, natDegree_comp]
  have hl (F : ℚ[X]) : (shift F).leadingCoeff = F.leadingCoeff := by
    change (F.comp (X + C d)).leadingCoeff = _
    rw [leadingCoeff_comp (by simp)]
    simp [(monic_X_add_C d).leadingCoeff]
  have shift_ne_zero {F : ℚ[X]} (hF : F ≠ 0) : shift F ≠ 0 := by
    intro h
    exact hF (leadingCoeff_eq_zero.mp (by simpa [hl] using congrArg leadingCoeff h))
  have hPn := shift_ne_zero hp
  have hQn := shift_ne_zero hq
  let A := shift P * Q
  let E := C g * (P * shift Q)
  let n := P.natDegree + Q.natDegree
  have hA : A.natDegree = n := by
    simp [A, n, natDegree_mul hPn hq, hd]
  have hE' : (P * shift Q).natDegree = n := by simp [n, natDegree_mul hp hQn, hd]
  have hE : E.natDegree ≤ n := by
    simpa [E, hE'] using (natDegree_C_mul_le g (P * shift Q))
  have hAc : A.coeff n = P.leadingCoeff * Q.leadingCoeff := by
    rw [← hA, coeff_natDegree]
    simp [A, leadingCoeff_mul, hl]
  have hEc : E.coeff n = g * (P.leadingCoeff * Q.leadingCoeff) := by
    change (C g * (P * shift Q)).coeff n = _
    rw [coeff_C_mul, ← hE', coeff_natDegree, leadingCoeff_mul, hl]
  have hz : A - E = 0 := by
    apply root_zero
    · have h := (natDegree_sub_le A E).trans (max_le hA.le hE)
      dsimp [n] at h
      omega
    · intro i
      simp only [A, E, shift, eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X]
      linear_combination Q.eval (y i) * hshift i - g * Q.eval (y i + d) * hbase i
  have hnz : (1 - g) * (P.leadingCoeff * Q.leadingCoeff) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hg)) <|
      mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  apply (hnz ?_).elim
  have hn := congrArg (fun F : ℚ[X] ↦ F.coeff n) hz
  simp only [coeff_sub, coeff_zero, hAc, hEc] at hn
  linear_combination hn

/--
Polynomial giving the generalized binomial coefficient on integer labels. This is used in Section 7 of the paper.
-/
noncomputable def binomialPolynomial (k : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

private theorem factorialCastNeZero (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

/-- The generalized binomial coefficient polynomial of index `k` has degree `k`. -/
theorem binomialPolynomialDegree (k : ℕ) : (_root_.AbcTwoNinths.Terminal.binomialPolynomial k).natDegree = k := by
  rw [_root_.AbcTwoNinths.Terminal.binomialPolynomial, natDegree_C_mul (inv_ne_zero (factorialCastNeZero k)),
    descPochhammer_natDegree]

/-- At a rational argument `y`, the binomial polynomial evaluates to `Ring.choose y k`. -/
theorem binomialPolynomialEval (k : ℕ) (y : ℚ) :
    (_root_.AbcTwoNinths.Terminal.binomialPolynomial k).eval y = Ring.choose y k := by
  rw [_root_.AbcTwoNinths.Terminal.binomialPolynomial, eval_mul, eval_C, Ring.choose_eq_smul, smul_eq_mul,
    ← eval₂_smulOneHom_eq_smeval ℤ, ← eval_map, descPochhammer_map]

/-- The interpolation polynomial. This is used in Section 7 of the paper. -/
private noncomputable def interpolationPolynomial {K : ℕ} (c : Fin K → ℚ) : ℚ[X] :=
  ∑ k, C (c k) * _root_.AbcTwoNinths.Terminal.binomialPolynomial k

private theorem interpolationDegree {K : ℕ} (hK : 0 < K) (c : Fin K → ℚ) :
    (interpolationPolynomial c).natDegree < K := by
  apply lt_of_le_of_lt (b := K - 1)
  · apply natDegree_sum_le_of_forall_le
    intro k _
    exact ((natDegree_C_mul_le _ _).trans_eq (_root_.AbcTwoNinths.Terminal.binomialPolynomialDegree k)).trans (by omega)
  · omega

private theorem interpolationEqZero {K : ℕ} {c : Fin K → ℚ}
    (hc : interpolationPolynomial c = 0) : c = 0 := by
  classical
  by_contra h
  let active := Finset.univ.filter (fun k : Fin K ↦ c k ≠ 0)
  have hactive : active.Nonempty := by
    by_contra he
    apply h
    ext k
    by_contra hk
    exact he ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  let k := active.max' hactive
  have hk : c k ≠ 0 := (Finset.mem_filter.mp (active.max'_mem hactive)).2
  have hc' := congrArg (fun F : ℚ[X] ↦ F.coeff k) hc
  change ((∑ i, C (c i) * _root_.AbcTwoNinths.Terminal.binomialPolynomial i).coeff k) = (0 : ℚ[X]).coeff k at hc'
  rw [finsetSum_coeff, coeff_zero, Finset.sum_eq_single k] at hc'
  · have hcoeff : (_root_.AbcTwoNinths.Terminal.binomialPolynomial (k : ℕ)).coeff (k : ℕ) =
        (_root_.AbcTwoNinths.Terminal.binomialPolynomial (k : ℕ)).leadingCoeff := by
      rw [← coeff_natDegree, _root_.AbcTwoNinths.Terminal.binomialPolynomialDegree]
    rw [coeff_C_mul, hcoeff] at hc'
    exact (mul_ne_zero hk (leadingCoeff_ne_zero.mpr (mul_ne_zero
      (C_ne_zero.mpr (inv_ne_zero (factorialCastNeZero k)))
      (monic_descPochhammer ℚ k).ne_zero))) hc'
  · intro i _ hik
    rw [coeff_C_mul]
    by_cases hi : c i = 0
    · simp [hi]
    · have hle : i ≤ k := active.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hlt : (i : ℕ) < (k : ℕ) := show i < k from lt_of_le_of_ne hle hik
      simp [coeff_eq_zero_of_natDegree_lt ((_root_.AbcTwoNinths.Terminal.binomialPolynomialDegree i).trans_lt hlt)]
  · simp

/-- The site. This is used in Section 7 of the paper. -/
abbrev Site := ℤ × ℤ

/--
A multiplicative rational character on the additive lattice in source-plane coordinates. This is used in Section 7 of the paper.
-/
abbrev Character := Multiplicative _root_.AbcTwoNinths.Terminal.Site →* ℚˣ

/-- The value. This is used in Section 7 of the paper. -/
def value (γ : _root_.AbcTwoNinths.Terminal.Character) (s : _root_.AbcTwoNinths.Terminal.Site) : ℚ := (γ (Multiplicative.ofAdd s) : ℚ)

/--
Columns are ordered as the two size-K binomial blocks of manuscript equation (1). This is used in Section 7 of the paper.
-/
noncomputable def row (K : ℕ) (γ : _root_.AbcTwoNinths.Terminal.Character) (s : _root_.AbcTwoNinths.Terminal.Site) : Fin K ⊕ Fin K → ℚ :=
  Sum.elim (fun k ↦ Ring.choose (s.2 : ℚ) k)
    (fun k ↦ Ring.choose (s.2 : ℚ) k * _root_.AbcTwoNinths.Terminal.value γ s)

/-- Extract a square minor with pairwise distinct row sites from a matrix with trivial kernel. -/
private theorem extractMinor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℚ) (hM : ∀ c, M.mulVec c = 0 → c = 0) :
    ∃ rows : κ ↪ ι, (M.submatrix rows id).det ≠ 0 := by
  classical
  have hinj : Function.Injective M.mulVecLin :=
    LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot').mpr fun c hc ↦ hM c hc)
  have hdim : Module.finrank ℚ (Submodule.span ℚ (Set.range M.row)) = Fintype.card κ := by
    rw [← M.rank_eq_finrank_span_row, Matrix.rank, LinearMap.finrank_range_of_inj hinj,
      Module.finrank_pi]
  obtain ⟨f, hf, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range M.row)
  choose a ha using hf
  let e := Fintype.equivFinOfCardEq hdim.symm
  have he : LinearIndependent ℚ (f ∘ e) := hli.comp _ e.injective
  let rows : κ ↪ ι := ⟨a ∘ e, fun i j hij ↦ he.injective <|
    (ha (e i)).symm.trans ((congrArg M.row hij).trans (ha (e j)))⟩
  refine ⟨rows, ?_⟩
  have hli' : LinearIndependent ℚ (M.submatrix rows id).row := by
    convert he using 1
    exact funext fun i ↦ ha (e i)
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hli'.mulVec_surjective
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_right_inverse hB)

/--
The selected minor has exactly 2K distinct sites in the union of the original set
and its translate. The input labels need only be distinct on the original set. This is used in Section 7 of the paper.
-/
theorem existsNonzeroMinor {K : ℕ} (hK : 0 < K) (γ : _root_.AbcTwoNinths.Terminal.Character) (w : _root_.AbcTwoNinths.Terminal.Site)
    (hw : _root_.AbcTwoNinths.Terminal.value γ w ≠ 1) (sites : Finset _root_.AbcTwoNinths.Terminal.Site)
    (hcount : 2 * K - 1 ≤ sites.card)
    (hlabels : Function.Injective (fun s : sites ↦ (s.1 : _root_.AbcTwoNinths.Terminal.Site).2)) :
    ∃ selected : (Fin K ⊕ Fin K) ↪ _root_.AbcTwoNinths.Terminal.Site,
      (∀ i, selected i ∈ sites ∪ sites.image (fun s ↦ s + w)) ∧
      (Matrix.of (fun i ↦ _root_.AbcTwoNinths.Terminal.row K γ (selected i))).det ≠ 0 := by
  classical
  let both := sites ∪ sites.image (fun s ↦ s + w)
  let M : Matrix both (Fin K ⊕ Fin K) ℚ := Matrix.of fun s ↦ _root_.AbcTwoNinths.Terminal.row K γ s
  have hx (c : Fin K ⊕ Fin K → ℚ) (hc : M.mulVec c = 0) (s : both) :
      (interpolationPolynomial (c ∘ Sum.inl)).eval (s.1.2 : ℚ) +
      _root_.AbcTwoNinths.Terminal.value γ s * (interpolationPolynomial (c ∘ Sum.inr)).eval (s.1.2 : ℚ) = 0 := by
    have h := congrFun hc s
    simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_sum_type,
      _root_.AbcTwoNinths.Terminal.row, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] at h
    simp only [interpolationPolynomial, eval_finsetSum, eval_mul, eval_C,
      _root_.AbcTwoNinths.Terminal.binomialPolynomialEval, Function.comp_apply, Finset.mul_sum]
    convert h using 1
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  have hk (c : Fin K ⊕ Fin K → ℚ) (hc : M.mulVec c = 0) : c = 0 := by
    let P := interpolationPolynomial (c ∘ Sum.inl)
    let Q := interpolationPolynomial (c ∘ Sum.inr)
    have hcard : 2 * K - 1 ≤ Fintype.card sites := by simpa using hcount
    have hy : Function.Injective (fun s : sites ↦ ((s.1 : _root_.AbcTwoNinths.Terminal.Site).2 : ℚ)) := by
      intro s t hst
      apply hlabels
      exact Int.cast_injective (α := ℚ) hst
    have hv (s : _root_.AbcTwoNinths.Terminal.Site) : _root_.AbcTwoNinths.Terminal.value γ (s + w) = _root_.AbcTwoNinths.Terminal.value γ s * _root_.AbcTwoNinths.Terminal.value γ w := by
      change (↑(γ (Multiplicative.ofAdd s * Multiplicative.ofAdd w)) : ℚ) = _
      rw [map_mul, Units.val_mul]
      rfl
    have hb (s : sites) : P.eval (s.1.2 : ℚ) + _root_.AbcTwoNinths.Terminal.value γ s * Q.eval (s.1.2 : ℚ) = 0 :=
      hx c hc ⟨s, Finset.mem_union_left _ s.2⟩
    have hs (s : sites) :
        P.eval ((s.1.2 : ℚ) + (w.2 : ℚ)) +
          _root_.AbcTwoNinths.Terminal.value γ s * _root_.AbcTwoNinths.Terminal.value γ w * Q.eval ((s.1.2 : ℚ) + (w.2 : ℚ)) = 0 := by
      simpa only [Prod.snd_add, Int.cast_add, hv] using
        hx c hc ⟨s.1 + w, Finset.mem_union_right _ (Finset.mem_image_of_mem _ s.2)⟩
    obtain ⟨hp, hq⟩ := _root_.AbcTwoNinths.Terminal.elimination hK hy hcard (fun s ↦ (γ (Multiplicative.ofAdd s)).ne_zero)
      hw (interpolationDegree hK _) (interpolationDegree hK _) hb hs
    have hleft := interpolationEqZero hp
    have hright := interpolationEqZero hq
    funext i
    rcases i with i | i
    · exact congrFun hleft i
    · exact congrFun hright i
  obtain ⟨rows, hdet⟩ := extractMinor M hk
  exact ⟨⟨fun i ↦ (rows i).1, Subtype.val_injective.comp rows.injective⟩,
    fun i ↦ (rows i).2, hdet⟩

end

end AbcTwoNinths.Terminal
