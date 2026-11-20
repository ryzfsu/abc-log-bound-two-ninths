/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Binomial Minor Nonvanishing

The module uses a polynomial root count to find a nonzero interpolation minor on a rectangular grid.

## Main results
* `AbcTwoNinths.Basic.rectangleBinomialMinor`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

/-- The grid of coordinate pairs with inclusive upper bounds. -/
abbrev Rectangle (R S : ℕ) := Fin (R+1) × Fin (S+1)

/-- Strict bounds on both side lengths give a strict lower bound on the grid cardinality. -/
theorem rectangleCardGt {R S q : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : a < (R : ℝ)+1)
    (hS : b < (S : ℝ)+1) (hprod : (q : ℝ) ≤ a*b) :
    q < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S) := by
  simp only [_root_.AbcTwoNinths.Basic.Rectangle, Fintype.card_prod, Fintype.card_fin]
  exact_mod_cast hprod.trans_lt (mul_lt_mul'' hR hS ha (by positivity))

/-- The multiplicative node at a grid point is the product of the two rational base powers. -/
def nodeW {R S : ℕ} (a b : ℚ) (i : _root_.AbcTwoNinths.Basic.Rectangle R S) : ℚ :=
  a ^ i.1.val * b ^ i.2.val

/-- Nonzero multiplicatively independent bases give distinct multiplicative nodes. -/
theorem nodeWInjective {R S : ℕ} {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ m n : ℤ, a ^ m * b ^ n = 1 → m = 0 ∧ n = 0) :
    Function.Injective (_root_.AbcTwoNinths.Basic.nodeW (R := R) (S := S) a b) := by
  intro i j he
  have h : a ^ ((i.1.val : ℤ)-j.1.val) * b ^ ((i.2.val : ℤ)-j.2.val) = 1 := by
    rw [zpow_sub₀ ha, zpow_sub₀ hb]
    simp only [zpow_natCast]
    rw [← mul_div_mul_comm]
    change _root_.AbcTwoNinths.Basic.nodeW a b i / _root_.AbcTwoNinths.Basic.nodeW a b j = 1
    rw [← he]
    exact div_self (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
  obtain ⟨h₁,h₂⟩ := hind _ _ h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/--
An injective finite family of roots of a nonzero polynomial has cardinality at most its degree.
-/
theorem rootsCard {I : Type*} [Fintype I] {K : Type*} [Field K]
    (z : I → K) (hz : Function.Injective z) (f : Polynomial K)
    (hf : f ≠ 0) (he : ∀ i, f.eval (z i) = 0) :
    Fintype.card I ≤ f.natDegree := by
  classical
  have hs : Finset.univ.image z ⊆ f.roots.toFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr (he i))
  calc
    Fintype.card I = (Finset.univ.image z).card := by
      rw [Finset.card_image_of_injective _ hz, Finset.card_univ]
    _ ≤ f.roots.toFinset.card := Finset.card_le_card hs
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f

open Polynomial

/--
At the sum of the degree bounds, the coefficient of a product is the product of the corresponding coefficients.
-/
theorem coeffProdBudget {I K : Type*} [Field K] (S : Finset I)
    (f : I → K[X]) (d : I → ℕ) (hd : ∀ i ∈ S, (f i).natDegree ≤ d i) :
    (∏ i ∈ S, f i).coeff (∑ i ∈ S, d i) = ∏ i ∈ S, (f i).coeff (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have hs : ∀ j ∈ S, (f j).natDegree ≤ d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))
      ((Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hs)), ih hs]

/--
The determinant coefficient at the sum of the column degree bounds equals the determinant of the column coefficients.
-/
theorem detCoeffBudget {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (M : Matrix I I K[X]) (d : I → ℕ) (hd : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = (Matrix.of fun i j => (M i j).coeff (d j)).det := by
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro g _
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · simp [h, _root_.AbcTwoNinths.Basic.coeffProdBudget _ _ _ (fun j _ => hd (g j) j)]
  · simp [h, Units.neg_smul, _root_.AbcTwoNinths.Basic.coeffProdBudget _ _ _ (fun j _ => hd (g j) j)]

/-- The degree of a polynomial determinant is at most the sum of the column degree bounds. -/
theorem detDegreeBudget {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (M : Matrix I I K[X]) (d : I → ℕ) (hd : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro g _
  have h := Polynomial.coeff_eq_zero_of_natDegree_lt
    (((Polynomial.natDegree_prod_le Finset.univ (fun j => M (g j) j)).trans
      (Finset.sum_le_sum (fun j _ => hd (g j) j))).trans_lt hk)
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs | hs
  · simp [hs, h]
  · simp [hs, Units.neg_smul, h]

/--
A scaled Vandermonde coefficient matrix precludes nontrivial kernels at more nodes than the determinant degree bound.
-/
theorem detGridContradiction {L : ℕ} {I K : Type*} [Fintype I] [Field K]
    (z : I → K) (hz : Function.Injective z) (J : ℕ)
    (hcard : L * J < Fintype.card I)
    (w : Fin L → K) (hw : Function.Injective w)
    (M : Matrix (Fin L) (Fin L) K[X]) (d : Fin L → ℕ)
    (a : Fin L → K) (ha : ∀ j, a j ≠ 0) (hd : ∀ j, d j ≤ J)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d j)
    (hc : ∀ i j, (M i j).coeff (d j) = w i ^ (j : ℕ) * a j)
    (hker : ∀ i : I, ∃ y : Fin L → K, y ≠ 0 ∧
      (M.map (fun f : K[X] => f.eval (z i))).mulVec y = 0) : False := by
  have hV : (Matrix.vandermonde w).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hw
  have hC : (Matrix.of fun i j => (M i j).coeff (d j)).det ≠ 0 := by
    have he : (Matrix.of fun i j => (M i j).coeff (d j)) =
      Matrix.vandermonde w * Matrix.diagonal a := by
      ext i j
      simp [hc, Matrix.vandermonde]
    rw [he, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  have hM : M.det ≠ 0 := by
    intro he
    exact hC (by rw [← _root_.AbcTwoNinths.Basic.detCoeffBudget M d hdeg, he, Polynomial.coeff_zero])
  have hzero (i : I) : M.det.eval (z i) = 0 := by
    obtain ⟨y, hy, h⟩ := hker i
    have hm : (M.map (fun f : K[X] => f.eval (z i))).det = 0 :=
      by_contra fun hh => hy (Matrix.eq_zero_of_mulVec_eq_zero hh h)
    change Polynomial.evalRingHom (z i) M.det = 0
    rw [RingHom.map_det]
    exact hm
  have hsum : ∑ j, d j ≤ L * J := by
    simpa [mul_comm] using (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd j))
  exact (not_le_of_gt hcard) ((_root_.AbcTwoNinths.Basic.rootsCard z hz M.det hM hzero).trans
    ((_root_.AbcTwoNinths.Basic.detDegreeBudget M d hdeg).trans hsum))

/--
A family of bounded-degree polynomials with vanishing weighted sums on the specified grid is identically zero.
-/
theorem gridPolynomialsZero {L : ℕ} {I K : Type*} [Fintype I] [Field K]
    (J : ℕ) (z₁ w₁ : Fin L → K) (z₂ w₂ : I → K)
    (hw : Function.Injective w₁) (hz : Function.Injective z₂)
    (hw₂ : ∀ i, w₂ i ≠ 0) (hn : L * J < Fintype.card I)
    (Q : Fin L → K[X]) (hQ : ∀ t, (Q t).natDegree ≤ J)
    (he : ∀ i j, ∑ t : Fin L, (Q t).eval (z₁ i + z₂ j) * (w₁ i * w₂ j) ^ (t : ℕ) = 0) :
    ∀ t, Q t = 0 := by
  classical
  intro t
  by_contra ht
  let P (j : Fin L) := if Q j = 0 then 1 else Q j
  have hP (j : Fin L) : P j ≠ 0 := by by_cases hj : Q j = 0 <;> simp [P,hj]
  have hPJ (j : Fin L) : (P j).natDegree ≤ J := by
    by_cases hj : Q j = 0 <;> simp [P, hj, hQ]
  let T (i : Fin L) : K[X] := X + C (z₁ i)
  have hT (i : Fin L) : (T i).natDegree = 1 := by simp [T]
  have hTc (i : Fin L) : (T i).leadingCoeff = 1 := by simp [T, leadingCoeff_X_add_C]
  let M : Matrix (Fin L) (Fin L) K[X] := Matrix.of fun i j =>
    C (w₁ i ^ (j : ℕ)) * (P j).comp (T i)
  apply _root_.AbcTwoNinths.Basic.detGridContradiction z₂ hz J hn w₁ hw M (fun j => (P j).natDegree)
    (fun j => (P j).leadingCoeff) (fun j => leadingCoeff_ne_zero.mpr (hP j)) hPJ
  · intro i j
    change (C (w₁ i ^ (j : ℕ)) * (P j).comp (T i)).natDegree ≤ _
    exact natDegree_mul_le.trans (by rw [natDegree_C, natDegree_comp, hT, mul_one, zero_add])
  · intro i j
    change (C (w₁ i ^ (j : ℕ)) * (P j).comp (T i)).coeff (P j).natDegree = _
    have hN : ((P j).comp (T i)).natDegree = (P j).natDegree := by
      rw [natDegree_comp, hT, mul_one]
    have hN' : (T i).natDegree ≠ 0 := by rw [hT]; decide
    have hLead := leadingCoeff_comp (p := P j) hN'
    rw [coeff_C_mul, ← hN, coeff_natDegree, hLead, hTc, one_pow, mul_one]
  · intro j
    let y (k : Fin L) : K := if Q k = 0 then 0 else w₂ j ^ (k : ℕ)
    refine ⟨y, ?_, ?_⟩
    · intro h
      have hy := congrFun h t
      exact pow_ne_zero _ (hw₂ j) (by simpa [y, ht] using hy)
    · funext i
      change (∑ k : Fin L, ((M i k).eval (z₂ j)) * y k) = 0
      rw [← he i j]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : Q k = 0
      · simp [y,hk]
      · simp [M,P,T,y,hk,eval_comp,mul_pow,add_comm (z₂ j) (z₁ i)]
        ring

/-- A matrix with linearly independent rows has a nonzero minor using every row. -/
theorem minorOfIndependentRows {I D K : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Field K] (M : Matrix I D K) (h : LinearIndependent K M.row) :
    ∃ f : I ↪ D, (M.submatrix id f).det ≠ 0 := by
  classical
  have hs : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    exact h.mulVec_surjective
  obtain ⟨g, hg, hgs, hi⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.col)
  have hr : Module.finrank K (Submodule.span K (Set.range M.col)) = Fintype.card I := by
    rw [hs, finrank_top, Module.finrank_pi]
  let e := (Fintype.equivFin I).trans (finCongr hr.symm)
  choose f hf using fun i : I => hg (e i)
  have hx : Function.Injective f := by
    intro i j he
    apply e.injective
    apply hi.injective
    rw [← hf i, ← hf j, he]
  refine ⟨⟨f,hx⟩, ?_⟩
  have hl : LinearIndependent K (M.submatrix id f).col := by
    convert hi.comp e e.injective using 1
    funext i
    exact hf i
  have hspan : Submodule.span K (Set.range (M.submatrix id f).col) = ⊤ := by
    have heq : (M.submatrix id f).col = g ∘ e := funext hf
    rw [heq, e.surjective.range_comp, hgs, hs]
  have hdet := ((Pi.basisFun K I).is_basis_iff_det).mp ⟨hl,hspan⟩
  have heq : (Pi.basisFun K I).toMatrix (M.submatrix id f).col = M.submatrix id f := by
    apply Matrix.ext
    intro i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  change (M.submatrix id f).det ≠ 0
  rw [Module.Basis.det_apply, heq] at hdet
  exact hdet.ne_zero

/--
The rational binomial polynomial is the falling factorial divided by the factorial of its degree.
-/
noncomputable def binPoly (k : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

/--
The binomial polynomial evaluates at each natural argument to the corresponding binomial coefficient.
-/
theorem evalBinPoly (n k : ℕ) : (_root_.AbcTwoNinths.Basic.binPoly k).eval (n : ℚ) = n.choose k := by
  have h : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  simp [_root_.AbcTwoNinths.Basic.binPoly, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, h]

/-- Compatible additive and multiplicative grid nodes yield a nonzero full-row binomial minor. -/
theorem gridBinomialMinor {L J : ℕ} {I D : Type*} [Fintype I] [Fintype D]
    (Z : D → ℕ) (W : D → ℚ) (z₁ : Fin L → ℕ) (w₁ : Fin L → ℚ)
    (z₂ : I → ℕ) (w₂ : I → ℚ)
    (hw : Function.Injective w₁) (hz : Function.Injective z₂)
    (hw₂ : ∀ i, w₂ i ≠ 0) (hn : L * J < Fintype.card I)
    (join : Fin L → I → D)
    (hZ : ∀ i j, Z (join i j) = z₁ i + z₂ j)
    (hW : ∀ i j, W (join i j) = w₁ i * w₂ j) :
    let M : Matrix (Fin (J+1) × Fin L) D ℚ :=
      Matrix.of fun k d => (Nat.choose (Z d) k.1.val : ℚ) * W d ^ k.2.val
    ∃ f : (Fin (J+1) × Fin L) ↪ D, (M.submatrix id f).det ≠ 0 := by
  classical
  dsimp only
  apply _root_.AbcTwoNinths.Basic.minorOfIndependentRows
  rw [Fintype.linearIndependent_iff]
  intro v hv k
  let Q (t : Fin L) := ∑ j : Fin (J+1), C (v (j,t)) * _root_.AbcTwoNinths.Basic.binPoly j.val
  have hdeg (j : Fin (J+1)) (t : Fin L) :
      (C (v (j,t)) * _root_.AbcTwoNinths.Basic.binPoly j.val).natDegree ≤ j.val := by
    unfold _root_.AbcTwoNinths.Basic.binPoly
    rw [← mul_assoc, ← C_mul]
    exact natDegree_mul_le.trans (by rw [natDegree_C, descPochhammer_natDegree, zero_add])
  have hQ (t : Fin L) : (Q t).natDegree ≤ J :=
    natDegree_sum_le_of_forall_le _ _ (fun j _ => (hdeg j t).trans (Nat.le_of_lt_succ j.isLt))
  have he : ∀ i j, ∑ t : Fin L, (Q t).eval ((z₁ i : ℚ) + z₂ j) *
      (w₁ i * w₂ j) ^ (t : ℕ) = 0 := by
    intro i j
    have h := congrFun hv (join i j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply, Matrix.of_apply,
      hZ, hW, Pi.zero_apply] at h
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h
    push_cast at h
    simp only [Q, eval_finsetSum, eval_mul, eval_C, ← Nat.cast_add, _root_.AbcTwoNinths.Basic.evalBinPoly, Finset.sum_mul]
    simpa only [mul_assoc] using h
  have hzero := _root_.AbcTwoNinths.Basic.gridPolynomialsZero J (fun i => (z₁ i : ℚ)) w₁
    (fun j => (z₂ j : ℚ)) w₂ hw (fun i j h => hz (by
      change (z₂ i : ℚ) = (z₂ j : ℚ) at h
      exact_mod_cast h)) hw₂ hn Q hQ he
  suffices h : ∀ n (j : Fin (J+1)) (t : Fin L), J - j.val = n → v (j,t) = 0 by
    exact h (J-k.1.val) k.1 k.2 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- Use downward induction on the distance from the maximal degree.
      intro j t hj
      have hh := congrArg (fun f : ℚ[X] => f.coeff j.val) (hzero t)
      simp only [Q, finsetSum_coeff, coeff_zero] at hh
      rw [Finset.sum_eq_single j] at hh
      · rw [coeff_C_mul] at hh
        have hnz : (_root_.AbcTwoNinths.Basic.binPoly j.val).coeff j.val ≠ 0 := by
          unfold _root_.AbcTwoNinths.Basic.binPoly
          have hh' : (descPochhammer ℚ j.val).coeff j.val = 1 := by
            have hM := monic_descPochhammer ℚ j.val
            simpa only [descPochhammer_natDegree] using hM.coeff_natDegree
          rw [coeff_C_mul, hh', mul_one]
          exact inv_ne_zero (by exact_mod_cast j.val.factorial_ne_zero)
        exact (mul_eq_zero.mp hh).resolve_right hnz
      · intro l _ hlj
        rcases lt_trichotomy l.val j.val with hlt | hEq | hgt
        · exact coeff_eq_zero_of_natDegree_lt ((hdeg l t).trans_lt hlt)
        · exact (hlj (Fin.ext hEq)).elim
        · have hl := l.isLt
          have hj' := j.isLt
          have hz := ih (J - l.val) (by omega) l t rfl
          simp [hz]
      · simp

/--
The additive node has value equal to the first coordinate times the second weight plus the second coordinate times the first weight.
-/
def nodeZ {R S : ℕ} (c₁ c₂ : ℕ) (i : _root_.AbcTwoNinths.Basic.Rectangle R S) : ℕ :=
  i.1.val * c₂ + i.2.val * c₁

/-- Coordinatewise addition sends two rectangle nodes into the rectangle with summed bounds. -/
def addNode {R S R' S' : ℕ} (i : _root_.AbcTwoNinths.Basic.Rectangle R S) (j : _root_.AbcTwoNinths.Basic.Rectangle R' S') :
    _root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S') :=
  (⟨i.1.val+j.1.val, by have := i.1.isLt; have := j.1.isLt; omega⟩,
   ⟨i.2.val+j.2.val, by have := i.2.isLt; have := j.2.isLt; omega⟩)

/--
Independent multiplicative bases and an injective additive coordinate on the second rectangle yield a nonzero full-row binomial minor.
-/
theorem rectangleBinomialMinor {R S R' S' L J c₁ c₂ : ℕ} (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ m n : ℤ, a ^ m * b ^ n = 1 → m = 0 ∧ n = 0)
    (h₁ : L ≤ Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R S))
    (h₂ : L*J < Fintype.card (_root_.AbcTwoNinths.Basic.Rectangle R' S'))
    (hz : Function.Injective (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') c₁ c₂)) :
    let M : Matrix (Fin (J+1) × Fin L) (_root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S')) ℚ :=
      Matrix.of fun k d => (Nat.choose (_root_.AbcTwoNinths.Basic.nodeZ c₁ c₂ d) k.1.val : ℚ) * _root_.AbcTwoNinths.Basic.nodeW a b d ^ k.2.val
    ∃ f : (Fin (J+1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S'), (M.submatrix id f).det ≠ 0 := by
  classical
  let e := (Fin.castLEEmb h₁).trans (Fintype.equivFin (_root_.AbcTwoNinths.Basic.Rectangle R S)).symm.toEmbedding
  apply _root_.AbcTwoNinths.Basic.gridBinomialMinor (_root_.AbcTwoNinths.Basic.nodeZ c₁ c₂) (_root_.AbcTwoNinths.Basic.nodeW a b) (_root_.AbcTwoNinths.Basic.nodeZ c₁ c₂ ∘ e)
    (_root_.AbcTwoNinths.Basic.nodeW a b ∘ e) (_root_.AbcTwoNinths.Basic.nodeZ c₁ c₂) (_root_.AbcTwoNinths.Basic.nodeW a b)
    ((_root_.AbcTwoNinths.Basic.nodeWInjective ha hb hind).comp e.injective) hz
    (fun i => mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)) h₂
    (fun i j => _root_.AbcTwoNinths.Basic.addNode (e i) j)
  · intro i j
    simp [_root_.AbcTwoNinths.Basic.nodeZ, _root_.AbcTwoNinths.Basic.addNode, add_mul]
    omega
  · intro i j
    simp [_root_.AbcTwoNinths.Basic.nodeW, _root_.AbcTwoNinths.Basic.addNode, pow_add]
    ring

end

end AbcTwoNinths.Basic
