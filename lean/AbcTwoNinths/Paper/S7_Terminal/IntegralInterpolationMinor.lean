/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Integral Interpolation Minor

The module expands an integral interpolation minor and bounds its valuation through individual feature terms. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.integralMinorDvd`
* `AbcTwoNinths.Terminal.floorTwoNinths`
* `AbcTwoNinths.Terminal.integralMinorValuation`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

open scoped BigOperators

section

variable {R : Type*} [CommRing R]

/--
The minimum of (K - d)m + r d² over 0 ≤ d ≤ K is the guaranteed divisibility exponent. This is used in Section 7 of the paper.
-/
def floor (K m r : ℕ) : ℕ :=
  (Finset.range (K + 1)).inf' (by simp) fun j => (K - j) * m + r * j ^ 2

private theorem featureDetExpansion {I F : Type*} [Fintype I] [DecidableEq I] [Fintype F]
    (U : Matrix I F R) (C : Matrix F I R) :
    (U * C).det = ∑ f : I → F, (∏ i, C (f i) i) * (U.submatrix id f).det := by
  classical
  calc
    _ = ∑ f : I → F, ∑ σ : Equiv.Perm I,
        (Equiv.Perm.sign σ : R) * ∏ i, U (σ i) (f i) * C (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      ext f
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq]
      ring

private theorem featurePowDvdDet {I F : Type*} [Fintype I] [DecidableEq I] [Fintype F]
    (U : Matrix I F R) (C : Matrix F I R) (p : R) (e : F → I → ℕ) (E : ℕ)
    (hc : ∀ i j, p ^ e j i ∣ C j i)
    (budget : ∀ f : I → F, Function.Injective f →
      (∀ i, C (f i) i ≠ 0) → E ≤ ∑ i, e (f i) i) :
    p ^ E ∣ (U * C).det := by
  classical
  rw [featureDetExpansion]
  apply Finset.dvd_sum
  intro f _
  by_cases hi : Function.Injective f
  · by_cases hn : ∀ i, C (f i) i ≠ 0
    · have hprod : (∏ i, p ^ e (f i) i) ∣ ∏ i, C (f i) i :=
        Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hc i (f i)
      rw [Finset.prod_pow_eq_pow_sum] at hprod
      exact dvd_mul_of_dvd_left ((pow_dvd_pow p (budget f hi hn)).trans hprod) _
    · push Not at hn
      obtain ⟨i, hzero⟩ := hn
      have hv : (∏ j, C (f j) j) = 0 :=
        Finset.prod_eq_zero (f := fun j => C (f j) j) (Finset.mem_univ i) hzero
      rw [hv, zero_mul]
      exact dvd_zero _
  · unfold Function.Injective at hi
    push Not at hi
    obtain ⟨i,j,hij,hne⟩ := hi
    have hz : (U.submatrix id f).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix, hij])
    simp [hz]

private theorem offsetLeMono {j K : ℕ} (f : Fin j → ℕ) (hf : StrictMono f)
    (hK : ∀ i, K ≤ f i) (i : Fin j) : K + (i : ℕ) ≤ f i := by
  suffices h : ∀ t (ht : t < j), K + t ≤ f ⟨t, ht⟩ from h i i.isLt
  intro t
  induction t with
  | zero => intro ht; simpa using hK ⟨0, ht⟩
  | succ t ih =>
    intro ht
    have ht' : t < j := by omega
    have hh := hf (show (⟨t, ht'⟩ : Fin j) < ⟨t + 1, ht⟩ by exact Nat.lt_succ_self _)
    have := ih ht'
    omega

private theorem sumOffset {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℕ) (hf : Set.InjOn f S) {K : ℕ} (hK : ∀ i ∈ S, K ≤ f i) :
    ∑ i : Fin S.card, (K + (i : ℕ)) ≤ ∑ i ∈ S, f i := by
  classical
  let T := S.image f
  have hcard : T.card = S.card := Finset.card_image_of_injOn hf
  let e := T.orderEmbOfFin hcard
  have he (i : Fin S.card) : K ≤ e i := by
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (T.orderEmbOfFin_mem hcard i)
    exact he ▸ hK x hx
  calc
    _ ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => offsetLeMono e e.strictMono he i
    _ = ∑ i ∈ T, i := by rw [← T.map_orderEmbOfFin_univ hcard, Finset.sum_map]; rfl
    _ = _ := Finset.sum_image hf

private theorem analyticBudget {K : ℕ} (S : Finset (Fin K)) (n : Fin K → ℕ)
    (hinj : Set.InjOn n S) (hn : ∀ i ∈ S, K ≤ n i) :
    S.card ^ 2 ≤ ∑ i ∈ S, (n i - (i : ℕ)) := by
  have hc : S.card ≤ K := by simpa using Finset.card_le_univ S
  have h₁ := sumOffset S n hinj hn
  have h₂ := sumOffset S (fun i => K - 1 - (i : ℕ)) (K := 0)
    (fun i _ j _ h => Fin.ext (by
      change K - 1 - (i : ℕ) = K - 1 - (j : ℕ) at h
      have hi := i.isLt; have hj := j.isLt; omega))
    (fun _ _ => Nat.zero_le _)
  have hsum : (∑ i ∈ S, (n i - (i : ℕ))) + (∑ _i ∈ S, K) =
      (∑ i ∈ S, n i) + (∑ i ∈ S, (K - 1 - (i : ℕ))) + S.card := by
    have h : ∀ i ∈ S, (n i - (i : ℕ)) + K =
        n i + (K - 1 - (i : ℕ)) + 1 := by
      intro i hi
      have := hn i hi
      have := i.isLt
      omega
    simpa only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl), mul_one] using
      Finset.sum_congr rfl h
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, zero_add] at h₁ h₂ hsum
  have H : (∑ i : Fin S.card, (i : ℕ)) * 2 = S.card * (S.card - 1) := by
    have H := Finset.sum_range_id_mul_two S.card
    rw [← Fin.sum_univ_eq_sum_range] at H
    exact H
  rcases hj : S.card with _ | j
  · simp
  · rw [hj, Nat.add_sub_cancel] at H
    rw [hj] at hsum h₁ h₂
    nlinarith

private theorem analyticExpansion (a : R) (y k L : ℕ) (hY : y < L) :
    (y.choose k : R) * a ^ y =
      ∑ n ∈ Finset.range L, (y.choose n : R) *
        (a ^ k * (n.choose k : R) * (a - 1) ^ (n - k)) := by
  by_cases h : k ≤ y
  · have hlen : y + 1 - k = y - k + 1 := by omega
    rw [← Finset.sum_subset (show Finset.Ico k (y + 1) ⊆ Finset.range L by
        intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at *; omega),
      Finset.sum_Ico_eq_sum_range, hlen]
    · have hpow : a ^ (y - k) = ∑ b ∈ Finset.range (y - k + 1),
          (a - 1) ^ b * ((y - k).choose b : R) := by
        conv_lhs => rw [show a = (a - 1) + 1 by ring, add_pow]
        simp
      calc
        (y.choose k : R) * a ^ y =
            (y.choose k : R) * (a ^ k * a ^ (y - k)) := by
          rw [← pow_add, Nat.add_sub_of_le h]
        _ = _ := by
          rw [hpow, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          have hb : (k + b - k) = b := by omega
          have hc := congrArg (fun n : ℕ => (n : R))
            (Nat.choose_mul (n := y) (k := k + b) (s := k) (by omega))
          simp only [Nat.cast_mul, hb] at hc
          rw [hb]
          linear_combination (a - 1) ^ b * a ^ k * hc.symm
    · intro n hn hout
      simp only [Finset.mem_Ico, Finset.mem_range] at hn hout
      by_cases hny : y < n
      · simp [Nat.choose_eq_zero_of_lt hny]
      · have hnk : n < k := by omega
        simp [Nat.choose_eq_zero_of_lt hnk]
  · rw [Nat.choose_eq_zero_of_lt (by omega : y < k), Nat.cast_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro n _
    by_cases hny : y < n
    · simp [Nat.choose_eq_zero_of_lt hny]
    · simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

/--
The disjoint union of two copies of Fin K indexes the rows and columns of the interpolation minor. This is used in Section 7 of the paper.
-/
abbrev Slots (K : ℕ) := Fin K ⊕ Fin K

/-- The nat minor. This is used in Section 7 of the paper. -/
private def natMinor {K : ℕ} (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℕ) (z a : R) :
    Matrix (_root_.AbcTwoNinths.Terminal.Slots K) (_root_.AbcTwoNinths.Terminal.Slots K) R :=
  fun i j => match j with
  | .inl k => y i |>.choose k |>.cast
  | .inr k => (Nat.choose (y i) k : R) * z ^ x i * a ^ y i

/-- The weight. This is used in Section 7 of the paper. -/
private def weight {K L : ℕ} (m r : ℕ) : (Fin L ⊕ Fin K) → _root_.AbcTwoNinths.Terminal.Slots K → ℕ
  | .inl n, .inr k => r * (n.val - k.val)
  | .inr _, .inr _ => m
  | _, .inl _ => 0

private theorem natMinorDvd {K : ℕ} (m r : ℕ) (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℕ) (p z a : R)
    (hz : p ^ m ∣ z - 1) (ha : p ^ r ∣ a - 1) :
    p ^ _root_.AbcTwoNinths.Terminal.floor K m r ∣ (natMinor x y z a).det := by
  classical
  let L := K + 1 + ∑ i, y i
  have hK : K ≤ L := by dsimp [L]; omega
  have hY (i : _root_.AbcTwoNinths.Terminal.Slots K) : y i < L := by
    have := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [L]
    omega
  let fix (k : Fin K) : Fin L := ⟨k, k.isLt.trans_le hK⟩
  have hd (i : _root_.AbcTwoNinths.Terminal.Slots K) : p ^ m ∣ (z ^ x i - 1) * a ^ y i := by
    exact dvd_mul_of_dvd_left (hz.trans (sub_one_dvd_pow_sub_one z (x i))) _
  choose d hd using hd
  let U : Matrix (_root_.AbcTwoNinths.Terminal.Slots K) (Fin L ⊕ Fin K) R := fun i j => match j with
    | .inl n => (Nat.choose (y i) n : R)
    | .inr k => (Nat.choose (y i) k : R) * d i
  let C : Matrix (Fin L ⊕ Fin K) (_root_.AbcTwoNinths.Terminal.Slots K) R := fun j k => match j, k with
    | .inl n, .inl t => if n = fix t then 1 else 0
    | .inl n, .inr t => a ^ t.val * (n.val.choose t : R) * (a - 1) ^ (n.val - t.val)
    | .inr _, .inl _ => 0
    | .inr u, .inr t => if u = t then p ^ m else 0
  have hUC : U * C = natMinor x y z a := by
    ext i j
    cases j with
    | inl k =>
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp [U, C, natMinor, fix, mul_ite, Finset.sum_ite_eq']
    | inr k =>
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [U, C, natMinor]
      have hx := analyticExpansion a (y i) k.val L (hY i)
      rw [← Fin.sum_univ_eq_sum_range] at hx
      rw [← hx]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      linear_combination -(Nat.choose (y i) k : R) * (hd i)
  rw [← hUC]
  apply featurePowDvdDet U C p (weight m r)
  · intro k j
    rcases j with n | b <;> rcases k with k | k
    · simp [weight]
    · have hh := pow_dvd_pow_of_dvd ha (n.val - k.val)
      rw [← pow_mul] at hh
      exact dvd_mul_of_dvd_right hh _
    · simp [weight]
    · by_cases h : b = k <;> simp [C, weight, h]
  · intro f hf hn
    have hfix (k : Fin K) : f (.inl k) = .inl (fix k) := by
      specialize hn (.inl k)
      cases h : f (.inl k) with
      | inl j =>
        have he : j = fix k := by by_contra hne; exact hn (by simp [h, C, hne])
        simp [he]
      | inr j => simp [h, C] at hn
    let S := Finset.univ.filter fun k : Fin K => (f (.inr k)).isLeft
    let n (k : Fin K) := (f (.inr k)).elim Fin.val (fun _ => 0)
    have hselected (k : Fin K) (hk : k ∈ S) : ∃ j : Fin L, f (.inr k) = .inl j := by
      cases h : f (.inr k) with
      | inl j => exact ⟨j, rfl⟩
      | inr j => simp [S, h] at hk
    have hlabels (k : Fin K) (hk : k ∈ S) : K ≤ n k := by
      obtain ⟨j, hj⟩ := hselected k hk
      simp only [n, hj, Sum.elim_inl]
      by_contra! h
      let b : Fin K := ⟨j.val, h⟩
      have he : j = fix b := Fin.ext rfl
      have hbad := hf ((hfix b).trans (hj.trans (congrArg Sum.inl he)).symm)
      contradiction
    have hinj : Set.InjOn n S := by
      intro i hi j hj h
      obtain ⟨b, hb⟩ := hselected i hi
      obtain ⟨c, hc⟩ := hselected j hj
      have he : b = c := Fin.ext (by simpa [n, hb, hc] using h)
      exact Sum.inr.inj (hf (hb.trans (hc.trans (congrArg Sum.inl he.symm)).symm))
    have hsum : ∑ i, weight m r (f i) i =
        r * (∑ k ∈ S, (n k - k.val)) + (K - S.card) * m := by
      rw [Fintype.sum_sum_type]
      simp only [show (∀ (j : Fin L ⊕ Fin K) (k : Fin K),
          weight m r j (.inl k) = 0) by intro j k; cases j <;> rfl, Finset.sum_const_zero,
          zero_add]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Fin K => (f (.inr k)).isLeft)]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨j, hj⟩ := hselected k hk
        simp [hj, weight, n]
      · have hcard : (Finset.univ.filter fun k : Fin K => ¬ (f (.inr k)).isLeft).card =
            K - S.card := by
          have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin K))
            (fun k => (f (.inr k)).isLeft) (fun _ => (1 : ℕ))
          simp only [Finset.sum_const_nat (fun _ _ => rfl), mul_one, Finset.card_univ,
            Fintype.card_fin] at h
          change S.card + _ = K at h
          omega
        rw [← hcard]
        apply Finset.sum_const_nat
        intro k hk
        cases h : f (.inr k) with
        | inl j => simp [h] at hk
        | inr j => simp [weight]
    have hcard : S.card ≤ K := by simpa using Finset.card_le_univ S
    rw [hsum]
    refine (Finset.inf'_le (fun j => (K - j) * m + r * j ^ 2)
      (Finset.mem_range.mpr (by omega : S.card < K + 1))).trans ?_
    have H := Nat.mul_le_mul_left r (analyticBudget S n hinj hlabels)
    omega

/--
The interpolation matrix on signed integer sites pairs binomial columns with their unit-character multiples. This is used in Section 7 of the paper.
-/
def integralMinor {K : ℕ} (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℤ) (z a : Rˣ) :
    Matrix (_root_.AbcTwoNinths.Terminal.Slots K) (_root_.AbcTwoNinths.Terminal.Slots K) R :=
  fun i j => match j with
  | .inl k => (Ring.choose (y i) k : ℤ)
  | .inr k => ((Ring.choose (y i) k : ℤ) : R) * ↑(z ^ x i * a ^ y i)

private theorem signedChooseShift {K : ℕ} (u d : ℕ) (k : Fin K) :
    ((Ring.choose ((u : ℤ) - d) k.val : ℤ) : R) =
      ∑ j : Fin K, (u.choose j : R) *
        (if j ≤ k then ((Ring.choose (-(d : ℤ)) (k.val - j.val) : ℤ) : R) else 0) := by
  rw [sub_eq_add_neg, Ring.add_choose_eq _ (Commute.all _ _), Int.cast_sum]
  simp only [Int.cast_mul, Ring.choose_natCast, Int.cast_natCast]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j b => (u.choose j : R) * ((Ring.choose (-(d : ℤ)) b : ℤ) : R))]
  let G (j : ℕ) : R := (u.choose j : R) *
    (if j ≤ k.val then ((Ring.choose (-(d : ℤ)) (k.val - j) : ℤ) : R) else 0)
  change _ = ∑ j : Fin K, G j
  rw [Fin.sum_univ_eq_sum_range G]
  rw [← Finset.sum_subset (show Finset.range (k.val + 1) ⊆ Finset.range K from
    Finset.range_mono k.isLt)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [G, show j ≤ k.val by omega]
  · intro j hj hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [G, show ¬j ≤ k.val by omega]

/--
The two unit congruences imply divisibility of the integral determinant by the local parameter raised to the valuation floor. This is used in Section 7 of the paper.
-/
theorem integralMinorDvd {K : ℕ} (m r : ℕ) (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℤ) (p : R) (z a : Rˣ)
    (hz : p ^ m ∣ (z : R) - 1) (ha : p ^ r ∣ (a : R) - 1) :
    p ^ _root_.AbcTwoNinths.Terminal.floor K m r ∣ (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det := by
  classical
  let dx := ∑ i, (x i).natAbs
  let dy := ∑ i, (y i).natAbs
  let X i := (x i + dx).toNat
  let Y i := (y i + dy).toNat
  have shift (f : _root_.AbcTwoNinths.Terminal.Slots K → ℤ) (i : _root_.AbcTwoNinths.Terminal.Slots K) :
      (((f i + (∑ j, (f j).natAbs : ℕ)).toNat : ℕ) : ℤ) -
        (∑ j, (f j).natAbs : ℕ) = f i := by
    have h := Finset.single_le_sum (f := fun j => (f j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hb := neg_le_abs (f i)
    rw [Int.abs_eq_natAbs] at hb
    omega
  have hx (i : _root_.AbcTwoNinths.Terminal.Slots K) : (X i : ℤ) - dx = x i := shift x i
  have hy (i : _root_.AbcTwoNinths.Terminal.Slots K) : (Y i : ℤ) - dy = y i := shift y i
  let T (j k : Fin K) : R :=
    if j ≤ k then ((Ring.choose (-(dy : ℤ)) (k.val - j.val) : ℤ) : R) else 0
  let s : R := ↑(z ^ (-(dx : ℤ)) * a ^ (-(dy : ℤ)))
  let C : Matrix (_root_.AbcTwoNinths.Terminal.Slots K) (_root_.AbcTwoNinths.Terminal.Slots K) R := fun j k => match j, k with
    | .inl j, .inl k => T j k
    | .inr j, .inr k => s * T j k
    | _, _ => 0
  have hchar (i : _root_.AbcTwoNinths.Terminal.Slots K) :
      (↑(z ^ x i * a ^ y i) : R) = (z : R) ^ X i * (a : R) ^ Y i * s := by
    rw [← hx i, ← hy i, sub_eq_add_neg, sub_eq_add_neg, zpow_add, zpow_add]
    simp [s]
    ring
  have he (i : _root_.AbcTwoNinths.Terminal.Slots K) (k : Fin K) :
      ((Ring.choose (y i) k.val : ℤ) : R) = ∑ j : Fin K, ((Y i).choose j : R) * T j k := by
    rw [← hy i]
    exact signedChooseShift (Y i) dy k
  have hM : _root_.AbcTwoNinths.Terminal.integralMinor x y z a = natMinor X Y (z : R) (a : R) * C := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    cases j with
    | inl k => simpa [_root_.AbcTwoNinths.Terminal.integralMinor, natMinor, C] using he i k
    | inr k =>
      simp only [_root_.AbcTwoNinths.Terminal.integralMinor, natMinor, C, mul_zero, Finset.sum_const_zero, zero_add, hchar, he]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hM, Matrix.det_mul]
  exact dvd_mul_of_dvd_left (natMinorDvd m r X Y _ _ _ hz ha) _

/--
If 4rK ≤ 3m, then nine times the valuation floor is at least 8rK². This is used in Section 7 of the paper.
-/
theorem floorTwoNinths {K m r : ℕ} (hm : 4 * r * K ≤ 3 * m) :
    8 * r * K ^ 2 ≤ 9 * _root_.AbcTwoNinths.Terminal.floor K m r := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (K + 1))
    (H := by simp) (f := fun j => (K - j) * m + r * j ^ 2)
  have hj' : j ≤ K := by simpa using hj
  rw [_root_.AbcTwoNinths.Terminal.floor, he]
  zify [hj'] at hm ⊢
  have hk : 0 ≤ (K : ℤ) - j := sub_nonneg.mpr (by exact_mod_cast hj')
  nlinarith only [mul_le_mul_of_nonneg_right hm hk,
    mul_nonneg (Int.natCast_nonneg r) (sq_nonneg (3 * (j : ℤ) - 2 * K))]

/--
The valuation of a nonzero p-adic integral interpolation determinant is at least the valuation floor. This is used in Section 7 of the paper.
-/
theorem integralMinorValuation {K p : ℕ} [Fact p.Prime] (m r : ℕ)
    (x y : _root_.AbcTwoNinths.Terminal.Slots K → ℤ) (z a : ℤ_[p]ˣ)
    (hz : (p : ℤ_[p]) ^ m ∣ (z : ℤ_[p]) - 1)
    (ha : (p : ℤ_[p]) ^ r ∣ (a : ℤ_[p]) - 1)
    (hdet : (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det ≠ 0) :
    _root_.AbcTwoNinths.Terminal.floor K m r ≤ (_root_.AbcTwoNinths.Terminal.integralMinor x y z a).det.valuation :=
  (PadicInt.mem_span_pow_iff_le_valuation _ hdet _).mp
    (Ideal.mem_span_singleton.mpr (_root_.AbcTwoNinths.Terminal.integralMinorDvd m r x y _ z a hz ha))

end

end AbcTwoNinths.Terminal
