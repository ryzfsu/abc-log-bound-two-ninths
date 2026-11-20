/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.BadPairCount
public import AbcTwoNinths.Paper.S6_Diamond.MassThreshold
public import Mathlib.NumberTheory.Harmonic.Bounds
public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePlane

/-!
# Auxiliary prime pair

Constructs two auxiliary primes and a rank-two lattice with a short transverse vector and a lower
bound on low-denominator slope approximations. This is Lemma 6.2 of the paper.

## Main results
* `AbcTwoNinths.Diamond.divisorSumLe`
* `AbcTwoNinths.Diamond.tupleCodeMemProductPairs`
* `AbcTwoNinths.Diamond.oldImageCardLe`
* `AbcTwoNinths.Diamond.signedPairsCardLe`
* `AbcTwoNinths.Diamond.denominatorWeightOnset`
* `AbcTwoNinths.Diamond.costProjectEq`
* `AbcTwoNinths.Diamond.existsRoofBad`
* `AbcTwoNinths.Diamond.nativeRatioCancel`
* `AbcTwoNinths.Diamond.nativeRoofBad`
* `AbcTwoNinths.Diamond.existsFreshPrimePair`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section




/--
Counting positive integer pairs under a product cutoff. This is used in Section 6 of the paper.
-/
theorem divisorSumLe (N : ℕ) :
    ((∑ a ∈ Finset.Icc 1 N, N / a : ℕ) : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (N : ℝ) / a := by
      rw [Nat.cast_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      have ha' : 0 < a := (Finset.mem_Icc.mp ha).1
      apply (le_div_iff₀ (show (0 : ℝ) < a by exact_mod_cast ha')).mpr
      exact_mod_cast Nat.div_mul_le_self N a
    _ = (N : ℝ) * (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg _)

/-- Positive integer pairs with product at most `N`. This is used in Section 6 of the paper. -/
def productPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)

/-- Membership in the product-pair set is equivalent to positivity of both coordinates and
the bound on their product. -/
theorem memProductPairs {N : ℕ} {ab : ℕ × ℕ} :
    ab ∈ _root_.AbcTwoNinths.Diamond.productPairs N ↔ 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1 * ab.2 ≤ N := by
  simp only [_root_.AbcTwoNinths.Diamond.productPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => ⟨h.1.1.1, h.1.2.1, h.2⟩, fun h => ?_⟩
  exact ⟨⟨⟨h.1, (Nat.le_mul_of_pos_right _ h.2.1).trans h.2.2⟩,
    ⟨h.2.1, (Nat.le_mul_of_pos_left _ h.1).trans h.2.2⟩⟩, h.2.2⟩

/-- Summing the integer quotients `N / a` over positive first coordinates bounds the number
of pairs with product at most `N`. -/
theorem productPairsCardLe (N : ℕ) :
    (_root_.AbcTwoNinths.Diamond.productPairs N).card ≤ ∑ a ∈ Finset.Icc 1 N, N / a := by
  have hmap : ∀ ab ∈ _root_.AbcTwoNinths.Diamond.productPairs N, ab.1 ∈ Finset.Icc 1 N := by
    intro ab hab
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_le_sum fun a ha => ?_
  let F := (_root_.AbcTwoNinths.Diamond.productPairs N).filter (fun ab => ab.1 = a)
  have hinj : Set.InjOn Prod.snd (↑F : Set (ℕ × ℕ)) := by
    intro ab hab cd hcd h
    exact Prod.ext ((Finset.mem_filter.mp hab).2.trans (Finset.mem_filter.mp hcd).2.symm) h
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card (t := Finset.Icc 1 (N / a)) ?_).trans (by simp [Nat.card_Icc])
  intro b hb
  obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hmem, hfst⟩ := Finset.mem_filter.mp hab
  obtain ⟨h₁, h₂, hmul⟩ := _root_.AbcTwoNinths.Diamond.memProductPairs.mp hmem
  have ha' : 0 < a := (Finset.mem_Icc.mp ha).1
  exact Finset.mem_Icc.mpr ⟨h₂, (Nat.le_div_iff_mul_le ha').mpr (by simpa [← hfst, Nat.mul_comm] using hmul)⟩

/-- For nonnegative `t`, at most `Real.exp t * (1 + t)` positive integer pairs have product
at most `Real.exp t`. -/
theorem productPairsCardExpLe (t : ℝ) (ht : 0 ≤ t) :
    ((_root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp t⌋₊).card : ℝ) ≤ Real.exp t * (1 + t) := by
  have hfloor : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_nonneg _)
  have hone : 1 ≤ ⌊Real.exp t⌋₊ := Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr ht)
  calc
    _ ≤ ((∑ a ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, ⌊Real.exp t⌋₊ / a : ℕ) : ℝ) := by
      exact_mod_cast _root_.AbcTwoNinths.Diamond.productPairsCardLe ⌊Real.exp t⌋₊
    _ ≤ (⌊Real.exp t⌋₊ : ℝ) * (1 + Real.log ⌊Real.exp t⌋₊) := _root_.AbcTwoNinths.Diamond.divisorSumLe _
    _ ≤ Real.exp t * (1 + t) := by
      have hone' : (1 : ℝ) ≤ ⌊Real.exp t⌋₊ := by exact_mod_cast hone
      have hpos : 0 < (⌊Real.exp t⌋₊ : ℝ) := by linarith
      have hlog' := Real.log_le_log hpos hfloor
      rw [Real.log_exp] at hlog'
      exact mul_le_mul hfloor (by linarith)
        (by linarith [Real.log_nonneg hone']) (Real.exp_nonneg _)

/--
The logarithm of the product of the two codes is the full weighted length. This is used in Section 6 of the paper.
-/
theorem tupleCodeMemProductPairs {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (u : ι → ℤ) (t : ℝ)
    (hu : _root_.AbcTwoNinths.Diamond.length q u ≤ t) : _root_.AbcTwoNinths.Diamond.tupleCode q u ∈ _root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp t⌋₊ := by
  have hpos := _root_.AbcTwoNinths.Diamond.primeProductPos q (fun i => (u i).toNat) hp
  have hneg := _root_.AbcTwoNinths.Diamond.primeProductPos q (fun i => (-u i).toNat) hp
  apply _root_.AbcTwoNinths.Diamond.memProductPairs.mpr
  refine ⟨hpos, hneg, Nat.le_floor ?_⟩
  change ((_root_.AbcTwoNinths.Diamond.primeProduct q _ * _root_.AbcTwoNinths.Diamond.primeProduct q _ : ℕ) : ℝ) ≤ Real.exp t
  rw [Nat.cast_mul, ← Real.log_le_iff_le_exp (mul_pos (by exact_mod_cast hpos) (by exact_mod_cast hneg)),
    Real.log_mul (by exact_mod_cast hpos.ne') (by exact_mod_cast hneg.ne')]
  unfold _root_.AbcTwoNinths.Diamond.primeProduct _root_.AbcTwoNinths.Diamond.length at *
  rw [Nat.cast_prod, Nat.cast_prod,
    Real.log_prod (fun i _ => by exact_mod_cast pow_ne_zero _ (hp i).ne_zero),
    Real.log_prod (fun i _ => by exact_mod_cast pow_ne_zero _ (hp i).ne_zero)]
  simp only [Nat.cast_pow, Real.log_pow, ← Finset.sum_add_distrib, ← add_mul]
  convert hu using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have habs : ((u i).toNat : ℤ) + ((-u i).toNat : ℤ) = |u i| := by
    by_cases h : 0 ≤ u i
    · rw [abs_of_nonneg h, Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega), Int.natCast_zero, add_zero]
    · rw [abs_of_neg (by omega), Int.toNat_of_nonpos (by omega), Int.toNat_of_nonneg (by omega), Int.natCast_zero, zero_add]
  exact_mod_cast habs

/--
The old coordinates in a single roof and residue cell have one product code each. This is used in Section 6 of the paper.
-/
theorem oldImageCardLe {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0)
    {b : ℕ} (hb : 0 < b) (T : ℝ) (S : Finset _root_.AbcTwoNinths.Diamond.Pair) (a : _root_.AbcTwoNinths.Diamond.Pair → ℤ)
    (u : _root_.AbcTwoNinths.Diamond.Pair → ι → ℤ) (c r : ℤ)
    (hcell : ∀ s ∈ S, (a s • v + b • u s) roof = c ∧ a s % (b : ℤ) = r ∧
      _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v (u s)) ≤ T) :
    (S.image (fun s => a s • v + b • u s)).card ≤ (_root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2 * T)⌋₊).card := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    let old := fun s => a s • v + b • u s
    let I := S.image old
    let d := fun w : ι → ℤ => fun i => (w i - old s₀ i) / (b : ℤ)
    have hd : ∀ w ∈ I, w - old s₀ = b • d w ∧ _root_.AbcTwoNinths.Diamond.length q (d w) ≤ 2 * T := by
      intro w hw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨e, he, heL⟩ := _root_.AbcTwoNinths.Diamond.integralDifference q hp roof v hv hb (a s) (a s₀)
        (u s) (u s₀) T ((hcell s hs).2.1.trans (hcell s₀ hs₀).2.1.symm)
        ((hcell s hs).1.trans (hcell s₀ hs₀).1.symm) (hcell s hs).2.2 (hcell s₀ hs₀).2.2
      have he' : d (old s) = e := by
        funext i
        have hi := congrFun he i
        change old s i - old s₀ i = (b : ℤ) * e i at hi
        change (old s i - old s₀ i) / (b : ℤ) = e i
        rw [hi, Int.mul_ediv_cancel_left _ (by exact_mod_cast hb.ne')]
      rw [he']
      exact ⟨he, heL⟩
    have hinj : Set.InjOn (_root_.AbcTwoNinths.Diamond.tupleCode q ∘ d) (↑I : Set (ι → ℤ)) := by
      intro w hw z hz h
      have eq := _root_.AbcTwoNinths.Diamond.tupleCodeInjective q hp hiq h
      apply sub_left_inj.mp
      exact (hd w hw).1.trans (eq ▸ (hd z hz).1.symm)
    change I.card ≤ _
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
    exact _root_.AbcTwoNinths.Diamond.tupleCodeMemProductPairs q hp (d w) _ (hd w hw).2
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/--
Sharp product-count version of the signed bad-pair lemma. This is used in Section 6 of the paper.
-/
theorem signedPairsCardLe {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) (T : ℝ) (C B : ℕ)
    (S : Finset _root_.AbcTwoNinths.Diamond.Pair) (hCross : _root_.AbcTwoNinths.Diamond.CrossBound p (↑S : Set _root_.AbcTwoNinths.Diamond.Pair))
    (a : _root_.AbcTwoNinths.Diamond.Pair → ℤ) (b : _root_.AbcTwoNinths.Diamond.Pair → ℕ) (u : _root_.AbcTwoNinths.Diamond.Pair → ι → ℤ)
    (evalOld : (ι → ℤ) → ZMod p)
    (hB : ∀ s ∈ S, 0 < b s ∧ b s ≤ B)
    (hC : ∀ s ∈ S, (a s • v + b s • u s) roof ∈ Finset.Icc (-(C : ℤ)) C)
    (hT : ∀ s ∈ S, _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v (u s)) ≤ T)
    (hSigned : ∀ s ∈ S, let e := evalOld (a s • v + b s • u s) * _root_.AbcTwoNinths.Diamond.ratio p s ^ b s;
      e = 1 ∨ e = -1) :
    S.card ≤ (2 * C + 1) * (_root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2 * T)⌋₊).card *
      ∑ k ∈ Finset.Icc 1 B, 2 * k ^ 2 := by
  classical
  let D := (_root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2 * T)⌋₊).card
  let old := fun s => a s • v + b s • u s
  let I := Finset.Icc 1 B
  let c := fun s => old s roof
  let m := fun s => a s % (b s : ℤ)
  have hmem : ∀ s ∈ S, b s ∈ I := fun s hs => Finset.mem_Icc.mpr (hB s hs)
  rw [Finset.card_eq_sum_card_fiberwise hmem, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  let P := S.filter (fun s => b s = k)
  let J := (Finset.Icc (-(C : ℤ)) C) ×ˢ (Finset.Ico 0 (k : ℤ))
  have hk₀ : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkz : 0 < (k : ℤ) := by exact_mod_cast hk₀
  have hm (s : _root_.AbcTwoNinths.Diamond.Pair) (hs : s ∈ P) : s ∈ S ∧ b s = k := Finset.mem_filter.mp hs
  have hmap : ∀ s ∈ P, (c s, m s) ∈ J := by
    intro s hs
    refine Finset.mem_product.mpr ⟨hC s (hm s hs).1, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · simp only [m, (hm s hs).2]
      exact Int.emod_nonneg _ hkz.ne'
    · simp only [m, (hm s hs).2]
      exact Int.emod_lt_of_pos _ hkz
  change P.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hcell : ∀ j ∈ J, (P.filter (fun s => (c s, m s) = j)).card ≤ D * (2 * k) := by
    intro j _
    let Q := P.filter (fun s => (c s, m s) = j)
    have hQ (s : _root_.AbcTwoNinths.Diamond.Pair) (hs : s ∈ Q) : s ∈ S ∧ b s = k ∧ (c s, m s) = j :=
      ⟨(hm s (Finset.mem_filter.mp hs).1).1, (hm s (Finset.mem_filter.mp hs).1).2,
        (Finset.mem_filter.mp hs).2⟩
    let inv := Q.image old
    have hInv : inv.card ≤ D := by
      have hold : Q.image old = Q.image (fun s => a s • v + k • u s) :=
        Finset.image_congr fun s hs => by simp [old, (hQ s hs).2.1]
      rw [show inv = Q.image old from rfl, hold]
      apply _root_.AbcTwoNinths.Diamond.oldImageCardLe q hp hiq roof v hv hk₀ T Q a u j.1 j.2
      intro s hs
      obtain ⟨hS, hb, hj⟩ := hQ s hs
      refine ⟨?_, ?_, hT s hS⟩
      · simpa [c, old, hb] using congrArg Prod.fst hj
      · simpa [m, hb] using congrArg Prod.snd hj
    calc
      Q.card ≤ ∑ w ∈ inv, 2 * k :=
        _root_.AbcTwoNinths.Diamond.cardLeSumSignedFibers Q
          (fun s hs t ht => hCross s (hQ s hs).1 t (hQ t ht).1)
          inv old (fun _ => k) evalOld
          (fun s hs => Finset.mem_image_of_mem old hs) (fun _ _ => hk₀)
          (fun s hs => by simpa [old, (hQ s hs).2.1] using hSigned s (hQ s hs).1)
      _ = inv.card * (2 * k) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hInv
  calc
    _ ≤ ∑ _j ∈ J, D * (2 * k) := Finset.sum_le_sum hcell
    _ = _ := by
      have hj : J.card = (2 * C + 1) * k := by
        simp only [J, Finset.card_product, Int.card_Icc, Int.card_Ico, sub_zero]
        rw [Int.toNat_natCast]
        congr 1
        omega
      rw [Finset.sum_const, nsmul_eq_mul, hj]
      change ((2 * C + 1) * k) * (D * (2 * k)) = (2 * C + 1) * D * (2 * k ^ 2)
      ring

/-- The radius. This is used in Section 6 of the paper. -/
noncomputable def radius (x : ℝ) : ℝ := 2 * x / Real.log x

/-- The denominator weight. This is used in Section 6 of the paper. -/
def denominatorWeight (W : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 W, 2 * k ^ 2

/--
At the common radius the harmonic factor is paid by the unused part of
the literal denominator sum. `W` is fixed before the onset. This is used in Section 6 of the paper.
-/
theorem denominatorWeightOnset (W : ℕ) {x L : ℝ} (hx : Real.exp 1 ≤ x)
    (hx₂ : 2 ≤ x) (hcut : 10 * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) ≤ x)
    (hL : 0 < L) (hLx : L ≤ x) :
    (1 + 2 * _root_.AbcTwoNinths.Diamond.radius x) * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) ≤
      _root_.AbcTwoNinths.Diamond.denominatorWeight ⌊2 * x ^ 2 / L⌋₊ := by
  have hlog : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos (1 : ℝ)) hx
  have hx₀ : 0 ≤ x := by linarith
  have hrad : _root_.AbcTwoNinths.Diamond.radius x ≤ 2 * x := div_le_self (by positivity) hlog
  have hfactor : 1 + 2 * _root_.AbcTwoNinths.Diamond.radius x ≤ 5 * x := by linarith
  let k := ⌊x⌋₊
  have hk : 0 < k := Nat.floor_pos.mpr (by linarith)
  have hkHalf : x / 2 ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one x
    change x < (k : ℝ) + 1 at h
    linarith
  have hkb : k ≤ ⌊2 * x ^ 2 / L⌋₊ := by
    apply Nat.le_floor
    apply (Nat.floor_le hx₀).trans
    apply (le_div_iff₀ hL).mpr
    have hmul := mul_le_mul_of_nonneg_left hLx hx₀
    nlinarith
  have hsum : 2 * k ^ 2 ≤ _root_.AbcTwoNinths.Diamond.denominatorWeight ⌊2 * x ^ 2 / L⌋₊ := by
    exact Finset.single_le_sum (f := fun j : ℕ => 2 * j ^ 2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨hk, hkb⟩)
  have hkSq := pow_le_pow_left₀ (show 0 ≤ x / 2 by positivity) hkHalf 2
  calc
    _ ≤ (5 * x) * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) := mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ x ^ 2 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hcut hx₀]
    _ ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
    _ ≤ _ := by exact_mod_cast hsum

/-- The exceptional-pair bound applies to signed pairs with bounded denominators,
distinguished coordinates, and projected cost at the Section 6 radius. -/
theorem signedPairsAtRadius {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) {x L : ℝ} (W : ℕ)
    (hx : Real.exp 1 ≤ x) (hx₂ : 2 ≤ x) (hcut : 10 * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) ≤ x)
    (hL : 0 < L) (hLx : L ≤ x) (S : Finset _root_.AbcTwoNinths.Diamond.Pair) (hCross : _root_.AbcTwoNinths.Diamond.CrossBound p (↑S : Set _root_.AbcTwoNinths.Diamond.Pair))
    (a : _root_.AbcTwoNinths.Diamond.Pair → ℤ) (b : _root_.AbcTwoNinths.Diamond.Pair → ℕ) (u : _root_.AbcTwoNinths.Diamond.Pair → ι → ℤ)
    (evalOld : (ι → ℤ) → ZMod p)
    (hB : ∀ s ∈ S, 0 < b s ∧ b s ≤ W)
    (hC : ∀ s ∈ S, (a s • v + b s • u s) roof ∈
      Finset.Icc (-(⌊x ^ 2 / Real.log 2⌋₊ : ℤ)) ⌊x ^ 2 / Real.log 2⌋₊)
    (hT : ∀ s ∈ S, _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v (u s)) ≤ _root_.AbcTwoNinths.Diamond.radius x)
    (hSigned : ∀ s ∈ S, let e := evalOld (a s • v + b s • u s) * _root_.AbcTwoNinths.Diamond.ratio p s ^ b s;
      e = 1 ∨ e = -1) :
    (S.card : ℝ) ≤ _root_.AbcTwoNinths.Diamond.badBudget x L := by
  have hlog : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos (1 : ℝ)) hx
  have hrad : 0 ≤ _root_.AbcTwoNinths.Diamond.radius x := by unfold _root_.AbcTwoNinths.Diamond.radius; positivity
  have count := _root_.AbcTwoNinths.Diamond.signedPairsCardLe q hp hiq roof v hv (_root_.AbcTwoNinths.Diamond.radius x) _ W S hCross a b u evalOld hB hC hT hSigned
  have hD := _root_.AbcTwoNinths.Diamond.productPairsCardExpLe (2 * _root_.AbcTwoNinths.Diamond.radius x) (by positivity)
  have hW := _root_.AbcTwoNinths.Diamond.denominatorWeightOnset W hx hx₂ hcut hL hLx
  have hexp : 2 * _root_.AbcTwoNinths.Diamond.radius x = 4 * ((1 / Real.log x) * x) := by unfold _root_.AbcTwoNinths.Diamond.radius; ring
  let C := ⌊x ^ 2 / Real.log 2⌋₊
  calc
    _ ≤ (2 * (C : ℝ) + 1) * ((_root_.AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2 * _root_.AbcTwoNinths.Diamond.radius x)⌋₊).card : ℝ) *
          (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) := by exact_mod_cast count
    _ ≤ (2 * (C : ℝ) + 1) * (Real.exp (2 * _root_.AbcTwoNinths.Diamond.radius x) * (1 + 2 * _root_.AbcTwoNinths.Diamond.radius x)) *
          (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) := by gcongr
    _ = (2 * (C : ℝ) + 1) * Real.exp (2 * _root_.AbcTwoNinths.Diamond.radius x) *
          ((1 + 2 * _root_.AbcTwoNinths.Diamond.radius x) * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ)) := by ring
    _ ≤ _ := by
      unfold _root_.AbcTwoNinths.Diamond.badBudget _root_.AbcTwoNinths.Diamond.denominatorWeight at *
      rw [hexp] at hW ⊢
      gcongr




open MeasureTheory

private theorem combinationSigned {ι : Type*} {p : ℕ} [Fact p.Prime]
    (red : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (v u : ι → ℤ) (ρ : (ZMod p)ˣ)
    (a : ℤ) (b : ℕ) (hv : _root_.AbcTwoNinths.ExteriorE2.reduction red (Multiplicative.ofAdd v) = 1)
    (hu : _root_.AbcTwoNinths.ExteriorE2.reduction red (Multiplicative.ofAdd u) * _root_.AbcTwoNinths.Diamond.quotientLabel ρ = 1) :
    let e := (red (Multiplicative.ofAdd (a • v + b • u)) : ZMod p) * (ρ : ZMod p)^b
    e = 1 ∨ e = -1 := by
  apply _root_.AbcTwoNinths.Diamond.signedOfQuotient
  change _root_.AbcTwoNinths.ExteriorE2.reduction red ((Multiplicative.ofAdd v) ^ a * (Multiplicative.ofAdd u) ^ b) *
    _root_.AbcTwoNinths.Diamond.quotientLabel ρ ^ b = 1
  rw [map_mul, map_zpow, map_pow, hv, one_zpow, one_mul]
  calc
    _ = (_root_.AbcTwoNinths.ExteriorE2.reduction red (Multiplicative.ofAdd u) * _root_.AbcTwoNinths.Diamond.quotientLabel ρ) ^ b := by
      have eq := congrArg (QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p))
        ((mul_pow (red (Multiplicative.ofAdd u)) ρ b).symm)
      simpa only [_root_.AbcTwoNinths.ExteriorE2.reduction, MonoidHom.comp_apply, _root_.AbcTwoNinths.Diamond.quotientLabel, map_mul, map_pow] using eq
    _ = 1 := by rw [hu, one_pow]

private theorem roofMem {u v P : ℤ} {Q : ℕ} {h K x ℓ : ℝ}
    (hv : v ≠ 0) (hh : |(v : ℝ)| * Real.log 2 ≤ h)
    (hl : ℓ ≤ x) (hK : 0 ≤ K) (hx : K ≤ x)
    (hclose : |(Q : ℝ) * ((u : ℝ) / (v : ℝ)) - (P : ℝ)| * h ≤ K * ℓ) :
    -P * v + (Q : ℤ) * u ∈ Finset.Icc (-(⌊x ^ 2 / Real.log 2⌋₊ : ℤ))
      (⌊x ^ 2 / Real.log 2⌋₊ : ℤ) := by
  let j : ℤ := -P * v + (Q : ℤ) * u
  let a : ℝ := (Q : ℝ) * ((u : ℝ) / (v : ℝ)) - (P : ℝ)
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hc : (j : ℝ) = a * (v : ℝ) := by
    dsimp [j, a]
    push_cast
    field_simp
    ring
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hw : |(j : ℝ)| * Real.log 2 ≤ x ^ 2 := by
    rw [hc, abs_mul, mul_assoc]
    calc
      _ ≤ |a| * h := mul_le_mul_of_nonneg_left hh (abs_nonneg a)
      _ ≤ K * ℓ := hclose
      _ ≤ K * x := mul_le_mul_of_nonneg_left hl hK
      _ ≤ x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hx (hK.trans hx)]
  have habs : |(j : ℝ)| ≤ x ^ 2 / Real.log 2 := (le_div_iff₀ hl2).mpr hw
  rw [Int.natCast_floor_eq_floor (div_nonneg (sq_nonneg x) hl2.le)]
  exact Finset.mem_Icc.mpr ⟨neg_le.mp (Int.le_floor.mpr (by
    simpa only [Int.cast_neg] using (neg_le_abs (j : ℝ)).trans habs)),
    Int.le_floor.mpr ((le_abs_self (j : ℝ)).trans habs)⟩

/--
The projected cost with the literal logarithmic weights on the nonroof coordinates. This is used in Section 6 of the paper.
-/
theorem costProjectEq {I : Type*} [Fintype I] (old : Unit ⊕ I → ℕ) (v u : Unit ⊕ I → ℤ)
    (hv : v (.inl ()) ≠ 0) :
    _root_.AbcTwoNinths.Diamond.cost old (_root_.AbcTwoNinths.Diamond.roofProjection (.inl ()) v u) =
      _root_.AbcTwoNinths.ExteriorE2.cost (fun i => Real.log (old (.inr i))) (_root_.AbcTwoNinths.ExteriorE2.project v u) := by
  classical
  unfold _root_.AbcTwoNinths.Diamond.cost _root_.AbcTwoNinths.ExteriorE2.cost
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  have hz : _root_.AbcTwoNinths.Diamond.roofProjection (.inl ()) v u (.inl ()) = 0 := by
    change (u (.inl ()) : ℝ) - (u (.inl ()) : ℝ) / (v (.inl ()) : ℝ) * (v (.inl ()) : ℝ) = 0
    have hv' : (v (.inl ()) : ℝ) ≠ 0 := by exact_mod_cast hv
    simp [hv']
  rw [hz, abs_zero, zero_mul, zero_add]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The slope good. This is used in Section 6 of the paper. -/
def SlopeGood (W : ℕ) (u v : ℤ) (h ℓ K : ℝ) : Prop :=
  ∀ Q : ℕ, 0 < Q → Q ≤ W → ∀ P : ℤ,
    K * ℓ ≤ |(Q : ℝ) * ((u : ℝ) / (v : ℝ)) - (P : ℝ)| * h

/--
A bad set declared before the fresh vector is selected. Every short old
witness on a surviving pair has the required roof slope. This is used in Section 6 of the paper.
-/
theorem existsRoofBad {ι : Type*} [Fintype ι] {p R : ℕ} [Fact p.Prime]
    (old : ι → ℕ) (prime : ∀ i, (old i).Prime) (hi : Function.Injective old)
    (roof : ι) (red : _root_.AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ) (v : ι → ℤ)
    (hv : v roof ≠ 0) (hvred : _root_.AbcTwoNinths.ExteriorE2.reduction red (Multiplicative.ofAdd v) = 1)
    (W : ℕ) {h K x M : ℝ} (hh : |(v roof : ℝ)| * Real.log 2 ≤ h)
    (hK : 0 ≤ K) (hKx : K ≤ x) (hx : Real.exp 1 ≤ x) (hx₂ : 2 ≤ x)
    (hcut : 10 * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) ≤ x) (hℓ : Real.log p ≤ x)
    (hM : 0 ≤ M) (hL : 0 < Real.log M) (hLx : Real.log M ≤ x) (hcross : M ^ 2 < p) :
    ∃ bad : Finset (ℕ × ℕ), (bad.card : ℝ) ≤ _root_.AbcTwoNinths.Diamond.badBudget x (Real.log M) ∧
      ∀ s : _root_.AbcTwoNinths.Diamond.Pair, s.val ∉ bad → _root_.AbcTwoNinths.ExteriorE2.Fresh M R s.val.1 → _root_.AbcTwoNinths.ExteriorE2.Fresh M R s.val.2 →
        ∀ (u : ι → ℤ) (ρ : (ZMod p)ˣ), (ρ : ZMod p) = _root_.AbcTwoNinths.Diamond.ratio p s →
          _root_.AbcTwoNinths.ExteriorE2.reduction red (Multiplicative.ofAdd u) * _root_.AbcTwoNinths.Diamond.quotientLabel ρ = 1 →
          _root_.AbcTwoNinths.Diamond.cost old (_root_.AbcTwoNinths.Diamond.roofProjection roof v u) < _root_.AbcTwoNinths.Diamond.radius x →
          _root_.AbcTwoNinths.Diamond.SlopeGood W (u roof) (v roof) h (Real.log p) K := by
  classical
  let base := _root_.AbcTwoNinths.ExteriorE2.fresh R M
  let pairs := (base ×ˢ base).subtype (fun s => s.1.Prime ∧ s.2.Prime ∧ s.1 ≠ s.2)
  let cert (s : _root_.AbcTwoNinths.Diamond.Pair) (a : ℤ) (b : ℕ) (u : ι → ℤ) : Prop :=
    (0 < b ∧ b ≤ W) ∧
    (a • v + b • u) roof ∈ Finset.Icc (-(⌊x ^ 2 / Real.log 2⌋₊ : ℤ)) ⌊x ^ 2 / Real.log 2⌋₊ ∧
    _root_.AbcTwoNinths.Diamond.cost old (_root_.AbcTwoNinths.Diamond.roofProjection roof v u) ≤ _root_.AbcTwoNinths.Diamond.radius x ∧
    (let z := (red (Multiplicative.ofAdd (a • v + b • u)) : ZMod p) * _root_.AbcTwoNinths.Diamond.ratio p s ^ b
     z = 1 ∨ z = -1)
  let F := pairs.filter (fun s => ∃ a b u, cert s a b u)
  have pick (s : _root_.AbcTwoNinths.Diamond.Pair) : ∃ a b u, s ∈ F → cert s a b u := by
    by_cases hs : s ∈ F
    · obtain ⟨a, b, u, h⟩ := (Finset.mem_filter.mp hs).2
      exact ⟨a, b, u, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => (hs h).elim⟩
  choose a b u hw using pick
  have hxF : _root_.AbcTwoNinths.Diamond.CrossBound p (F : Set _root_.AbcTwoNinths.Diamond.Pair) := by
    apply _root_.AbcTwoNinths.Diamond.crossBoundOfUpper hcross
    intro s hs
    have hm : s.val.1 ∈ base ∧ s.val.2 ∈ base := by
      simpa only [pairs, Finset.mem_subtype, Finset.mem_product] using (Finset.mem_filter.mp hs).1
    exact ⟨((_root_.AbcTwoNinths.ExteriorE2.memFresh hM).mp hm.1).2.2.1, ((_root_.AbcTwoNinths.ExteriorE2.memFresh hM).mp hm.2).2.2.1⟩
  have count := _root_.AbcTwoNinths.Diamond.signedPairsAtRadius old prime hi roof v hv W hx hx₂ hcut hL hLx F hxF a b u
    (fun w => (red (Multiplicative.ofAdd w) : ZMod p))
    (fun s hs => (hw s hs).1) (fun s hs => (hw s hs).2.1)
    (fun s hs => (hw s hs).2.2.1) (fun s hs => (hw s hs).2.2.2)
  refine ⟨F.image Subtype.val, ?_, ?_⟩
  · simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using count
  · intro s hs h₁ h₂ w ρ hρ hcancel hshort Q hQ hQW P
    by_contra! hclose
    apply hs
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_filter.mpr ⟨?_, ⟨-P, Q, w, ⟨hQ, hQW⟩, ?_, hshort.le, ?_⟩⟩, rfl⟩
    · simpa only [pairs, Finset.mem_subtype, Finset.mem_product] using
        And.intro ((_root_.AbcTwoNinths.ExteriorE2.memFresh hM).mpr h₁) ((_root_.AbcTwoNinths.ExteriorE2.memFresh hM).mpr h₂)
    · exact roofMem hv hh hℓ hK hKx hclose.le
    · simpa only [hρ] using combinationSigned red v w ρ (-P) Q hvred hcancel

/--
Restricting an actual fresh lattice vector gives the signed old residue
condition with the same ratio of fresh primes. This is used in Section 6 of the paper.
-/
theorem nativeRatioCancel {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (old : ι → ℕ) (s : _root_.AbcTwoNinths.Diamond.Pair) (pr : ∀ j, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old s.val j).Prime)
    (av : ∀ j, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old s.val j)
    (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old s.val) pr av)
    (hu₁ : u.val.toAdd (.inr false) = 1) (hu₂ : u.val.toAdd (.inr true) = -1) :
    ∃ ρ : (ZMod p)ˣ, (ρ : ZMod p) = _root_.AbcTwoNinths.Diamond.ratio p s ∧
      _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.residue old (fun i => pr (.inl i)) (fun i => av (.inl i)))
        (Multiplicative.ofAdd (fun i => u.val.toAdd (.inl i))) * _root_.AbcTwoNinths.Diamond.quotientLabel ρ = 1 := by
  let base := _root_.AbcTwoNinths.Diamond.freshExtendedBase old s.val
  let w : _root_.AbcTwoNinths.ExteriorE2.Exponents ι := Multiplicative.ofAdd (fun i => u.val.toAdd (.inl i))
  let f := _root_.AbcTwoNinths.ExteriorE2.residueUnit base pr av
  let ρ := f (.inr false) / f (.inr true)
  refine ⟨ρ, ?_, ?_⟩
  · change (((f (.inr false) / f (.inr true) : (ZMod p)ˣ)) : ZMod p) = _
    rw [Units.val_div_eq_div_val]
    rfl
  · have hdecomp : u.val = _root_.AbcTwoNinths.Diamond.extendExponents w 1 (-1) := by
      apply Multiplicative.toAdd.injective
      funext i
      rcases i with i | (_ | _)
      · rfl
      · exact hu₁
      · exact hu₂
    have hk : _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.residue base pr av) u.val = 1 := u.property
    rw [hdecomp, _root_.AbcTwoNinths.ExteriorE2.residue, _root_.AbcTwoNinths.Diamond.reductionEval, _root_.AbcTwoNinths.Diamond.extendEval] at hk
    change _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.eval (fun i => f (.inl i))) w * _root_.AbcTwoNinths.Diamond.quotientLabel ρ = 1
    rw [_root_.AbcTwoNinths.Diamond.reductionEval]
    simpa only [ρ, _root_.AbcTwoNinths.Diamond.quotientLabel, map_div, zpow_one, zpow_neg_one, div_eq_mul_inv, map_mul, map_inv, f] using hk

-- The elaboration of fresh prime pair needs a larger budget.
set_option maxHeartbeats 1200000 in
/--
The actual native shell supplies the range and cross-product inequalities.
Every fresh lattice vector on a surviving pair supplies the signed witness. This is used in Section 6 of the paper.
-/
theorem nativeRoofBad {I : Type*} [Fintype I] {p R : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
    (hi : Function.Injective old) (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid)
    (hv : v.val.toAdd (.inl ()) ≠ 0) (W : ℕ) {h K x H η : ℝ}
    (hh : |(v.val.toAdd (.inl ()) : ℝ)| * Real.log 2 ≤ h)
    (hK : 0 ≤ K) (hKx : K ≤ x) (hx : Real.exp 1 ≤ x) (hx₂ : 2 ≤ x)
    (hcut : 10 * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ) ≤ x) (adm : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x) :
    let M := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
    ∃ bad : Finset (ℕ × ℕ), (bad.card : ℝ) ≤ _root_.AbcTwoNinths.Diamond.badBudget x (Real.log M) ∧
      ∀ q : ℕ × ℕ, q ∉ bad → _root_.AbcTwoNinths.ExteriorE2.Fresh M R q.1 → _root_.AbcTwoNinths.ExteriorE2.Fresh M R q.2 → q.1 < q.2 →
        ∀ (pr : ∀ j, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q j).Prime) (av : ∀ j, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old q j)
          (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av),
          u.val.toAdd (.inr false) = 1 → u.val.toAdd (.inr true) = -1 →
          _root_.AbcTwoNinths.ExteriorE2.cost (fun i => Real.log (old (.inr i)))
            (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < _root_.AbcTwoNinths.Diamond.radius x →
          _root_.AbcTwoNinths.Diamond.SlopeGood W (u.val.toAdd (.inl (.inl ()))) (v.val.toAdd (.inl ())) h (Real.log p) K := by
  let M := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
  have hM : 0 < M := _root_.AbcTwoNinths.ExteriorE2.MPos _ _ _ _
  have hmargin := mul_pos (_root_.AbcTwoNinths.ExteriorE2.marginPos adm.eta_lt) adm.hx
  have hslack := _root_.AbcTwoNinths.ExteriorE2.shellSlack adm
  have hL : 0 < Real.log M := hmargin.trans_le hslack.1
  have hLx : Real.log M ≤ x := by linarith [hslack.2, adm.log_hi]
  have hcross : M ^ 2 < (p : ℝ) := by
    rw [← Real.log_lt_log_iff (pow_pos hM _) adm.hp, Real.log_pow]
    norm_num
    linarith [hslack.2]
  obtain ⟨bad, hbad, good⟩ := _root_.AbcTwoNinths.Diamond.existsRoofBad (R := R) old prime hi (.inl ()) (_root_.AbcTwoNinths.ExteriorE2.residue old prime avoid)
    v.val.toAdd hv v.property W hh hK hKx hx hx₂ hcut adm.log_hi hM.le hL hLx hcross
  refine ⟨bad, hbad, ?_⟩
  intro q hq h₁ h₂ hlt pr av u hu₁ hu₂ hshort
  let s : _root_.AbcTwoNinths.Diamond.Pair := ⟨q, h₁.1, h₂.1, hlt.ne⟩
  obtain ⟨ρ, hρ, hcancel⟩ := _root_.AbcTwoNinths.Diamond.nativeRatioCancel old s pr av u hu₁ hu₂
  have hcost := (_root_.AbcTwoNinths.Diamond.costProjectEq old v.val.toAdd (fun i => u.val.toAdd (.inl i)) hv).symm ▸ hshort
  exact good s hq h₁ h₂ _ ρ hρ hcancel hcost

-- The elaboration of fresh prime pair needs a larger budget.
set_option maxHeartbeats 1500000 in
/-- Beyond a common threshold, two fresh primes produce a saturated rank-two plane whose
character is injective and whose distinguished coordinates satisfy the slope bound. -/
theorem diamondSlopeBounds {η K : ℝ} (hη : η < 1/9) (hK : 0 ≤ K) (W : ℕ) :
    ∃ X : ℝ, ∀ {I : Type} [Fintype I] [DecidableEq I]
      {p R : ℕ} [Fact p.Prime] [Fact (2 < p)] (_hpR : p ∣ R)
      (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
      (_hi : Function.Injective old) (_holdR : ∀ i, old i ∣ R) (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid)
      {H x B h : ℝ},
      let weight := fun i => Real.log (old (.inr i))
      X ≤ x → 0 < R → Real.log R = 3*x → _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x →
      max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin η)) / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ x →
      v.val.toAdd (.inl ()) ≠ 0 →
      (∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (a : ℝ),
        (∀ i, (w.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, w = v ^ c) →
      (∀ w ∈ (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid).toAdditive.ker,
        _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd w) < _root_.AbcTwoNinths.Diamond.radius x →
          _root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd w = 0) →
      0 < B → (∑ i, weight i) ≤ B →
      H ≤ 3*x*|(v.val.toAdd (.inl ()) : ℝ)| →
      |(v.val.toAdd (.inl ()) : ℝ)| * Real.log 2 ≤ h →
      _root_.AbcTwoNinths.Diamond.massFloor x ≤ (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real
        (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 (_root_.AbcTwoNinths.Diamond.radius x/2)) →
      ∃ q : ℕ × ℕ, let M := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
        _root_.AbcTwoNinths.ExteriorE2.Fresh M R q.1 ∧ _root_.AbcTwoNinths.ExteriorE2.Fresh M R q.2 ∧ q.1 < q.2 ∧
        ∃ (pr : ∀ j, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q j).Prime) (av : ∀ j, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old q j)
          (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av),
          let V := _root_.AbcTwoNinths.Diamond.extension (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av v
          let γ := _root_.AbcTwoNinths.Diamond.planeCharacter (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av V u
          u.val.toAdd (.inr false) = 1 ∧ u.val.toAdd (.inr true) = -1 ∧
          _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < _root_.AbcTwoNinths.Diamond.radius x ∧
          (∀ y : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av, _root_.AbcTwoNinths.Diamond.inRealPlane V.val u.val y.val →
            ∃! c : ℤ × ℤ, y.val = _root_.AbcTwoNinths.Diamond.along V.val u.val c) ∧ Function.Injective γ ∧
          (γ (Multiplicative.ofAdd ((1,0) : ℤ × ℤ)) : ℚ) = _root_.AbcTwoNinths.Diamond.character old prime avoid v ∧
          _root_.AbcTwoNinths.Diamond.SlopeGood W (u.val.toAdd (.inl (.inl ()))) (v.val.toAdd (.inl ())) h (Real.log p) K := by
  obtain ⟨X, select⟩ := _root_.AbcTwoNinths.Diamond.freshPrimeMassEventually hη
  refine ⟨max X (max (Real.exp 1) (max 2 (max K (10 * (_root_.AbcTwoNinths.Diamond.denominatorWeight W : ℝ))))), ?_⟩
  intro I _ _ p R _ _ hpR old prime avoid hi holdR v H x B h
  dsimp only
  intro hx hR hRx adm hshell hv hline hsep hB hW hroof hh hmass
  have hxX := (le_max_left X _).trans hx
  have hx₀ := (le_max_right X _).trans hx
  have he := (le_max_left (Real.exp 1) _).trans hx₀
  have hx₁ := (le_max_right (Real.exp 1) _).trans hx₀
  have hx₂ := (le_max_left (2 : ℝ) _).trans hx₁
  have hx₃ := (le_max_right (2 : ℝ) _).trans hx₁
  have hKx := (le_max_left K _).trans hx₃
  have hcut := (le_max_right K _).trans hx₃
  have hlog : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos (1 : ℝ)) he
  have hr : 0 < _root_.AbcTwoNinths.Diamond.radius x := div_pos (by positivity [adm.hx]) (by linarith)
  let weight := fun i : I => Real.log (old (.inr i))
  have hw : ∀ i, 0 < weight i := fun i => Real.log_pos (by exact_mod_cast (prime (.inr i)).one_lt)
  obtain ⟨bad, hbad, slope⟩ := _root_.AbcTwoNinths.Diamond.nativeRoofBad (R := R) old prime avoid hi v hv W hh hK hKx he hx₂ hcut adm
  obtain ⟨q, hq, hf, ht, hlt, pr, av, u, hu₁, hu₂, hshort, hplane, hinj, hsource⟩ :=
    select hpR old prime avoid hi holdR v weight bad hxX hR hRx adm hshell hv hline hsep hw hr hB hW hroof hmass hbad
  exact ⟨q, hf, ht, hlt, pr, av, u, hu₁, hu₂, hshort, hplane, hinj, hsource,
    slope q hq hf ht hlt pr av u hu₁ hu₂ hshort⟩

end

end AbcTwoNinths.Diamond

namespace AbcTwoNinths.Diamond

open MeasureTheory

/--
The auxiliary primes and their separated plane exist beyond a threshold depending
only on the shell parameter, the slope bound, and the denominator limit. This is
Lemma 6.2 of the paper. This is used in Section 6 of the paper.
-/
theorem existsFreshPrimePair {η K : ℝ} (hη : η < 1 / 9) (hK : 0 ≤ K) (W : ℕ) :
    ∃ X : ℝ, ∀ {I : Type} [Fintype I] [DecidableEq I]
      {p R : ℕ} [Fact p.Prime] [Fact (2 < p)] (_hpR : p ∣ R)
      (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
      (_hi : Function.Injective old) (_holdR : ∀ i, old i ∣ R)
      (v : AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) {H x h : ℝ},
      let weight := fun i => Real.log (old (.inr i))
      X ≤ x → 0 < R → Real.log R = 3 * x → AbcTwoNinths.ExteriorE2.Admissible p H η x →
      v.val.toAdd (.inl ()) ≠ 0 →
      (∀ (w : AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (a : ℝ),
        (∀ i, (w.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, w = v ^ c) →
      (∀ w ∈ (AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid).toAdditive.ker,
        AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project v.val.toAdd w) < AbcTwoNinths.Diamond.radius x →
          AbcTwoNinths.ExteriorE2.project v.val.toAdd w = 0) →
      H ≤ 3 * x * |(v.val.toAdd (.inl ()) : ℝ)| →
      |(v.val.toAdd (.inl ()) : ℝ)| * Real.log 2 ≤ h →
      AbcTwoNinths.Diamond.massFloor x ≤ (volume : Measure (AbcTwoNinths.ExteriorE2.Coord I)).real
        (AbcTwoNinths.ExteriorE2.ball weight 0 (AbcTwoNinths.Diamond.radius x / 2)) →
      ∃ q : ℕ × ℕ, let M := AbcTwoNinths.ExteriorE2.m p H (AbcTwoNinths.ExteriorE2.margin η) x
        AbcTwoNinths.ExteriorE2.Fresh M R q.1 ∧ AbcTwoNinths.ExteriorE2.Fresh M R q.2 ∧ q.1 < q.2 ∧
        ∃ (pr : ∀ j, (AbcTwoNinths.Diamond.freshExtendedBase old q j).Prime)
          (av : ∀ j, p ≠ AbcTwoNinths.Diamond.freshExtendedBase old q j)
          (u : AbcTwoNinths.Diamond.LatticeSelectedPlaneData (AbcTwoNinths.Diamond.freshExtendedBase old q) pr av),
          let V := AbcTwoNinths.Diamond.extension (AbcTwoNinths.Diamond.freshExtendedBase old q) pr av v
          let γ := AbcTwoNinths.Diamond.planeCharacter (AbcTwoNinths.Diamond.freshExtendedBase old q) pr av V u
          u.val.toAdd (.inr false) = 1 ∧ u.val.toAdd (.inr true) = -1 ∧
          AbcTwoNinths.ExteriorE2.cost weight
            (AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < AbcTwoNinths.Diamond.radius x ∧
          (∀ y : AbcTwoNinths.Diamond.LatticeSelectedPlaneData (AbcTwoNinths.Diamond.freshExtendedBase old q) pr av, AbcTwoNinths.Diamond.inRealPlane V.val u.val y.val →
            ∃! c : ℤ × ℤ, y.val = AbcTwoNinths.Diamond.along V.val u.val c) ∧ Function.Injective γ ∧
          (γ (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)) : ℚ) = AbcTwoNinths.Diamond.character old prime avoid v ∧
          AbcTwoNinths.Diamond.SlopeGood W (u.val.toAdd (.inl (.inl ()))) (v.val.toAdd (.inl ())) h (Real.log p) K := by
  obtain ⟨X, select⟩ := AbcTwoNinths.Diamond.diamondSlopeBounds hη hK W
  let startup := max 128 (16 * (1 + 6 / AbcTwoNinths.ExteriorE2.margin η)) / AbcTwoNinths.ExteriorE2.margin η
  refine ⟨max X startup, ?_⟩
  intro I _ _ p R _ _ hpR old prime avoid hi holdR v H x h
  dsimp only
  intro hx hR hRx hadm hnonzero hline hsep hroof hh hmass
  let weightSum : ℝ := ∑ i : I, Real.log (old (.inr i))
  have hxX : X ≤ x := (le_max_left X startup).trans hx
  have hxStartup : startup ≤ x := (le_max_right X startup).trans hx
  have hB : 0 < max 1 weightSum := zero_lt_one.trans_le (le_max_left _ _)
  have hWeight : weightSum ≤ max 1 weightSum := le_max_right _ _
  exact select hpR old prime avoid hi holdR v hxX hR hRx hadm hxStartup
    hnonzero hline hsep hB hWeight hroof hh hmass

end AbcTwoNinths.Diamond
