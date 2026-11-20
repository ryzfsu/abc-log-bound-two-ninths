/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Padic Determinant Divisibility

The module proves determinant divisibility from Newton coefficient divisibility and bounds on interpolation errors.

## Main results
* `AbcTwoNinths.Basic.determinantDvdWithErrors`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open scoped BigOperators

/--
A lower bound on the total exponent for every injective row selection gives divisibility of the determinant.
-/
theorem determinantDvdOfExpansion {I J R : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (p : R) (E : ℕ) (c : I → J → R) (b : J → I → R)
    (cost : I → J → ℕ)
    (hc : ∀ i j, p ^ cost i j ∣ c i j)
    (hs : ∀ f : I → J, Function.Injective f → E ≤ ∑ i, cost i (f i)) :
    p ^ E ∣ Matrix.det (fun i => ∑ j, c i j • b j : Matrix I I R) := by
  classical
  let d := (Matrix.detRowAlternating (n := I) (R := R)).toMultilinearMap
  change p ^ E ∣ d (fun i => ∑ j, c i j • b j)
  rw [d.map_sum (fun i j => c i j • b j)]
  apply Finset.dvd_sum
  intro f _
  rw [d.map_smul_univ]
  by_cases hf : Function.Injective f
  · have hprod : p ^ (∑ i, cost i (f i)) ∣ ∏ i, c i (f i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hc i (f i)
    exact (pow_dvd_pow p (hs f hf)).trans (hprod.trans (dvd_mul_right _ _))
  · have hb : ¬ Function.Injective (b ∘ f) := fun h => hf (Function.Injective.of_comp h)
    have hz : d (fun i => b (f i)) = 0 :=
      Matrix.detRowAlternating.map_eq_zero_of_not_injective _ hb
    rw [hz, smul_zero]
    exact dvd_zero _

/-- An increasing embedding from `Fin N` to the naturals sends each index to at least its value. -/
theorem finOrderEmbBound {N : ℕ} (f : Fin N ↪o ℕ) (i : Fin N) : i.val ≤ f i := by
  have h (n : ℕ) (hn : n < N) : n ≤ f ⟨n, hn⟩ := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hn' : n < N := by omega
      have hm := f.strictMono (show (⟨n, hn'⟩ : Fin N) < ⟨n+1, hn⟩ from Nat.lt_succ_self n)
      have h₀ := ih hn'
      omega
  exact h i.val i.isLt

/-- The sum of (N) distinct naturals truncated at (N) is at least (N(N-1)/2). -/
theorem sumDistinctGe {I : Type*} [Fintype I] {f : I → ℕ} (hf : Function.Injective f)
    (N : ℕ) (hn : Fintype.card I = N) :
    N * (N - 1) / 2 ≤ ∑ i, min N (f i) := by
  classical
  let S := Finset.univ.image f
  have hS : S.card = N := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hn]
  let e := S.orderIsoOfFin hS
  have hf' : Function.Bijective (fun i : I => (⟨f i, Finset.mem_image_of_mem f
    (Finset.mem_univ i)⟩ : ↥S)) := by
    constructor
    · intro i j h; exact hf (congrArg Subtype.val h)
    · intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩
  let reindex : Fin N ≃ I := e.toEquiv.trans (Equiv.ofBijective _ hf').symm
  have he (i : Fin N) : f (reindex i) = S.orderEmbOfFin hS i := by
    exact congrArg Subtype.val ((Equiv.ofBijective _ hf').apply_symm_apply (e i))
  rw [← Equiv.sum_comp reindex, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => le_min i.isLt.le (he i ▸ _root_.AbcTwoNinths.Basic.finOrderEmbBound _ i)

/--
Row expansions with errors divisible by the matrix-size power of the base preserve the stated determinant divisibility.
-/
theorem determinantDvdWithErrors {I R : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] (p : R) (E M : ℕ) (k : I → ℕ)
    (c : I → Fin M → R) (b : Fin M → I → R) (err : Matrix I I R)
    (hc : ∀ i j, p ^ (j.val - k i) ∣ c i j)
    (he : ∀ i j, p ^ Fintype.card I ∣ err i j)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    p ^ E ∣ Matrix.det (fun i => (∑ j, c i j • b j) + err i : Matrix I I R) := by
  classical
  let N := Fintype.card I
  let d i j := Classical.choose (he i j)
  have hd i j : err i j = p ^ N * d i j := Classical.choose_spec (he i j)
  let C (i : I) : Fin M ⊕ I → R :=
    Sum.elim (c i) (fun j => if i = j then p ^ N else 0)
  let B : Fin M ⊕ I → I → R := Sum.elim b d
  let cost (i : I) : Fin M ⊕ I → ℕ := Sum.elim (fun j => j.val - k i) (fun _ => N)
  have hC i j : p ^ cost i j ∣ C i j := by
    cases j with
    | inl j => exact hc i j
    | inr j => by_cases h : i = j <;> simp [C, cost, h]
  let enc : Fin M ⊕ I → ℕ := Sum.elim Fin.val (fun j => M + N + Fintype.equivFin I j)
  have henc : Function.Injective enc := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Fin.ext h)
    · change a.val = M + N + (Fintype.equivFin I b).val at h
      omega
    · change M + N + (Fintype.equivFin I a).val = b.val at h
      omega
    · apply congrArg Sum.inr
      apply (Fintype.equivFin I).injective
      apply Fin.ext
      change M + N + (Fintype.equivFin I a).val = M + N + (Fintype.equivFin I b).val at h
      omega
  have hcost (f : I → Fin M ⊕ I) (hf : Function.Injective f) : E ≤ ∑ i, cost i (f i) := by
    have h0 := _root_.AbcTwoNinths.Basic.sumDistinctGe (henc.comp hf) N rfl
    change Fintype.card I * (Fintype.card I - 1) / 2 ≤
      ∑ i, min N (enc (f i)) at h0
    have h1 : (∑ i, min N (enc (f i))) ≤ ∑ i, (cost i (f i) + k i) := by
      apply Finset.sum_le_sum
      intro i _
      cases hh : f i with
      | inl j =>
        change min N j.val ≤ j.val - k i + k i
        exact (min_le_right ..).trans (by omega)
      | inr j =>
        change min N _ ≤ N + k i
        exact (min_le_left ..).trans (Nat.le_add_right ..)
    rw [Finset.sum_add_distrib] at h1
    omega
  have hmat : (fun i => ∑ j, C i j • B j : Matrix I I R) =
      (fun i => (∑ j, c i j • b j) + err i) := by
    funext i j
    rw [Fintype.sum_sum_type]
    simp [C, B, hd, Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [← hmat]
  exact _root_.AbcTwoNinths.Basic.determinantDvdOfExpansion p E C B cost hC hcost

end

end AbcTwoNinths.Basic
