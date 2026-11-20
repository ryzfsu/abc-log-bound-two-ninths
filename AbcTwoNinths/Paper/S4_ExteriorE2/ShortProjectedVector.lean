/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PivotedGridGeometry

/-!
# Short Projected Vector

Obtains a short vector in the weighted projection from the cutoff residue image. It supports
Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.actualShortVector`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real



/--
The modulus, source-height, and support bounds give a vector in the monomial reduction
kernel whose roof projection is nonzero and has every coordinate smaller than `1 / Q` in
absolute value.
-/
theorem actualShortVector {I : Type*} [Fintype I] {η : ℚ} {σ κ : ℝ} {Q M L g : ℕ}
    {t : _root_.AbcTwoNinths.Basic.Triple} (h : _root_.AbcTwoNinths.ExteriorE2.ModulusConditions η σ κ Q t M L)
    (hκ : 0 < κ) (hQ : 0 < Q)
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime M)
    (E V : Unit ⊕ I → ℤ) (hg : 0 < g) (he : E = g • V)
    (hpiv : 0 < V (.inl ())) (hmax : ∀ j, (E j).natAbs ≤ (E (.inl ())).natAbs)
    (hgen : ∀ a ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker,
      _root_.AbcTwoNinths.Basic.roofProjection (V (.inl ())) (fun i => V (.inr i)) a = 0 → ∃ m : ℤ, a = m • V)
    (hH : t.logHeight ≤ _root_.AbcTwoNinths.ExteriorE1.height (fun j => log (q j : ℝ)) (fun j => (E j : ℝ)))
    (hweights : (∑ j, log (q j : ℝ)) ≤ 3 * t.thirdLogRadical)
    (S : Finset ℕ) (hs : S ⊆ (t.a * t.b * t.c).primeFactors) (hdim : Fintype.card I ≤ S.card)
    {rootHeight : ℝ} (hlte : (L : ℝ) * log (M : ℝ) ≤ rootHeight + log (g : ℝ))
    (hroot : (g : ℝ) * rootHeight ≤ 2 * t.logHeight) (hfloor : log (M : ℝ) ≤ rootHeight)
    (hcut : (M : ℝ) ≤ t.logHeight * exp (-σ * t.thirdLogRadical)) (hmass : κ * t.logHeight / 16 ≤ (L : ℝ) * log (M : ℝ)) :
    ∃ a ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker,
      _root_.AbcTwoNinths.Basic.roofProjection (V (.inl ())) (fun i => V (.inr i)) a ≠ 0 ∧
      ∀ i, |_root_.AbcTwoNinths.Basic.roofProjection (V (.inl ())) (fun i => V (.inr i)) a i| < 1 / (Q : ℝ) := by
  classical
  let : NeZero M := ⟨by have := h.modulus; omega⟩
  let k := (V (.inl ())).toNat
  have hk : (k : ℤ) = V (.inl ()) := Int.toNat_of_nonneg hpiv.le
  have hk' : 0 < k := by exact_mod_cast (hk.symm ▸ hpiv : 0 < (k : ℤ))
  let v := fun i => V (.inr i)
  have hV : Sum.elim (fun _ : Unit => (k : ℤ)) v = V := by
    funext j
    rcases j with ⟨⟩ | i
    · exact hk
    · rfl
  have hEg : E (.inl ()) = (g : ℤ) * k := by
    rw [he, hk]
    simp
  have hEp : 0 < E (.inl ()) := hEg ▸ (by positivity)
  have hr := _root_.AbcTwoNinths.ExteriorE2.roofMass (fun j => log (q j : ℝ)) E (.inl ())
    (fun j => log_nonneg (by exact_mod_cast (hp j).one_le)) hEp hmax hH hweights
  rw [hEg, Int.cast_mul, Int.cast_natCast, Int.cast_natCast] at hr
  have hroof : t.logHeight ≤ (k : ℝ) * ((g : ℝ) * (3 * t.thirdLogRadical)) := by linarith only [hr]
  have hb := h.grid_cost S hs
  have hb' := mul_le_mul_of_nonneg_right (show (Fintype.card I : ℝ) ≤ S.card by exact_mod_cast hdim)
    (Real.log_nonneg (by exact_mod_cast hQ : (1 : ℝ) ≤ Q))
  have hM2 : 2 ≤ M := by have := h.modulus; omega
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hM2 : (2 : ℝ) ≤ M)
  have hh := (exp_pos _).trans_le h.high.2
  have h₀ := _root_.AbcTwoNinths.ExteriorE2.shortProjectionOfCutoffImage (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc) hk' hQ v
    (by intro a ha hz; rw [hV]; exact hgen a ha (by simpa only [hk, v] using hz))
    (show 1 ≤ (g : ℝ) by exact_mod_cast hg) hh (show 0 < 3 * t.thirdLogRadical by have := h.x_pos; positivity)
    (show 0 < κ / 16 by positivity) hroof (show κ / 16 * t.logHeight ≤ _ by linarith only [hmass])
    hlte hroot (hlog2.trans hfloor) h.root_onset (_root_.AbcTwoNinths.ExteriorE2.rangeBound M q hc) hcut
    (by linarith only [hb, hb'])
  simpa only [hk, v] using h₀

end

end AbcTwoNinths.ExteriorE2
