/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.ShearedDiamond
public import AbcTwoNinths.Paper.S7_Terminal.DiamondLabelInjectivity
public import AbcTwoNinths.Paper.S7_Terminal.DeterminantContradiction

/-!
# Diamond Determinant Contradiction

The module applies the determinant contradiction to lattice sites in the diamond using height subadditivity. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.diamondEngine`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section




/-- The sheared site height with nonnegative weights is subadditive. -/
theorem siteHeightAddLe (c h t : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t) (a b : _root_.AbcTwoNinths.Basic.Sites) :
    _root_.AbcTwoNinths.Terminal.siteHeight c h t (a+b) ≤ _root_.AbcTwoNinths.Terminal.siteHeight c h t a + _root_.AbcTwoNinths.Terminal.siteHeight c h t b := by
  simp only [_root_.AbcTwoNinths.Terminal.siteHeight, Prod.fst_add, Prod.snd_add, Int.cast_add]
  rw [show (a.1 : ℝ) + b.1 + c*((a.2 : ℝ)+b.2) =
    ((a.1 : ℝ)+c*a.2)+((b.1 : ℝ)+c*b.2) by ring]
  linarith [mul_le_mul_of_nonneg_right (abs_add_le ((a.1 : ℝ)+c*a.2) ((b.1 : ℝ)+c*b.2)) hh,
    mul_le_mul_of_nonneg_right (abs_add_le (a.2 : ℝ) b.2) ht]

/--
A short unimodular diamond basis and a nontrivial shift contradict the strict determinant budget under the stated count and valuation hypotheses. This is used in Section 7 of the paper.
-/
theorem diamondEngine {p K m J : ℕ} [Fact p.Prime]
    (γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter) (hp : ∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s))
    (hm : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1))
    {c h t δ ρ : ℝ} (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ : 2*ρ < h) (u v : _root_.AbcTwoNinths.Basic.Sites)
    (hd : |(u.1 : ℝ) * v.2 - (v.1 : ℝ) * u.2| = 1)
    (hu : _root_.AbcTwoNinths.Terminal.siteHeight c h t u ≤ δ) (hv : _root_.AbcTwoNinths.Terminal.siteHeight c h t v ≤ δ)
    (hshift : _root_.AbcTwoNinths.Terminal.value γ u ≠ 1)
    (HB : ∀ s, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ s) : ℝ) ≤ _root_.AbcTwoNinths.Terminal.siteHeight c h t s)
    (hK : 0 < K) (hKm : 4*K ≤ 3*m) (hJ : 0 < J)
    (hcount : ((2*K-1 : ℕ) : ℝ) ≤ 2/(h*t) * (ρ-δ)^2)
    (budget : let S := ρ+δ
      2/(h*t) * (S*(S+δ)^2 - S^3/3 + S^3/(2*J) + δ*S^2) +
        Real.log ((2*K).factorial : ℝ) + (2*K : ℝ) * ((S/t + K) * Real.log 2) <
        (2/9 : ℝ) * (2*K : ℝ)^2 * Real.log (p : ℝ)) : False := by
  classical
  let ball (r : ℝ) := _root_.AbcTwoNinths.Terminal.diamondSites (r := r) c u v hh ht hd
  have hc : (_root_.AbcTwoNinths.Terminal.siteHeight c h t u + _root_.AbcTwoNinths.Terminal.siteHeight c h t v) / 2 ≤ δ := by linarith
  have hs (r : ℝ) (hr : 0 ≤ r) := _root_.AbcTwoNinths.Terminal.diamondSitesSpec c u v hh ht hr hδ hd hc
  have hht (r : ℝ) (s : _root_.AbcTwoNinths.Basic.Sites) (hmem : s ∈ ball r) :
      _root_.AbcTwoNinths.Terminal.siteHeight c h t s ≤ r := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
    rw [← _root_.AbcTwoNinths.Terminal.diamondSiteMap c u v i hh.le ht.le]
    exact (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd i).mp hi
  refine _root_.AbcTwoNinths.Terminal.engineFalse γ hp hm u hshift ball (_root_.AbcTwoNinths.Terminal.siteHeight c h t) (by positivity)
    hδ hδρ ht ?_ hht ?_ HB ?_ ?_ ?_ ?_ hK hKm hJ hcount budget
  · intro r s hrs j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hi' := (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd i).mp hi
    exact Finset.mem_image.mpr ⟨i, (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd i).mpr
      (hi'.trans hrs), rfl⟩
  · intro s
    unfold _root_.AbcTwoNinths.Terminal.siteHeight
    linarith [mul_nonneg (abs_nonneg ((s.1 : ℝ)+c*s.2)) hh.le]
  · exact fun r hr => (hs r hr).1
  · exact fun r hr => (hs r hr).2.1
  · intro s hm
    have hsum := (_root_.AbcTwoNinths.Terminal.siteHeightAddLe c h t hh.le ht.le s u).trans (add_le_add (hht _ _ hm) hu)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have he : _root_.AbcTwoNinths.Terminal.siteMap u v (i + (1,0)) = _root_.AbcTwoNinths.Terminal.siteMap u v i + u := by
      ext <;> simp [_root_.AbcTwoNinths.Terminal.siteMap, add_mul] <;> ring
    refine Finset.mem_image.mpr ⟨i + (1,0), ?_, he⟩
    apply (_root_.AbcTwoNinths.Terminal.memDiamondBall c (_root_.AbcTwoNinths.Basic.lift u) (_root_.AbcTwoNinths.Basic.lift v) hh ht hd _).mpr
    rw [_root_.AbcTwoNinths.Terminal.diamondSiteMap c u v _ hh.le ht.le, he]
    exact hsum
  · exact _root_.AbcTwoNinths.Terminal.ballLabelsInjective hh ht.le hρ (fun s hm => hht _ s hm)

end

end AbcTwoNinths.Terminal
