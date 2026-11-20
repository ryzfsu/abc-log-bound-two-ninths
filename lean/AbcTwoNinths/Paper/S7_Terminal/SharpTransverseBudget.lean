/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.AdmissibleTransverseWindow
public import AbcTwoNinths.Basic.SharpScalarBudget
public import AbcTwoNinths.Paper.S7_Terminal.DiamondDeterminantContradiction
public import AbcTwoNinths.Paper.S7_Terminal.DirichletBasis

/-!
# Sharp Transverse Budget

The module combines denominator and height inequalities into a contradiction for a short transverse basis. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.sharpBudget`
* `AbcTwoNinths.Terminal.goodBasis`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section




/-- The radius. This is used in Section 7 of the paper. -/
noncomputable def radius (θ h t ℓ : ℝ) : ℝ := (3/2 : ℝ) * (1 + θ) * h * (t / ℓ)

/--
The denominator cutoff for the short-basis argument is one plus the natural ceiling of four divided by three times the relative cell width and the lower transverse ratio. This is used in Section 7 of the paper.
-/
noncomputable def goodDenominator (Z b : ℝ) : ℕ := ⌈4 / (3 * Z * b)⌉₊ + 1

/--
Every positive denominator below the cutoff has weighted approximation error at least the prescribed slope threshold. This is used in Section 7 of the paper.
-/
def Good (Z ℓ h c : ℝ) (W : ℕ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → Q < W → ∀ P : ℤ, 4 * ℓ / (3 * Z) ≤ |(Q : ℝ) * c - P| * h

/-- The sharp budget. This is used in Section 7 of the paper. -/
structure SharpBudget (h t ℓ θ Z : ℝ) (J m K : ℕ) : Prop where
  h_pos : 0 < h
  t_pos : 0 < t
  delta_pos : 0 < Z * _root_.AbcTwoNinths.Terminal.radius θ h t ℓ
  delta_le_radius : Z * _root_.AbcTwoNinths.Terminal.radius θ h t ℓ ≤ _root_.AbcTwoNinths.Terminal.radius θ h t ℓ
  diameter : 2 * _root_.AbcTwoNinths.Terminal.radius θ h t ℓ < h
  rows_pos : 0 < K
  depth : 4 * K ≤ 3 * m
  count : ((2*K-1 : ℕ) : ℝ) ≤ 2/(h*t) * (_root_.AbcTwoNinths.Terminal.radius θ h t ℓ-Z*_root_.AbcTwoNinths.Terminal.radius θ h t ℓ)^2
  wide : let δ := Z * _root_.AbcTwoNinths.Terminal.radius θ h t ℓ
    4 * t * h ≤ δ^2
  budget : let ρ := _root_.AbcTwoNinths.Terminal.radius θ h t ℓ
    let δ := Z * ρ
    let S := ρ + δ
    2/(h*t) * (S*(S+δ)^2 - S^3/3 + S^3/(2*J) + δ*S^2) +
      Real.log ((2*K).factorial : ℝ) + (2*K : ℝ) * ((S/t + K) * Real.log 2) <
      (2/9 : ℝ) * (2*K : ℝ)^2 * ℓ

private theorem sharpArchimedean {h t ρ Z : ℝ} {J : ℕ}
    (hh : 0 < h) (ht : 0 < t) (hρ : 0 < ρ) (hZ : 0 ≤ Z) :
    let N := 2/(h*t)*ρ^2
    let δ := Z*ρ
    let S := ρ+δ
    2/(h*t) * (S*(S+δ)^2 - S^3/3 + S^3/(2*J) + δ*S^2) ≤
      ((1+Z)^3*(2/3+3*Z+Z^2+1/(2*J))) * (N*ρ) := by
  dsimp only
  set δ := Z * ρ with hd
  set S := ρ + δ with hs
  have hδ : 0 ≤ δ := by positivity
  have hS : 0 ≤ S := by positivity
  have hδS : δ ≤ Z*S := by rw [hs, mul_add, ← hd]; exact le_add_of_nonneg_right (by positivity)
  have hSS : S + δ ≤ (1+Z)*S := by linarith only [hδS, show (1+Z)*S = S+Z*S by ring]
  have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ S + δ by positivity) hSS 2) hS
  have h2 := mul_le_mul_of_nonneg_right hδS (sq_nonneg S)
  calc
    _ ≤ 2/(h*t) * (S*((1+Z)*S)^2 - S^3/3 + S^3/(2*J) + (Z*S)*S^2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) (by positivity)
    _ = _ := by rw [hs, hd]; ring

/--
A transverse window with strict depth slack admits uniform parameters and an integer row count satisfying the diamond budget. This is used in Section 7 of the paper.
-/
theorem sharpBudget {a b κ : ℝ} (hb : 0 < b) (ha : 0 < a) (hκ : 0 ≤ κ)
    (hgap : 3*a < 1-2*κ) :
    ∃ θ Z : ℝ, ∃ J : ℕ, ∃ X : ℝ,
      0 < θ ∧ θ < 1 ∧ 0 < Z ∧ Z < 1 ∧ 0 < J ∧ 1 ≤ X ∧
      ∀ {h t ℓ H : ℝ} {m : ℕ}, X ≤ ℓ → X ≤ h/ℓ → h ≤ H →
        (1-2*κ)*H ≤ m*ℓ → b*ℓ ≤ t → t ≤ a*ℓ →
        ∃ K : ℕ, _root_.AbcTwoNinths.Terminal.SharpBudget h t ℓ θ Z J m K := by
  obtain ⟨θ, Z, J, hθ, hθ1, hZ, hZ1, hJ, hdepth, hs⟩ := _root_.AbcTwoNinths.Terminal.sharpSlack ha hgap
  let α := (3/2 : ℝ)*(1+θ)
  let f := (1-Z)^2
  let F := (1+Z)^3*(2/3+3*Z+Z^2+1/(2*J))
  let D := (3/2 : ℝ)*(1-2*κ) - 2*α^2*a
  have hα : 0 < α := by dsimp [α]; positivity
  have hD : 0 < D := by dsimp [D, α]; nlinarith only [hdepth]
  have hf : 0 < f := sq_pos_of_pos (sub_pos.mpr hZ1)
  have hf1 : f ≤ 1 := by
    simpa [f] using pow_le_pow_left₀ (show 0 ≤ 1-Z by linarith) (show 1-Z ≤ 1 by linarith) 2
  have hF : F < (2/3 : ℝ)*(1+θ)*f^2 := by
    dsimp [F, f]
    linear_combination (2/3 : ℝ) * hs
  obtain ⟨Y, hY, hy⟩ := _root_.AbcTwoNinths.Basic.sharpBudgetOnset hf hf1 hθ hθ1.le hb hF
  let C := 2*α^2*b
  have hC : 0 < C := by dsimp [C]; positivity
  let X := max Y (max (Y/(C*f)) (max (1/D) (4/(Z^2*α^2*b))))
  have hYX : Y ≤ X := le_max_left _ _
  have hX : 1 ≤ X := hY.trans hYX
  refine ⟨θ, Z, J, X, hθ, hθ1, hZ, hZ1, hJ, hX, ?_⟩
  intro h t ℓ H m hℓX hnX hhH hm htlow hthi
  have hℓ : 0 < ℓ := zero_lt_one.trans_le (hX.trans hℓX)
  let r := h/ℓ
  let τ := t/ℓ
  have hr : 0 < r := zero_lt_one.trans_le (hX.trans hnX)
  have hh : 0 < h := (div_pos_iff.mp hr).resolve_right (fun h => (not_lt_of_ge hℓ.le) h.2) |>.1
  have ht : 0 < t := (mul_pos hb hℓ).trans_le htlow
  have hbτ : b ≤ τ := (le_div_iff₀ hℓ).2 (by simpa [mul_comm] using htlow)
  have hτa : τ ≤ a := (div_le_iff₀ hℓ).2 hthi
  let ρ := _root_.AbcTwoNinths.Terminal.radius θ h t ℓ
  let δ := Z*ρ
  let S := ρ+δ
  let N := 2/(h*t)*ρ^2
  have hρeq : ρ = α*h*τ := rfl
  have hρ : 0 < ρ := by rw [hρeq]; exact mul_pos (mul_pos hα hh) (hb.trans_le hbτ)
  have hδ : 0 < δ := mul_pos hZ hρ
  have hδρ : δ ≤ ρ := by dsimp [δ]; nlinarith only [mul_nonneg (sub_nonneg.mpr hZ1.le) hρ.le]
  have hN : N = 2*α^2*r*τ := by
    dsimp [N, r, τ]
    rw [hρeq]
    dsimp [τ]
    field_simp
  have hNℓ : N*ℓ = 3*(1+θ)*ρ := by
    rw [hN, hρeq]
    dsimp [r, α]
    field_simp
  have hNlow : C*r ≤ N := by
    rw [hN]
    dsimp [C]
    nlinarith only [mul_le_mul_of_nonneg_left hbτ (show 0 ≤ 2*α^2*r by positivity)]
  have hNhi : N ≤ 2*α^2*a*r := by
    rw [hN]
    nlinarith only [mul_le_mul_of_nonneg_left hτa (show 0 ≤ 2*α^2*r by positivity)]
  have hscale : Y/(C*f) ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hnX)
  have hround : Y ≤ N*f := ((div_le_iff₀ (mul_pos hC hf)).1 hscale).trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hNlow hf.le])
  have hYN : Y ≤ N := by
    have hN0 : 0 ≤ N := by dsimp [N]; positivity
    linarith only [hround, mul_le_mul_of_nonneg_left hf1 hN0]
  have hN1 : 1 ≤ N := hY.trans hYN
  have hDr : 1 ≤ D*r := by
    have hdX : 1/D ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hnX))
    simpa [mul_comm] using (div_le_iff₀ hD).mp hdX
  have hmd : (3/2 : ℝ)*(1-2*κ)*r ≤ (3/2 : ℝ)*m := by
    have hpos : 0 ≤ 1-2*κ := by linarith only [ha, hgap]
    have hmul := (mul_le_mul_of_nonneg_left hhH hpos).trans hm
    have h' : (1-2*κ)*r ≤ m := by
      apply (mul_le_mul_iff_left₀ hℓ).mp
      calc
        (1-2*κ)*r*ℓ = (1-2*κ)*h := by dsimp [r]; rw [mul_assoc, div_mul_cancel₀ _ hℓ.ne']
        _ ≤ m*ℓ := hmul
    linarith only [h']
  have hdepth' : N*f+1 ≤ (3/2 : ℝ)*m := by
    have hNf : N*f ≤ N := by nlinarith only [mul_le_mul_of_nonneg_left hf1 (show 0 ≤ N by linarith)]
    dsimp [D] at hDr
    nlinarith only [hDr, hmd, hNhi, hNf]
  obtain ⟨K, hK, hKr, hKr', hKm⟩ := _root_.AbcTwoNinths.Terminal.sharpRows (hY.trans hround) hdepth' (le_refl _)
  have hKrN : (2*K : ℝ) ≤ 2*N := by
    linarith only [hKr, hN1, mul_le_mul_of_nonneg_left hf1 (show 0 ≤ N by linarith)]
  have hdiam : 2*ρ < h := by
    have hmain : 2*α*a < 1 := by
      have hθsq := mul_nonneg hθ.le (show 0 ≤ 1+θ by positivity)
      dsimp [α]
      nlinarith only [hdepth, hκ, mul_nonneg ha.le hθsq]
    rw [hρeq]
    have hprod := mul_lt_mul_of_pos_right
      ((mul_le_mul_of_nonneg_left hτa (show 0 ≤ 2*α by positivity)).trans_lt hmain) hh
    nlinarith only [hprod]
  have hcount : ((2*K-1 : ℕ) : ℝ) ≤ 2/(h*t)*(ρ-δ)^2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    convert hKr using 1
    dsimp [N, f, δ]
    ring
  have hwide : 4*t*h ≤ δ^2 := by
    have hcut : 4/(Z^2*α^2*b) ≤ r :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hnX))
    have h4r := (div_le_iff₀ (show 0 < Z^2*α^2*b by positivity)).mp hcut
    have h4τ : 4 ≤ Z^2*α^2*r*τ := by
      have hbt := mul_le_mul_of_nonneg_left hbτ (show 0 ≤ Z^2*α^2*r by positivity)
      nlinarith only [h4r, hbt]
    have hp := mul_le_mul_of_nonneg_right h4τ (show 0 ≤ t*h by positivity)
    have hi : Z^2*α^2*r*τ*(t*h) = δ^2 := by
      dsimp [δ]
      rw [hρeq]
      dsimp [r, τ]
      ring
    linarith only [hp, hi]
  have hS : S ≤ 2*ρ := by dsimp [S]; linarith only [hδρ]
  have hSp : 0 ≤ S := add_nonneg hρ.le hδ.le
  have hscalar := hy hYN (hYX.trans hℓX) hρ hNℓ hKrN hKr'.le hS hSp htlow
  have harch : 2/(h*t)*(S*(S+δ)^2-S^3/3+S^3/(2*J)+δ*S^2) ≤ F*(N*ρ) :=
    sharpArchimedean hh ht hρ hZ.le (J := J)
  refine ⟨K, hh, ht, hδ, hδρ, hdiam, hK, hKm, hcount, hwide, ?_⟩
  change 2/(h*t)*(S*(S+δ)^2-S^3/3+S^3/(2*J)+δ*S^2) +
    Real.log ((2*K).factorial : ℝ) + (2*K : ℝ)*((S/t+K)*Real.log 2) < _
  linarith only [harch, hscalar]

/--
Beyond a uniform height-ratio threshold, slope separation and sufficient diamond width give two short unimodular sites. This is used in Section 7 of the paper.
-/
theorem goodBasis {θ Z b : ℝ} (hθ : 0 < θ) (hZ : 0 < Z) (hb : 0 < b) :
    ∃ X : ℝ, ∀ {h t ℓ c : ℝ}, 0 < ℓ → 0 < h → b*ℓ ≤ t → X ≤ h/ℓ →
      4*t*h ≤ (Z*_root_.AbcTwoNinths.Terminal.radius θ h t ℓ)^2 → _root_.AbcTwoNinths.Terminal.Good Z ℓ h c (_root_.AbcTwoNinths.Terminal.goodDenominator Z b) →
      ∃ u v : _root_.AbcTwoNinths.Basic.Sites, u ≠ 0 ∧ |(u.1 : ℝ)*v.2 - (v.1 : ℝ)*u.2| = 1 ∧
        _root_.AbcTwoNinths.Terminal.siteHeight c h t u ≤ Z*_root_.AbcTwoNinths.Terminal.radius θ h t ℓ ∧ _root_.AbcTwoNinths.Terminal.siteHeight c h t v ≤ Z*_root_.AbcTwoNinths.Terminal.radius θ h t ℓ := by
  let W := _root_.AbcTwoNinths.Terminal.goodDenominator Z b
  let α := (3/2 : ℝ)*(1+θ)
  have hα : 0 < α := by dsimp [α]; positivity
  have hw : 2 ≤ W := by
    have hceil : (0 : ℕ) < ⌈4 / (3*Z*b)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    dsimp [W, _root_.AbcTwoNinths.Terminal.goodDenominator]
    omega
  have hWb : 4/(3*Z*b) ≤ (W : ℝ) := by
    have hc := Nat.le_ceil (4 / (3*Z*b))
    dsimp [W, _root_.AbcTwoNinths.Terminal.goodDenominator]
    push_cast
    linarith only [hc]
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
  refine ⟨2*(W : ℝ)/(Z*α), ?_⟩
  intro h t ℓ c hℓ hh htlow hx hwide hgood
  have ht : 0 < t := (mul_pos hb hℓ).trans_le htlow
  let δ := Z*_root_.AbcTwoNinths.Terminal.radius θ h t ℓ
  have hδ : 0 < δ := by unfold δ _root_.AbcTwoNinths.Terminal.radius; positivity
  let Qs := ⌊δ/(2*t)⌋₊
  have heq : δ/(2*t) = Z*α*(h/ℓ)/2 := by dsimp [δ, _root_.AbcTwoNinths.Terminal.radius, α]; field_simp
  have hwq : W ≤ Qs := by
    apply Nat.le_floor
    rw [heq]
    have hp := (div_le_iff₀ (mul_pos hZ hα)).1 hx
    nlinarith only [hp]
  have hQs : (Qs : ℝ) ≤ δ/(2*t) := Nat.floor_le (by positivity)
  have hQs' : δ/(2*t) < (Qs : ℝ)+1 := Nat.lt_floor_add_one _
  have hcut : h/((Qs : ℝ)+1) < 2*t*h/δ := by
    have hinv := (one_div_lt_one_div_of_lt (show 0 < δ/(2*t) by positivity) hQs')
    have hprod := mul_lt_mul_of_pos_left hinv hh
    convert hprod using 1 <;> field_simp
  have hgood' : ∀ Q : ℕ, 1 ≤ Q → Q < W → ∀ P : ℤ,
      1 / ((Qs : ℝ)+1) < |(Q : ℝ)*c-P| := by
    intro Q hQ hQW P
    have hα' : (3/2 : ℝ) ≤ α := by dsimp [α]; linarith only [hθ]
    have hd : 0 < Z*α := mul_pos hZ hα
    have hd' : 0 < (3/2 : ℝ)*Z := by positivity
    have hroof : 2*t*h/δ ≤ 4*ℓ/(3*Z) := by
      calc
        _ = 2*ℓ/(Z*α) := by dsimp [δ, _root_.AbcTwoNinths.Terminal.radius, α]; field_simp
        _ ≤ 2*ℓ/((3/2)*Z) := div_le_div_of_nonneg_left (by positivity) hd'
          (by nlinarith only [mul_le_mul_of_nonneg_right hα' hZ.le])
        _ = _ := by ring
    have hz := (hcut.trans_le hroof).trans_le (hgood Q hQ hQW P)
    apply (mul_lt_mul_iff_left₀ hh).mp
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm h] using hz
  obtain ⟨P₁, P₂, Q₁, Q₂, hW₁, h₁s, h₂, h₂₁, he₁, he₂, hdet⟩ :=
    _root_.AbcTwoNinths.Terminal.dirichletBasis c hw hwq hgood'
  let u : _root_.AbcTwoNinths.Basic.Sites := (-P₁, (Q₁ : ℤ))
  let v : _root_.AbcTwoNinths.Basic.Sites := (-P₂, (Q₂ : ℤ))
  have hu : u ≠ 0 := by
    intro huz
    have hz : (Q₁ : ℤ) = 0 := congrArg Prod.snd huz
    omega
  have hq₁ : (W : ℝ) ≤ Q₁ := by exact_mod_cast hW₁
  have hq₁s : (Q₁ : ℝ) ≤ Qs := by exact_mod_cast h₁s
  have hq₂s : (Q₂ : ℝ) ≤ Qs := by exact_mod_cast (le_trans h₂₁.le h₁s)
  have htbound (Q : ℕ) (hq : (Q : ℝ) ≤ Qs) : (Q : ℝ)*t ≤ δ/2 := by
    have hq' := (le_div_iff₀ (show 0 < 2*t by positivity)).1 (hq.trans hQs)
    nlinarith only [hq']
  have hfirst : 2*t*h/δ ≤ δ/2 := by
    apply (div_le_iff₀ hδ).2
    nlinarith only [hwide]
  have hsecond : h/(W : ℝ) ≤ δ/2 := by
    have hl : 1 ≤ (1+θ)*((t/ℓ)/b) := by
      have hbτ : b ≤ t/ℓ := (le_div_iff₀ hℓ).2 (by simpa [mul_comm] using htlow)
      have hbt : 1 ≤ (t/ℓ)/b := (le_div_iff₀ hb).2 (by simpa using hbτ)
      exact one_le_mul_of_one_le_of_one_le (by linarith only [hθ]) hbt
    have hδb : δ*(4/(3*Z*b)) = 2*h*((1+θ)*((t/ℓ)/b)) := by
      unfold δ _root_.AbcTwoNinths.Terminal.radius
      field_simp
      ring
    have hb₁ := mul_le_mul_of_nonneg_left hWb hδ.le
    have hb₂ := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*h by positivity)
    apply (div_le_iff₀ hWpos).2
    nlinarith only [hδb, hb₁, hb₂]
  have hdu : |(u.1 : ℝ)*v.2 - (v.1 : ℝ)*u.2| = 1 := by
    have he : (u.1 : ℝ)*v.2 - (v.1 : ℝ)*u.2 =
        (((Q₁ : ℤ)*P₂ - P₁*Q₂ : ℤ) : ℝ) := by
      dsimp [u, v]
      push_cast
      ring
    rw [he]
    rcases hdet with hp | hm
    · simp [hp]
    · simp [hm]
  refine ⟨u, v, hu, hdu, ?_, ?_⟩
  · have hu₁ := mul_le_mul_of_nonneg_right he₁ hh.le
    have hg : |(u.1 : ℝ) + c*(u.2 : ℝ)| * h ≤ h/((Qs : ℝ)+1) := by
      simpa only [u, Int.cast_neg, Int.cast_natCast, sub_eq_neg_add, mul_comm c, one_div,
        div_eq_mul_inv, mul_comm h, one_mul] using hu₁
    have hv := htbound Q₁ hq₁s
    have hz : |(u.2 : ℝ)| * t ≤ δ/2 := by simpa [u, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ Q₁)] using hv
    change |(u.1 : ℝ) + c*(u.2 : ℝ)| * h + |(u.2 : ℝ)| * t ≤ δ
    linarith only [hg, hz, hcut, hfirst]
  · have hv₁ := mul_le_mul_of_nonneg_right he₂ hh.le
    have hg : |(v.1 : ℝ) + c*(v.2 : ℝ)| * h ≤ h/(Q₁ : ℝ) := by
      simpa only [v, Int.cast_neg, Int.cast_natCast, sub_eq_neg_add, mul_comm c, one_div,
        div_eq_mul_inv, mul_comm h, one_mul] using hv₁
    have hv := htbound Q₂ hq₂s
    have hz : |(v.2 : ℝ)| * t ≤ δ/2 := by simpa [v, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ Q₂)] using hv
    have hq := div_le_div_of_nonneg_left hh.le hWpos hq₁
    change |(v.1 : ℝ) + c*(v.2 : ℝ)| * h + |(v.2 : ℝ)| * t ≤ δ
    linarith only [hg, hz, hq, hsecond]




/--
In the transverse window, a slope-separated injective principal plane character with the axial depth and site-height bounds yields a contradiction.
-/
theorem fineConflict {a b κ : ℝ} (hb : 0 < b) (ha : 0 < a) (hκ : 0 ≤ κ)
    (hgap : 3*a < 1-2*κ) :
    ∃ Z X : ℝ, 0 < Z ∧ Z < 1 ∧ 1 ≤ X ∧
      ∀ {p m : ℕ} [Fact p.Prime] {c h t H : ℝ},
        let ℓ := Real.log (p : ℝ)
        X ≤ ℓ → X ≤ h/ℓ → h ≤ H → (1-2*κ)*H ≤ m*ℓ →
        b*ℓ ≤ t → t ≤ a*ℓ → _root_.AbcTwoNinths.Terminal.Good Z ℓ h c (_root_.AbcTwoNinths.Terminal.goodDenominator Z b) →
        ∀ γ : _root_.AbcTwoNinths.Terminal.PlaneCharacter,
          Function.Injective (_root_.AbcTwoNinths.Terminal.value γ) →
          (∀ s : _root_.AbcTwoNinths.Terminal.Site, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s)) →
          (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1) →
          (∀ s, Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ s) : ℝ) ≤ _root_.AbcTwoNinths.Terminal.siteHeight c h t s) → False := by
  obtain ⟨θ, Z, J, Xs, hθ, _, hZ, hZ1, hJ, hXs, hs⟩ := _root_.AbcTwoNinths.Terminal.sharpBudget hb ha hκ hgap
  obtain ⟨Xb, hbas⟩ := _root_.AbcTwoNinths.Terminal.goodBasis hθ hZ hb
  refine ⟨Z, max Xs Xb, hZ, hZ1, hXs.trans (le_max_left _ _), ?_⟩
  intro p m hp c h t H ℓ hℓ hx hhH hm htb hta hgood γ hinj hprincipal hdepth hheight
  have hℓs := (le_max_left Xs Xb).trans hℓ
  have hxs := (le_max_left Xs Xb).trans hx
  have hxb := (le_max_right Xs Xb).trans hx
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le (hXs.trans hℓs)
  obtain ⟨K, hK⟩ := hs hℓs hxs hhH hm htb hta
  obtain ⟨u, v, hu0, huv, hu, hv⟩ := hbas hℓ0 hK.h_pos htb hxb hK.wide hgood
  have hshift : _root_.AbcTwoNinths.Terminal.value γ u ≠ 1 := by
    intro heq
    have hz : _root_.AbcTwoNinths.Terminal.value γ (0 : _root_.AbcTwoNinths.Terminal.Site) = 1 := by simp [_root_.AbcTwoNinths.Terminal.value]
    exact hu0 (hinj (heq.trans hz.symm))
  exact _root_.AbcTwoNinths.Terminal.diamondEngine γ hprincipal hdepth hK.h_pos hK.t_pos hK.delta_pos
    hK.delta_le_radius hK.diameter u v huv hu hv hshift hheight hK.rows_pos
    hK.depth hJ hK.count hK.budget

end

end AbcTwoNinths.Terminal
