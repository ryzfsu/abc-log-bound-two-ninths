/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.SharpTransverseBudget
public import AbcTwoNinths.Paper.S7_Terminal.TransverseHeightWindow
public import AbcTwoNinths.Paper.S7_Terminal.TransverseHeight
public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePair

/-!
# Shell Contradiction

The module excludes the shell case by applying the upper and lower transverse height inequalities together. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.fineShellConflict`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section







/--
Beyond common thresholds for the prime logarithm and the height ratio, the slope and depth bounds exclude a fresh pair on the selected shell. This is used in Section 7 of the paper.
-/
theorem fineShellConflict {η : ℚ} {κ : ℝ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) :
    let b := _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)/2
    ∃ Z X : ℝ, 0 < Z ∧ Z < 1 ∧ 1 ≤ X ∧
      ∀ {I : Type*} [Fintype I] [DecidableEq I] {p R m : ℕ} [Fact p.Prime] [Fact (2 < p)]
        (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
        (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (q : ℕ × ℕ)
        (pr : ∀ i, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q i).Prime) (av : ∀ i, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old q i)
        (_inj : Function.Injective (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q))
        (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av) {H x : ℝ} {z : ℚ},
        let ℓ := Real.log (p : ℝ)
        let h := Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax z : ℝ)
        let γ := _root_.AbcTwoNinths.Diamond.planeCharacter (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av
          (_root_.AbcTwoNinths.Diamond.extension (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av v) u
        _root_.AbcTwoNinths.ExteriorE2.Admissible p H (η : ℝ) x → Real.exp (4 / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)) ≤ x →
        _root_.AbcTwoNinths.ExteriorE2.Fresh (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)) x) R q.1 →
        _root_.AbcTwoNinths.ExteriorE2.Fresh (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)) x) R q.2 →
        (v.val.toAdd (.inl ()) ≠ 0) →
        u.val.toAdd (.inr false) = 1 → u.val.toAdd (.inr true) = -1 →
        _root_.AbcTwoNinths.ExteriorE2.cost (fun i : I => Real.log (old (.inr i) : ℝ))
          (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < 2*x/Real.log x →
        Function.Injective γ → _root_.AbcTwoNinths.Terminal.value γ (1, 0) = z →
        h ≤ H → (1-2*κ)*H ≤ m*ℓ → (m : ℤ) ≤ padicValRat p (z - 1) →
        X ≤ ℓ → X ≤ h/ℓ →
        _root_.AbcTwoNinths.Diamond.SlopeGood (_root_.AbcTwoNinths.Terminal.goodDenominator Z b) (u.val.toAdd (.inl (.inl ())))
          (v.val.toAdd (.inl ())) h ℓ (4/(3*Z)) → False := by
  intro b
  let a := 3*(η : ℝ) + _root_.AbcTwoNinths.ExteriorE2.gap (η : ℝ)/2
  obtain ⟨hb, hgap⟩ := _root_.AbcTwoNinths.Terminal.transverseConstants hη hκ
  have hη0 : (0 : ℝ) < η := by exact_mod_cast hη.1
  have hη1 : (η : ℝ) < 1/9 := by simpa using (Rat.cast_lt (K := ℝ)).mpr hη.2
  have ha : 0 < a := by dsimp [a]; unfold _root_.AbcTwoNinths.ExteriorE2.gap; linarith only [hη0, hη1]
  have hκ0 : 0 ≤ κ := hκ.1.le
  obtain ⟨Z, X, hZ, hZ1, hX, conflict⟩ := _root_.AbcTwoNinths.Terminal.fineConflict hb ha hκ0 hgap
  refine ⟨Z, X, hZ, hZ1, hX, ?_⟩
  intro I _ _ p R m _ _ old prime avoid v q pr av inj u H x z ℓ h γ
    adm hx hf ht hv hu₁ hu₂ hc hinj hγ hh hm hdepth hℓ hxratio hslope
  let base := _root_.AbcTwoNinths.Diamond.freshExtendedBase old q
  let qcost := _root_.AbcTwoNinths.ExteriorE2.cost (fun i : I => Real.log (old (.inr i) : ℝ))
    (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i)))
  let t := qcost + Real.log ((max q.1 q.2 : ℕ) : ℝ)
  let c := (u.val.toAdd (.inl (.inl ())) : ℝ) / v.val.toAdd (.inl ())
  have hcost : 0 ≤ qcost := by
    unfold qcost _root_.AbcTwoNinths.ExteriorE2.cost
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (Real.log_nonneg (by exact_mod_cast (prime (.inr i)).one_le)) (abs_nonneg _))
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le (hX.trans hℓ)
  obtain ⟨htb, hta⟩ := _root_.AbcTwoNinths.Terminal.shellWindow adm hx hf ht hcost hc
  have hbt : b*ℓ ≤ t := (le_div_iff₀ hℓ0).1 htb.le
  have hat : t ≤ a*ℓ := (div_le_iff₀ hℓ0).1 hta.le
  have hgood : _root_.AbcTwoNinths.Terminal.Good Z ℓ h c (_root_.AbcTwoNinths.Terminal.goodDenominator Z b) := by
    intro Q hQ hW P
    have hs := hslope Q (by omega) hW.le P
    simpa [c, div_mul_eq_mul_div, mul_comm (4 : ℝ) ℓ] using hs
  have hval : Function.Injective (_root_.AbcTwoNinths.Terminal.value γ) := by
    intro s s' heq
    exact Multiplicative.ofAdd.injective (hinj (Units.ext heq))
  have hp s : _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Terminal.value γ s) :=
    _root_.AbcTwoNinths.Diamond.planeCharacterPrincipal base pr av (_root_.AbcTwoNinths.Diamond.extension base pr av v) u s
  have hd : (m : ℤ) ≤ padicValRat p (_root_.AbcTwoNinths.Terminal.value γ (1, 0) - 1) := by simpa [hγ] using hdepth
  have hheight s : Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ s) : ℝ) ≤ _root_.AbcTwoNinths.Terminal.siteHeight c h t s := by
    have hh' := _root_.AbcTwoNinths.Terminal.freshHeightBound base pr av inj v u hv hu₁ hu₂ s
    change Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ s) : ℝ) ≤
      |(s.1 : ℝ) + c*s.2| * Real.log (_root_.AbcTwoNinths.Terminal.rowHeightMax (_root_.AbcTwoNinths.Terminal.value γ (1, 0)) : ℝ) +
        |(s.2 : ℝ)| * t at hh'
    simpa only [_root_.AbcTwoNinths.Terminal.siteHeight, hγ] using hh'
  exact conflict hℓ hxratio hh hm hbt hat hgood γ hval hp hd hheight

end

end AbcTwoNinths.Terminal
