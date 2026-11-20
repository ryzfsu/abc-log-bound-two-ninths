/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlapCounting
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPlaneData

/-!
# Fresh Torus Witness

The module constructs a fresh-prime torus witness and checks the extended prime base and its residues. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.freshTorusWitness`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section





private theorem residueFreshEq {p R : ℕ} [Fact p.Prime] {S : ℝ}
    (hpR : p ∣ R) {q : ℕ} (hq : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q)
    {ι : Type*} (base : ι → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (j : ι) (hj : base j = q) :
    QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (_root_.AbcTwoNinths.ExteriorE2.residueUnit base prime avoid j) = _root_.AbcTwoNinths.Diamond.residuePrimeLabel p q := by
  obtain ⟨h, he⟩ := _root_.AbcTwoNinths.Diamond.freshPrimeLabel hpR hq
  rw [he]
  congr 1
  apply Units.ext
  exact congrArg (fun n : ℕ => (n : ZMod p)) hj

/--
A short residue collision extends to a plane with unique integral coordinates and an injective principal character preserving the source and its contact depth. This is used in Section 6 of the paper.
-/
theorem freshTorusWitness {I : Type*} [Fintype I] {p R : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {S r : ℝ} (hpR : p ∣ R) (q : ℕ × ℕ)
    (hf : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.1) (ht : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.2)
    (base : (Unit ⊕ I) ⊕ Bool → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (hi : Function.Injective base)
    (hbf : base (.inr false) = q.1) (hbt : base (.inr true) = q.2)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)))
    (hroof : v.val.toAdd (.inl ()) ≠ 0)
    (hprim : ∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i))) (a : ℝ),
      (∀ i, (w.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, w = v ^ c)
    (source : ℚ) (m : ℤ)
    (hz : (_root_.AbcTwoNinths.Diamond.character (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i)) v : ℚ) = source)
    (hm : padicValRat p (source - 1) = m)
    (weight : I → ℝ) (w : _root_.AbcTwoNinths.ExteriorE2.Old I)
    (hshort : _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd w) < r)
    (hlabel : _root_.AbcTwoNinths.Diamond.oldPrimeReduction (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i)) (Multiplicative.ofAdd w) *
        (_root_.AbcTwoNinths.Diamond.residuePrimeLabel p q.1 / _root_.AbcTwoNinths.Diamond.residuePrimeLabel p q.2) = 1) :
    ∃ u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid,
      let V := _root_.AbcTwoNinths.Diamond.extension base prime avoid v
      let γ := _root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid V u
      u.val = _root_.AbcTwoNinths.Diamond.extendExponents (Multiplicative.ofAdd w) 1 (-1) ∧
      u.val.toAdd (.inr false) = 1 ∧ u.val.toAdd (.inr true) = -1 ∧
      _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < r ∧
      (∀ y : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid, _root_.AbcTwoNinths.Diamond.inRealPlane V.val u.val y.val →
        ∃! c : ℤ × ℤ, y.val = _root_.AbcTwoNinths.Diamond.along V.val u.val c) ∧
      Function.Injective γ ∧
      (∀ c : ℤ × ℤ, _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (γ (Multiplicative.ofAdd c) : ℚ)) ∧
      (γ (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)) : ℚ) = source ∧
      padicValRat p ((γ (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)) : ℚ) - 1) = m := by
  let B := fun i => QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (_root_.AbcTwoNinths.ExteriorE2.residueUnit base prime avoid i)
  have hmem : _root_.AbcTwoNinths.Diamond.extendExponents (Multiplicative.ofAdd w) 1 (-1) ∈ _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid := by
    change _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid) (_root_.AbcTwoNinths.Diamond.extendExponents (Multiplicative.ofAdd w) 1 (-1)) = 1
    rw [_root_.AbcTwoNinths.ExteriorE2.residue, _root_.AbcTwoNinths.Diamond.reductionEval, _root_.AbcTwoNinths.Diamond.extendEval]
    have he : _root_.AbcTwoNinths.ExteriorE2.eval (fun i => B (.inl i)) (Multiplicative.ofAdd w) =
        _root_.AbcTwoNinths.Diamond.oldPrimeReduction (fun i => base (.inl i)) (fun i => prime (.inl i))
          (fun i => avoid (.inl i)) (Multiplicative.ofAdd w) := by
      rw [_root_.AbcTwoNinths.Diamond.oldPrimeReduction, _root_.AbcTwoNinths.ExteriorE2.residue, _root_.AbcTwoNinths.Diamond.reductionEval]
      rfl
    change _root_.AbcTwoNinths.ExteriorE2.eval (fun i => B (.inl i)) (Multiplicative.ofAdd w) *
      (B (.inr false) ^ (1 : ℤ) * B (.inr true) ^ (-1 : ℤ)) = 1
    rw [he, show B (.inr false) = _ from residueFreshEq hpR hf base prime avoid _ hbf,
      show B (.inr true) = _ from residueFreshEq hpR ht base prime avoid _ hbt]
    simpa only [zpow_one, zpow_neg_one, ← div_eq_mul_inv] using hlabel
  let u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid := ⟨_, hmem⟩
  let V := _root_.AbcTwoNinths.Diamond.extension base prime avoid v
  have hVroof : V.val.toAdd (.inl (.inl ())) ≠ 0 := hroof
  have hVfresh : V.val.toAdd (.inr false) = 0 := rfl
  have huf : u.val.toAdd (.inr false) = 1 := rfl
  refine ⟨u, rfl, huf, rfl, hshort, ?_,
    _root_.AbcTwoNinths.Diamond.planeCharacterInjective base prime avoid hi V u (.inl ()) hVroof hVfresh huf,
    _root_.AbcTwoNinths.Diamond.planeCharacterPrincipal base prime avoid V u,
    _root_.AbcTwoNinths.Diamond.sourceContactUnchanged base prime avoid v u source hz,
    _root_.AbcTwoNinths.Diamond.contactDepthPreserved base prime avoid v u source m hz hm⟩
  intro y hy
  obtain ⟨c, hc⟩ := _root_.AbcTwoNinths.Diamond.completeCoordinates base prime avoid v u y huf hprim hy
  exact ⟨c, hc, fun d hd => _root_.AbcTwoNinths.Diamond.alongInjective _ _ (.inl ()) hVroof hVfresh huf (hd.symm.trans hc)⟩

/--
Append the first and second entries of the prime pair at the false and true coordinates, respectively. This is used in Section 6 of the paper.
-/
def freshExtendedBase {ι : Type*} (old : ι → ℕ) (q : ℕ × ℕ) : ι ⊕ Bool → ℕ
  | .inl i => old i
  | .inr false => q.1
  | .inr true => q.2

/--
Adjoining an increasing pair of fresh primes preserves primality, avoidance of the selected prime, and injectivity of the base.
-/
theorem freshExtendedBaseValid {ι : Type*} {p R : ℕ} {S : ℝ} (hpR : p ∣ R)
    (old : ι → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
    (hi : Function.Injective old) (holdR : ∀ i, old i ∣ R)
    (q : ℕ × ℕ) (hf : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.1) (ht : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.2)
    (hq : q.1 < q.2) :
    (∀ j, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q j).Prime) ∧
    (∀ j, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old q j) ∧
    Function.Injective (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) := by
  have hfR : ¬ q.1 ∣ R := fun h => hf.2.2.2 (dvd_mul_of_dvd_right h 2)
  have htR : ¬ q.2 ∣ R := fun h => ht.2.2.2 (dvd_mul_of_dvd_right h 2)
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | (_ | _))
    exacts [prime i, hf.1, ht.1]
  · rintro (i | (_ | _))
    · exact avoid i
    · exact fun h => hfR ((show p = q.1 from h) ▸ hpR)
    · exact fun h => htR ((show p = q.2 from h) ▸ hpR)
  · rintro (i | (_ | _)) (j | (_ | _)) h
    · exact congrArg Sum.inl (hi h)
    · exact (hfR ((show old i = q.1 from h) ▸ holdR i)).elim
    · exact (htR ((show old i = q.2 from h) ▸ holdR i)).elim
    · exact (hfR ((show q.1 = old j from h).symm ▸ holdR j)).elim
    · rfl
    · exact (hq.ne h).elim
    · exact (htR ((show q.2 = old j from h).symm ▸ holdR j)).elim
    · exact (hq.ne h.symm).elim
    · rfl

end

end AbcTwoNinths.Diamond
