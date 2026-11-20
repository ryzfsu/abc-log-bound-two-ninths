/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlap
public import AbcTwoNinths.Paper.S6_Diamond.LatticeTranslateOverlap

/-!
# Same Source Overlap Counting

The module counts weighted overlaps on a common source and associates fresh-prime labels with the witnesses. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.nativeSameSourceFamily`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

noncomputable section

open MeasureTheory Set
open scoped Pointwise ENNReal

section



variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Type*} [CommGroup G]

/--
The weighted open ball centered at the projection of an exponent vector. This is used in Section 6 of the paper.
-/
def weightedPatch (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (r : ℝ) (a : _root_.AbcTwoNinths.ExteriorE2.Old I) : Set (_root_.AbcTwoNinths.ExteriorE2.Coord I) :=
  _root_.AbcTwoNinths.ExteriorE2.ball weight (_root_.AbcTwoNinths.ExteriorE2.project s a) r

omit [DecidableEq I] in
/--
An overlap of two weighted patches gives a short exponent vector correcting the quotient of their labels.
-/
theorem weightedWitness (s : _root_.AbcTwoNinths.ExteriorE2.Old I) (red : Multiplicative (_root_.AbcTwoNinths.ExteriorE2.Old I) →* G)
    (label : ℕ → G) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    {r : ℝ} {i j : ℕ}
    (h : _root_.AbcTwoNinths.Diamond.PatchInput red (_root_.AbcTwoNinths.ExteriorE2.project s).toAddMonoidHom label (_root_.AbcTwoNinths.Diamond.weightedPatch s weight r) i j) :
    ∃ u : _root_.AbcTwoNinths.ExteriorE2.Old I, _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project s u) < r + r ∧
      red (Multiplicative.ofAdd u) * (label i / label j) = 1 := by
  obtain ⟨x, y, t, z, hxi, hyj, ⟨a, ha, hza⟩, ⟨b, hb, hzb⟩⟩ := h
  let pi := (_root_.AbcTwoNinths.ExteriorE2.project s).toAddMonoidHom
  let Q := QuotientAddGroup.mk' (_root_.AbcTwoNinths.Diamond.Lattice red pi)
  have hzero : Q (a - b) = 0 := by
    rw [map_sub, show Q a = z from hza, show Q b = z from hzb, sub_self]
  obtain ⟨w, hwK, hwp⟩ := (QuotientAddGroup.eq_zero_iff _).mp hzero
  refine ⟨w - x + y, ?_, ?_⟩
  · change _root_.AbcTwoNinths.ExteriorE2.cost weight (pi (w - x + y)) < r + r
    change _root_.AbcTwoNinths.ExteriorE2.cost weight (a - pi x) < r at ha
    change _root_.AbcTwoNinths.ExteriorE2.cost weight (b - pi y) < r at hb
    change pi w = a - b at hwp
    rw [map_add, map_sub, hwp]
    have hs : a - b - pi x + pi y = (a - pi x) - (b - pi y) := by abel
    rw [hs]
    exact (_root_.AbcTwoNinths.ExteriorE2.costSubLe weight hw _ _).trans_lt (add_lt_add ha hb)
  · have heq : Multiplicative.ofAdd (w - x + y) =
        Multiplicative.ofAdd w * (Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y := rfl
    rw [heq]
    exact _root_.AbcTwoNinths.Diamond.correctedLabel red _ _ _ _ _ t ((_root_.AbcTwoNinths.Diamond.memOldKernel red w).mp hwK) hxi hyj

/--
A volume lower bound gives a family of ordered fresh-prime pairs with a short residue witness for each pair. This is used in Section 6 of the paper.
-/
theorem nativeSameSourceFamily [Finite G] (s : _root_.AbcTwoNinths.ExteriorE2.Old I)
    (hs : s (.inl ()) ≠ 0) (red : Multiplicative (_root_.AbcTwoNinths.ExteriorE2.Old I) →* G)
    (hred : red (Multiplicative.ofAdd s) = 1)
    (primitive : ∀ (a : ℤ) (w : red.toAdditive.ker),
      a • w = ⟨s, hred⟩ → IsUnit a)
    (label : ℕ → G) (weight : I → ℝ) (hweight : ∀ i, 0 < weight i)
    {R : ℕ} (hR : 0 < R) {p H η x r B₀ : ℝ} (hx : Real.log R = 3*x)
    (a : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x) (hX : max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin η)) / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ x)
    (hshort : ∀ w ∈ red.toAdditive.ker, _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project s w) < r → _root_.AbcTwoNinths.ExteriorE2.project s w = 0)
    (hr : 0 < r) (hB₀ : 0 < B₀) (hWeightSum : ∑ i, weight i ≤ B₀) :
    let S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
    let n := ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ)
    let W₀ := (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 (r / 2))
    ∃ P : Finset (ℕ × ℕ),
      ((r / 2) / B₀) ^ Fintype.card I ≤ W₀ ∧
      (n / 2) * (n * W₀ / ((Nat.card G : ℝ) / |(s (.inl ()) : ℝ)|) - 1) ≤ P.card ∧
      ∀ q ∈ P, _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.1 ∧ _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.2 ∧ q.1 < q.2 ∧
        _root_.AbcTwoNinths.Diamond.PatchInput red (_root_.AbcTwoNinths.ExteriorE2.project s).toAddMonoidHom label (_root_.AbcTwoNinths.Diamond.weightedPatch s weight (r / 2)) q.1 q.2 ∧
        ∃ u : _root_.AbcTwoNinths.ExteriorE2.Old I, _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project s u) < r ∧
          red (Multiplicative.ofAdd u) * (label q.1 / label q.2) = 1 := by
  classical
  let s₀ : red.toAdditive.ker := ⟨s, hred⟩
  have hn : s₀ ≠ 0 := by
    intro he
    exact hs (congrArg (fun w : red.toAdditive.ker => w.val (.inl ())) he)
  obtain ⟨basis, hb⟩ := _root_.AbcTwoNinths.ExteriorE2.existsSourceBasis red.toAdditive s₀ hn primitive
  obtain ⟨D, hD, hDm, hDf, hVol⟩ := _root_.AbcTwoNinths.ExteriorE2.fundamentalData red.toAdditive s hs basis
    (congrArg Subtype.val hb)
  let pi := (_root_.AbcTwoNinths.ExteriorE2.project s).toAddMonoidHom
  let B := _root_.AbcTwoNinths.Diamond.weightedPatch s weight (r / 2)
  have hWlow := _root_.AbcTwoNinths.Diamond.ballVolumeLower weight hweight (half_pos hr) hB₀ hWeightSum
  have hW : 0 < (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 (r / 2)) :=
    lt_of_lt_of_le (by positivity) hWlow
  let _ : Fintype (_root_.AbcTwoNinths.Diamond.Tag red) := Fintype.ofFinite _
  let _ : MeasurableSpace (_root_.AbcTwoNinths.Diamond.Tag red) := ⊤
  let _ : MeasurableSingletonClass (_root_.AbcTwoNinths.Diamond.Tag red) := ⟨fun _ => trivial⟩
  let projectK : _root_.AbcTwoNinths.Diamond.oldKernel red → _root_.AbcTwoNinths.Diamond.Lattice red pi := fun a => ⟨pi a, ⟨a, a.property, rfl⟩⟩
  have hprojectK : Function.Surjective projectK := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have : Countable (_root_.AbcTwoNinths.Diamond.Lattice red pi) := hprojectK.countable
  have hact : ∀ c, ∀ u ∈ B c, ∀ v ∈ B c, ∀ l : _root_.AbcTwoNinths.Diamond.Lattice red pi, l +ᵥ u = v → l = 0 :=
    fun c => _root_.AbcTwoNinths.ExteriorE2.ballOrbitInjective red.toAdditive s weight (fun j => (hweight j).le)
      (_root_.AbcTwoNinths.ExteriorE2.project s c) r hshort
  have hnorm : (Fintype.card (_root_.AbcTwoNinths.Diamond.Tag red) : ℝ) * volume.real D =
      (Nat.card G : ℝ) / |(s (.inl ()) : ℝ)| := by
    have hi := red.range.index_mul_card
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card (α := _root_.AbcTwoNinths.Diamond.Tag red)] at hi
    have hcast : (Fintype.card (_root_.AbcTwoNinths.Diamond.Tag red) : ℝ) * Nat.card red.range = Nat.card G := by
      exact_mod_cast hi
    change volume.real D = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)| at hVol
    rw [hVol, ← mul_div_assoc, hcast]
  dsimp
  set S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
  have hS : 0 < S := _root_.AbcTwoNinths.ExteriorE2.MPos _ _ _ _
  have hS₁ : 1 < S := (Real.log_pos_iff hS.le).mp
    ((mul_pos (_root_.AbcTwoNinths.ExteriorE2.marginPos a.eta_lt) a.hx).trans_le (_root_.AbcTwoNinths.ExteriorE2.shellSlack a).1)
  have hQ := _root_.AbcTwoNinths.ExteriorE2.noEmptySupply hS₁ (_root_.AbcTwoNinths.ExteriorE2.adaptiveFreshSupply hR hx a hX)
  obtain ⟨P, hcard, hp⟩ := _root_.AbcTwoNinths.Diamond.sameSourcePatchFamily red pi hD hDm hDf label (_root_.AbcTwoNinths.ExteriorE2.fresh R S) hQ B
    (fun c => (_root_.AbcTwoNinths.ExteriorE2.ballOpen weight (_root_.AbcTwoNinths.ExteriorE2.project s c) (r / 2)).measurableSet) hact hW
    (fun c => _root_.AbcTwoNinths.ExteriorE2.ballMassEq weight (_root_.AbcTwoNinths.ExteriorE2.project s c) (r / 2))
  rw [hnorm] at hcard
  refine ⟨P, hWlow, hcard, ?_⟩
  intro q hq
  obtain ⟨hq₁, hq₂, hlt, hw⟩ := hp q hq
  refine ⟨(_root_.AbcTwoNinths.ExteriorE2.memFresh hS.le).mp hq₁, (_root_.AbcTwoNinths.ExteriorE2.memFresh hS.le).mp hq₂, hlt, hw, ?_⟩
  obtain ⟨u, hu, hlabel⟩ := _root_.AbcTwoNinths.Diamond.weightedWitness s red label weight (fun j => (hweight j).le) hw
  exact ⟨u, (show r / 2 + r / 2 = r by ring) ▸ hu, hlabel⟩

/--
The residue label modulo signs of a natural number, with value one at multiples of the contact prime. This is used in Section 6 of the paper.
-/
def residuePrimeLabel (p : ℕ) [Fact p.Prime] (q : ℕ) : _root_.AbcTwoNinths.ExteriorE2.Label p :=
  if h : (q : ZMod p) = 0 then 1
  else QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (Units.mk0 (q : ZMod p) h)

/--
A fresh prime has nonzero residue at the contact prime and its label is the class of that unit.
-/
theorem freshPrimeLabel {p R q : ℕ} [Fact p.Prime] {S : ℝ} (hpR : p ∣ R)
    (hq : _root_.AbcTwoNinths.ExteriorE2.Fresh S R q) :
    ∃ h : (q : ZMod p) ≠ 0,
      _root_.AbcTwoNinths.Diamond.residuePrimeLabel p q = QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) (Units.mk0 (q : ZMod p) h) := by
  have h : (q : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ q := ZMod.natCast_eq_zero_iff q p |>.mp he
    have hEq : p = q := (Nat.prime_dvd_prime_iff_eq Fact.out hq.1).mp hd
    exact hq.2.2.2 (hEq ▸ dvd_mul_of_dvd_right hpR 2)
  exact ⟨h, by simp [_root_.AbcTwoNinths.Diamond.residuePrimeLabel, h]⟩

/--
Reduction modulo signs of the prime monomial attached to an exponent vector on the original base. This is used in Section 6 of the paper.
-/
def oldPrimeReduction {p : ℕ} [Fact p.Prime] (base : Unit ⊕ I → ℕ)
    (prime : ∀ j, (base j).Prime) (avoid : ∀ j, p ≠ base j) :
    Multiplicative (_root_.AbcTwoNinths.ExteriorE2.Old I) →* _root_.AbcTwoNinths.ExteriorE2.Label p :=
  _root_.AbcTwoNinths.ExteriorE2.reduction (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid)

end

end
end AbcTwoNinths.Diamond
