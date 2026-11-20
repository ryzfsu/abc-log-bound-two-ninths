/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.CollisionConsumer
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLatticeContact
public import Mathlib.Tactic

/-!
# Selected Plane Data

The module defines the character of a source lattice, its full kernel, and the associated plane character. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.extensionCharacter`
* `AbcTwoNinths.Diamond.completeCoordinates`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

section




variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

/--
The exponent lattice whose prime product reduces to a sign modulo the selected prime. This is used in Section 6 of the paper.
-/
abbrev LatticeSelectedPlaneData (base : ι → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) := _root_.AbcTwoNinths.ExteriorE2.Kernel (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid)

/--
The signed rational prime product on the residue lattice. This is used in Section 6 of the paper.
-/
def character (base : ι → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid →* ℚˣ :=
  _root_.AbcTwoNinths.ExteriorE2.gammaStar (_root_.AbcTwoNinths.ExteriorE2.residue base prime avoid) (_root_.AbcTwoNinths.ExteriorE2.monomial base prime)

/--
The integral combination of two exponent vectors in the specified coefficient order. This is used in Section 6 of the paper.
-/
def along (v u : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool)) (c : ℤ × ℤ) : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool) :=
  v ^ c.1 * u ^ c.2

omit [Fintype ι] in
/--
Each exponent of a plane combination is the same integral combination of the corresponding exponents.
-/
theorem alongApply (v u : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool)) (c : ℤ × ℤ) (i : ι ⊕ Bool) :
    (_root_.AbcTwoNinths.Diamond.along v u c).toAdd i = c.1 * v.toAdd i + c.2 * u.toAdd i := by
  simp [_root_.AbcTwoNinths.Diamond.along, zsmul_eq_mul]

omit [Fintype ι] in
/--
A nonzero old coordinate of the first vector and fresh coordinates zero and one give unique coefficients.
-/
theorem alongInjective (v u : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool)) (k : ι)
    (hroof : v.toAdd (.inl k) ≠ 0) (hv : v.toAdd (.inr false) = 0)
    (hu : u.toAdd (.inr false) = 1) : Function.Injective (_root_.AbcTwoNinths.Diamond.along v u) := by
  intro c d heq
  have hb := congrArg (fun w : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool) => w.toAdd (.inr false)) heq
  simp only [_root_.AbcTwoNinths.Diamond.alongApply, hv, hu, mul_zero, mul_one, zero_add] at hb
  have ha := congrArg (fun w : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool) => w.toAdd (.inl k)) heq
  simp only [_root_.AbcTwoNinths.Diamond.alongApply, hb, add_left_inj] at ha
  exact Prod.ext (mul_right_cancel₀ hroof ha) hb

/--
The signed lattice character evaluated on the integral combinations of two lattice vectors. This is used in Section 6 of the paper.
-/
def planeCharacter (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (v u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) :
    Multiplicative (ℤ × ℤ) →* ℚˣ where
  toFun c := _root_.AbcTwoNinths.Diamond.character base prime avoid (v ^ c.toAdd.1 * u ^ c.toAdd.2)
  map_one' := by simp
  map_mul' c d := by
    change _root_.AbcTwoNinths.Diamond.character base prime avoid
      (v ^ (c.toAdd.1 + d.toAdd.1) * u ^ (c.toAdd.2 + d.toAdd.2)) = _
    simp only [zpow_add, map_mul]
    ac_rfl

/--
Distinct support primes and the distinguished old and fresh coordinates make the plane character injective.
-/
theorem planeCharacterInjective (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (hi : Function.Injective base) (v u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid)
    (k : ι) (hroof : v.val.toAdd (.inl k) ≠ 0) (hv : v.val.toAdd (.inr false) = 0)
    (hu : u.val.toAdd (.inr false) = 1) :
    Function.Injective (_root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid v u) := by
  intro c d h
  have h' := _root_.AbcTwoNinths.ExteriorE2.modularResidueLatticeInjective base prime hi avoid h
  have heq : _root_.AbcTwoNinths.Diamond.along v.val u.val c.toAdd = _root_.AbcTwoNinths.Diamond.along v.val u.val d.toAdd :=
    congrArg Subtype.val h'
  exact Multiplicative.toAdd.injective (_root_.AbcTwoNinths.Diamond.alongInjective _ _ k hroof hv hu heq)

/-- Each value of the plane character is a principal unit at the selected prime. -/
theorem planeCharacterPrincipal (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (v u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (c : ℤ × ℤ) :
    _root_.AbcTwoNinths.Basic.PrincipalPrincipalUnitData p (_root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid v u (Multiplicative.ofAdd c) : ℚ) :=
  _root_.AbcTwoNinths.ExteriorE2.signedLiftPrincipal base prime avoid (v ^ c.1 * u ^ c.2)

omit [Fact (2 < p)] in
private theorem residueExtendZero (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i) (v : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) :
    _root_.AbcTwoNinths.ExteriorE2.residue base prime avoid (_root_.AbcTwoNinths.Diamond.extendExponents v 0 0) =
      _root_.AbcTwoNinths.ExteriorE2.residue (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)) v := by
  unfold _root_.AbcTwoNinths.ExteriorE2.residue
  rw [_root_.AbcTwoNinths.Diamond.extendEval]
  simp only [zpow_zero, mul_one]
  congr 1

omit [Fact (2 < p)] [Fact p.Prime] in
private theorem monomialExtendZero (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (v : _root_.AbcTwoNinths.ExteriorE2.Exponents ι) :
    _root_.AbcTwoNinths.ExteriorE2.monomial base prime (_root_.AbcTwoNinths.Diamond.extendExponents v 0 0) =
      _root_.AbcTwoNinths.ExteriorE2.monomial (fun i => base (.inl i)) (fun i => prime (.inl i)) v := by
  unfold _root_.AbcTwoNinths.ExteriorE2.monomial
  rw [_root_.AbcTwoNinths.Diamond.extendEval]
  simp only [zpow_zero, mul_one]
  congr 1

/--
Extend a residue lattice vector by zero at both auxiliary primes. This is used in Section 6 of the paper.
-/
def extension (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i))) :
    _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid :=
  ⟨_root_.AbcTwoNinths.Diamond.extendExponents v.val 0 0, by
    have he := residueExtendZero base prime avoid v.val
    exact (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).2 (he.symm ▸ (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).1 v.property)⟩

/--
Extending a lattice vector by zero preserves its signed rational character. This is used in Section 6 of the paper.
-/
theorem extensionCharacter (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i))) :
    _root_.AbcTwoNinths.Diamond.character base prime avoid (_root_.AbcTwoNinths.Diamond.extension base prime avoid v) =
      _root_.AbcTwoNinths.Diamond.character (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)) v := by
  have he := residueExtendZero base prime avoid v.val
  have hm := monomialExtendZero base prime v.val
  simp only [_root_.AbcTwoNinths.Diamond.character, _root_.AbcTwoNinths.ExteriorE2.gammaStar, MonoidHom.coe_mk, OneHom.coe_mk,
    _root_.AbcTwoNinths.ExteriorE2.signUnit, _root_.AbcTwoNinths.Diamond.extension, he, hm]

/--
The value at the first coordinate vector is the prescribed signed character of the old source.
-/
theorem sourceContactUnchanged (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)))
    (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (z : ℚ)
    (hz : (_root_.AbcTwoNinths.Diamond.character (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i)) v : ℚ) = z) :
    (_root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid (_root_.AbcTwoNinths.Diamond.extension base prime avoid v) u
      (Multiplicative.ofAdd ((1,0) : ℤ × ℤ)) : ℚ) = z := by
  change (_root_.AbcTwoNinths.Diamond.character base prime avoid ((_root_.AbcTwoNinths.Diamond.extension base prime avoid v) ^ (1 : ℤ) * u ^ (0 : ℤ)) : ℚ) = z
  simpa only [zpow_one, zpow_zero, mul_one, _root_.AbcTwoNinths.Diamond.extensionCharacter] using hz

/--
An exponent vector lies in the real span of the given pair of exponent vectors. This is used in Section 6 of the paper.
-/
def inRealPlane (v u w : _root_.AbcTwoNinths.ExteriorE2.Exponents (ι ⊕ Bool)) : Prop :=
  ∃ a b : ℝ, ∀ i, (w.toAdd i : ℝ) = a * v.toAdd i + b * u.toAdd i

omit [Fact (2 < p)] in
/--
The fresh coordinate forces the second coefficient to be an integer. Subtracting
the corresponding lattice vector leaves an old vector on the original source line. This is used in Section 6 of the paper.
-/
theorem completeCoordinates (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)))
    (u w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (hu : u.val.toAdd (.inr false) = 1)
    (hprim : ∀ (y : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i))) (a : ℝ),
      (∀ i, (y.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, y = v ^ c)
    (hw : _root_.AbcTwoNinths.Diamond.inRealPlane (_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val u.val w.val) :
    ∃ c : ℤ × ℤ, w.val = _root_.AbcTwoNinths.Diamond.along (_root_.AbcTwoNinths.Diamond.extension base prime avoid v).val u.val c := by
  let V := _root_.AbcTwoNinths.Diamond.extension base prime avoid v
  obtain ⟨a,b,hw⟩ := hw
  let d := w.val.toAdd (.inr false)
  have hd : (d : ℝ) = b := by simpa [d, V, _root_.AbcTwoNinths.Diamond.extension, _root_.AbcTwoNinths.Diamond.extendExponents, hu] using hw (.inr false)
  let y := w * u ^ (-d)
  have hy : ∀ i, (y.val.toAdd i : ℝ) = a * V.val.toAdd i := by
    intro i
    have he : y.val = _root_.AbcTwoNinths.Diamond.along w.val u.val (1,-d) := by simp [y, _root_.AbcTwoNinths.Diamond.along]
    rw [he, _root_.AbcTwoNinths.Diamond.alongApply]
    push_cast
    rw [hw i, hd]
    ring
  let old := Multiplicative.ofAdd (fun i : ι => y.val.toAdd (.inl i))
  have hext : _root_.AbcTwoNinths.Diamond.extendExponents old 0 0 = y.val := by
    apply Multiplicative.toAdd.injective
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      have hzero := hy (.inr i)
      simp [V, _root_.AbcTwoNinths.Diamond.extension, _root_.AbcTwoNinths.Diamond.extendExponents] at hzero
      simpa [_root_.AbcTwoNinths.Diamond.extendExponents] using hzero.symm
  have hold : old ∈ _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i)) := by
    have he := residueExtendZero base prime avoid old
    rw [hext] at he
    exact (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).2 (he ▸ (_root_.AbcTwoNinths.ExteriorE2.memKer _ _).1 y.property)
  obtain ⟨c, hc⟩ := hprim ⟨old, hold⟩ a (fun i => hy (.inl i))
  have hys : y.val = V.val ^ c := by
    rw [← hext]
    have hc' : old = v.val ^ c := congrArg Subtype.val hc
    rw [hc']
    apply Multiplicative.toAdd.injective
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp [V, _root_.AbcTwoNinths.Diamond.extension, _root_.AbcTwoNinths.Diamond.extendExponents]
  refine ⟨(c,d), ?_⟩
  calc
    w.val = y.val * u.val ^ d := by simp [y, mul_assoc]
    _ = _root_.AbcTwoNinths.Diamond.along V.val u.val (c,d) := by rw [hys]; rfl

/--
The valuation of the plane character at the first coordinate vector minus one equals the given source depth.
-/
theorem contactDepthPreserved (base : (ι ⊕ Bool) → ℕ) (prime : ∀ i, (base i).Prime)
    (avoid : ∀ i, p ≠ base i)
    (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => base (.inl i)) (fun i => prime (.inl i)) (fun i => avoid (.inl i)))
    (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData base prime avoid) (z : ℚ) (m : ℤ)
    (hz : (_root_.AbcTwoNinths.Diamond.character (fun i => base (.inl i)) (fun i => prime (.inl i))
      (fun i => avoid (.inl i)) v : ℚ) = z) (hm : padicValRat p (z - 1) = m) :
    padicValRat p ((_root_.AbcTwoNinths.Diamond.planeCharacter base prime avoid (_root_.AbcTwoNinths.Diamond.extension base prime avoid v) u
      (Multiplicative.ofAdd ((1,0) : ℤ × ℤ)) : ℚ) - 1) = m := by
  rwa [_root_.AbcTwoNinths.Diamond.sourceContactUnchanged base prime avoid v u z hz]

end

end AbcTwoNinths.Diamond
