/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ExponentResidue
public import AbcTwoNinths.Basic.Pigeonhole
public import AbcTwoNinths.Basic.PrimitiveResidueVector

/-!
# Exponent Residue Collision

The module converts a collision of exponent residues into a nonzero vector with a logarithmic size bound.

## Main results
* `AbcTwoNinths.Basic.gammaCollision`
* `AbcTwoNinths.Basic.gammaLogCollision`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/-- The chart. -/
private def chart {I : Type*} (a : ℤ) (v : I → ℤ) : Option I → ℤ
  | none => a
  | some j => v j

/-- The pack. -/
private def pack {I : Type*} : (ℤ × (I → ℤ)) →+ (Option I → ℤ) where
  toFun x := chart x.1 x.2
  map_zero' := by ext j; cases j <;> rfl
  map_add' x y := by ext j; cases j <;> rfl

/--
Weighted residue bins produce a second kernel vector outside the rational pivot line and within the strict weighted error budget.
-/
theorem gammaCollision {I : Type*} [Fintype I] [Nonempty I] {p : ℕ}
    (hp : p.Prime) (q : Option I → ℕ) (haway : ∀ j, ¬ p ∣ q j)
    (e : Option I → ℤ) (E : ℕ) (hpivot : e none = (E : ℤ))
    (Q : I → ℕ) (hQ : ∀ j, 0 < Q j) (w : Option I → ℝ)
    (hw : ∀ j, 0 < w (some j)) (T : ℝ)
    (hbudget : ∑ j, w (some j) / (Q j : ℝ) ≤ T)
    (hcount : (p - 1) * ∏ j, Q j < E)
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker e) :
    ∃ (v : Option I → ℤ) (lam : ℝ),
      v ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker ∧
      0 < lam ∧ lam < 1 ∧
      (¬ ∃ r : ℚ, ∀ j, (v j : ℚ) = r * (e j : ℚ)) ∧
      ∑ j, |(v j : ℝ) - lam * (e j : ℝ)| * w j < T := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let chi := _root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)
  let phi : Multiplicative (ℤ × (I → ℤ)) →* (ZMod p)ˣ :=
    { toFun := fun x => (chi (pack x.toAdd)).toMul
      map_one' := by change chi (pack 0) = 0; simp
      map_mul' := by
        intro x y
        change chi (pack (x.toAdd + y.toAdd)) = chi (pack x.toAdd) + chi (pack y.toAdd)
        rw [map_add, map_add] }
  have hc : Fintype.card (ZMod p)ˣ * ∏ j, Q j < E := by
    rw [ZMod.card_units]; exact hcount
  obtain ⟨k, u, hk, hkE, hunit, herr⟩ :=
    _root_.AbcTwoNinths.Basic.collision phi E (fun j => e (some j)) Q hQ hc
  let v := chart (k : ℤ) u
  let lam := (k : ℝ) / (E : ℝ)
  have hv : v ∈ chi.ker := hunit
  have hEr : 0 < (E : ℝ) := by exact_mod_cast (hk.trans hkE)
  have hvr : (k : ℝ) = lam * (E : ℝ) := by
    dsimp [lam]; field_simp
  refine ⟨v, lam, hv, div_pos (by exact_mod_cast hk) hEr,
    (div_lt_one hEr).mpr (by exact_mod_cast hkE), ?_, ?_⟩
  · apply _root_.AbcTwoNinths.Basic.independentOfPrimitivePivot he hv hprim none
    · change 0 < (k : ℤ); exact_mod_cast hk
    · change (k : ℤ) < e none; rw [hpivot]; exact_mod_cast hkE
  · rw [Fintype.sum_option]
    change |(k : ℝ) - lam * (e none : ℝ)| * w none + _ < T
    rw [hpivot, Int.cast_natCast, ← hvr, sub_self, abs_zero, zero_mul, zero_add]
    exact _root_.AbcTwoNinths.Basic.weightedError Q (fun j => w (some j)) _ T hw herr hbudget

/--
Ceiling bins for prime logarithms produce an independent kernel vector within the logarithmic error budget.
-/
theorem gammaLogCollision {I : Type*} [Fintype I] [Nonempty I] {p : ℕ}
    (hp : p.Prime) (q : Option I → ℕ) (hq : ∀ j, (q j).Prime)
    (haway : ∀ j, ¬ p ∣ q j) (e : Option I → ℤ) (E : ℕ)
    (hpivot : e none = (E : ℤ)) (T : ℝ) (hT : 0 < T)
    (hcount : (p - 1) * ∏ j, ⌈(Fintype.card I : ℝ) * Real.log (q (some j)) / T⌉₊ < E)
    (he : e ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker)
    (hprim : _root_.AbcTwoNinths.Basic.PrimitiveIn (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker e) :
    ∃ (v : Option I → ℤ) (lam : ℝ),
      v ∈ (_root_.AbcTwoNinths.Basic.residue q (_root_.AbcTwoNinths.Basic.awayCoprime hp q haway)).ker ∧
      0 < lam ∧ lam < 1 ∧
      (¬ ∃ r : ℚ, ∀ j, (v j : ℚ) = r * (e j : ℚ)) ∧
      ∑ j, |(v j : ℝ) - lam * (e j : ℝ)| * Real.log (q j) < T := by
  have hw (j : I) : 0 < Real.log (q (some j)) :=
    Real.log_pos (by exact_mod_cast (hq (some j)).one_lt)
  obtain ⟨hQ, hs⟩ := _root_.AbcTwoNinths.Basic.ceilBins (fun j => Real.log (q (some j))) T hw hT
  exact _root_.AbcTwoNinths.Basic.gammaCollision hp q haway e E hpivot _ hQ (fun j => Real.log (q j))
    hw T hs hcount he hprim

end

end AbcTwoNinths.Basic
