/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneBasisHeightBounds
public import AbcTwoNinths.Paper.S3_ExteriorE1.ExponentialHeightDistance
public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactReduction

/-!
# Integral Plane Coordinates

The module recovers integral plane coordinates and transports their residue reduction. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.coordinateReduction`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- Cramer's rule expresses a real coordinate pair in an integral basis whose determinant
has the integer inverse `d`. -/
theorem coordinateInverse (x z : ℤ × ℤ) (d : ℤ)
    (hd : d * _root_.AbcTwoNinths.ExteriorE1.det2 x z = 1) (A B : ℝ) :
    let a : ℝ := (d : ℝ) * ((z.2 : ℝ) * A - (z.1 : ℝ) * B)
    let b : ℝ := (d : ℝ) * (-(x.2 : ℝ) * A + (x.1 : ℝ) * B)
    (A, B) = a • _root_.AbcTwoNinths.ExteriorE1.realPair x + b • _root_.AbcTwoNinths.ExteriorE1.realPair z := by
  dsimp
  have h : (d : ℝ) * ((x.1 : ℝ) * z.2 - (x.2 : ℝ) * z.1) = 1 := by
    exact_mod_cast hd
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, _root_.AbcTwoNinths.ExteriorE1.realPair, smul_eq_mul]
  · linear_combination -A * h
  · linear_combination -B * h

/-- The prime-weighted plane admits a unimodular integral basis with a bounded height
product and bounded weighted coordinates for `(1, 0)`. -/
theorem coordinateReduction {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (w v : ι → ℤ) (hq : ∀ i, (q i).Prime)
    (hw : w ≠ 0) (hi : ¬ ∃ c : ℚ, ∀ i, (v i : ℚ) = c * (w i : ℚ))
    (f : Seminorm ℝ (ℝ × ℝ)) (hc : Continuous f)
    (hp : ∀ x, x ≠ 0 → 0 < f x)
    (hf : ∀ x : ℝ × ℝ, f x = _root_.AbcTwoNinths.ExteriorE1.planeHeight q w v x)
    (p : ℝ) :
    ∃ (x z : ℤ × ℤ) (a b : ℤ),
      |_root_.AbcTwoNinths.ExteriorE1.det2 x z| = 1 ∧ (1, 0) = a • x + b • z ∧
      0 < f (_root_.AbcTwoNinths.ExteriorE1.realPair x) ∧ 0 < f (_root_.AbcTwoNinths.ExteriorE1.realPair z) ∧
      f (_root_.AbcTwoNinths.ExteriorE1.realPair x) * f (_root_.AbcTwoNinths.ExteriorE1.realPair z) ≤ 4 * f (1, 0) * f (p, 1) ∧
      |(a : ℝ)| * f (_root_.AbcTwoNinths.ExteriorE1.realPair x) ≤ 3 * f (1, 0) ∧
      |(b : ℝ)| * f (_root_.AbcTwoNinths.ExteriorE1.realPair z) ≤ 2 * f (1, 0) := by
  obtain ⟨x, z, hx, hd, hmin, htrans⟩ := _root_.AbcTwoNinths.ExteriorE1.existsUnimodularMinima q w v hq hw hi
  have hsign : _root_.AbcTwoNinths.ExteriorE1.det2 x z = 1 ∨ _root_.AbcTwoNinths.ExteriorE1.det2 x z = -1 := by
    rcases le_total 0 (_root_.AbcTwoNinths.ExteriorE1.det2 x z) with h | h
    · exact Or.inl (by simpa [abs_of_nonneg h] using hd)
    · exact Or.inr (by rw [abs_of_nonpos h] at hd; omega)
  let d := _root_.AbcTwoNinths.ExteriorE1.det2 x z
  have hdd : d * _root_.AbcTwoNinths.ExteriorE1.det2 x z = 1 := by
    rcases hsign with h | h <;> simp [d, h]
  have hdz : _root_.AbcTwoNinths.ExteriorE1.det2 x z ≠ 0 := by omega
  have hz : z ≠ 0 := by
    rintro rfl
    simp [_root_.AbcTwoNinths.ExteriorE1.det2] at hdz
  have hrz : _root_.AbcTwoNinths.ExteriorE1.realPair z ≠ 0 := by
    intro h
    apply hz
    apply Prod.ext
    · have he : (z.1 : ℝ) = 0 := congrArg Prod.fst h
      exact_mod_cast he
    · have he : (z.2 : ℝ) = 0 := congrArg Prod.snd h
      exact_mod_cast he
  have hrx : _root_.AbcTwoNinths.ExteriorE1.realPair x ≠ 0 := by
    intro h
    apply hx
    apply Prod.ext
    · have he : (x.1 : ℝ) = 0 := congrArg Prod.fst h
      exact_mod_cast he
    · have he : (x.2 : ℝ) = 0 := congrArg Prod.snd h
      exact_mod_cast he
  have hind : ¬ ∃ s : ℝ, _root_.AbcTwoNinths.ExteriorE1.realPair z = s • _root_.AbcTwoNinths.ExteriorE1.realPair x := by
    rintro ⟨s, hs⟩
    have h₁ := congrArg Prod.fst hs
    have h₂ := congrArg Prod.snd hs
    simp only [_root_.AbcTwoNinths.ExteriorE1.realPair, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h₁ h₂
    have h0 : (x.1 : ℝ) * z.2 - (x.2 : ℝ) * z.1 = 0 := by
      rw [h₁, h₂]
      ring
    exact hdz (by exact_mod_cast h0)
  obtain ⟨u, t, ht, hclose, hqmin⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.existsAttainedQuotientDistOfContinuous f hc _ _ (hp _ hrx) hind hp
  have hshort (n : ℤ) : f (_root_.AbcTwoNinths.ExteriorE1.realPair z) ≤ f (_root_.AbcTwoNinths.ExteriorE1.realPair z - (n : ℝ) • _root_.AbcTwoNinths.ExteriorE1.realPair x) := by
    have he : _root_.AbcTwoNinths.ExteriorE1.det2 x (z - n • x) = _root_.AbcTwoNinths.ExteriorE1.det2 x z := by
      change x.1 * (z.2 - n * x.2) - x.2 * (z.1 - n * x.1) = x.1 * z.2 - x.2 * z.1
      ring
    have h := htrans _ (he.symm ▸ hdz)
    rw [hf, hf]
    convert h using 2
    apply Prod.ext <;> simp [_root_.AbcTwoNinths.ExteriorE1.realPair]
  let a : ℤ := d * z.2
  let b : ℤ := -d * x.2
  let c : ℝ := (d : ℝ) * ((z.2 : ℝ) * p - z.1)
  let e : ℝ := (d : ℝ) * (-(x.2 : ℝ) * p + x.1)
  have hwa : ((1 : ℝ), 0) = (a : ℝ) • _root_.AbcTwoNinths.ExteriorE1.realPair x + (b : ℝ) • _root_.AbcTwoNinths.ExteriorE1.realPair z := by
    simpa [a, b] using _root_.AbcTwoNinths.ExteriorE1.coordinateInverse x z d hdd 1 0
  have hya : (p, (1 : ℝ)) = c • _root_.AbcTwoNinths.ExteriorE1.realPair x + e • _root_.AbcTwoNinths.ExteriorE1.realPair z := by
    simpa [c, e] using _root_.AbcTwoNinths.ExteriorE1.coordinateInverse x z d hdd p 1
  have hd' : (d : ℝ) * ((x.1 : ℝ) * (z.2 : ℝ) - (x.2 : ℝ) * (z.1 : ℝ)) = 1 := by
    exact_mod_cast hdd
  have hab : (a : ℝ) * e - (b : ℝ) * c = (d : ℝ) := by
    push_cast [a, b, c, e]
    linear_combination (d : ℝ) * hd'
  have hab' : (a : ℝ) * e - (b : ℝ) * c = 1 ∨ (a : ℝ) * e - (b : ℝ) * c = -1 := by
    rw [hab]
    exact hsign.imp (by intro h; exact_mod_cast h) (by intro h; exact_mod_cast h)
  have hint : ((1 : ℤ), 0) = a • x + b • z := by
    apply Prod.ext
    · have := congrArg Prod.fst hwa
      simp only [_root_.AbcTwoNinths.ExteriorE1.realPair, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      exact_mod_cast this
    · have := congrArg Prod.snd hwa
      simp only [_root_.AbcTwoNinths.ExteriorE1.realPair, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
      exact_mod_cast this
  refine ⟨x, z, a, b, hd, hint, hp _ hrx, hp _ hrz, ?_⟩
  exact _root_.AbcTwoNinths.ExteriorE1.reducedBasisBounds f _ _ _ _ _ _ _ _ _ _ hwa hya hab' ht hclose hqmin hshort
    (by simpa only [hf] using hmin z hz)

end

end AbcTwoNinths.ExteriorE1
