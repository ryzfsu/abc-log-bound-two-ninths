/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Real Interpolation Zero Estimate

The module transfers a nonzero minor to the real matrix and proves the real interpolation zero estimate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realInterpolationZeroEstimate`
-/

@[expose] public section

namespace AbcTwoNinths.ExteriorE1

section



/-- A field homomorphism preserves nonvanishing of a determinant. -/
theorem mapMatrixDetNeZero {I F K : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Field K] (f : F →+* K) (Q : Matrix I I F) (hQ : Q.det ≠ 0) :
    (Q.map f).det ≠ 0 := by
  change (f.mapMatrix Q).det ≠ 0
  rw [← RingHom.map_det]
  simpa only [map_zero] using f.injective.ne hQ

/--
Two grid-image cardinality bounds give a nonzero maximal minor of the real binomial interpolation matrix. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realInterpolationZeroEstimate
    {R S R' S' L J b₁ b₂ : ℕ} (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : L ≤ (Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeW (R := R) (S := S) a b)).card)
    (h₂ : L * J <
      (Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') b₁ b₂)).card) :
    let M : Matrix (Fin (J+1) × Fin L) (_root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S')) ℝ :=
      Matrix.of fun k d => (Nat.choose (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ d) k.1.val : ℝ) *
        ((a : ℝ) ^ d.1.val * (b : ℝ) ^ d.2.val) ^ k.2.val
    ∃ f : (Fin (J+1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S'),
      (M.submatrix id f).det ≠ 0 := by
  classical
  let A := Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeW (R := R) (S := S) a b)
  let B := Finset.univ.image (_root_.AbcTwoNinths.Basic.nodeZ (R := R') (S := S') b₁ b₂)
  have liftA (y : A) : ∃ x : _root_.AbcTwoNinths.Basic.Rectangle R S, _root_.AbcTwoNinths.Basic.nodeW a b x = (y : ℚ) := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp y.property
    exact ⟨x, hx⟩
  have liftB (y : B) : ∃ x : _root_.AbcTwoNinths.Basic.Rectangle R' S', _root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ x = (y : ℕ) := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp y.property
    exact ⟨x, hx⟩
  choose u hu using liftA
  choose v hv using liftB
  have hc : L ≤ Fintype.card A := by simpa using h₁
  let e : Fin L ↪ A := (Fin.castLEEmb hc).trans (Fintype.equivFin A).symm.toEmbedding
  have hAi : Function.Injective (fun i => _root_.AbcTwoNinths.Basic.nodeW a b (u (e i))) := by
    intro i j h
    exact e.injective (Subtype.ext (by simpa only [hu] using h))
  have hBi : Function.Injective (fun i => _root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (v i)) := by
    intro i j h
    exact Subtype.ext (by simpa only [hv] using h)
  obtain ⟨f, hf⟩ := _root_.AbcTwoNinths.Basic.gridBinomialMinor (J := J)
    (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂) (_root_.AbcTwoNinths.Basic.nodeW a b)
    (fun i => _root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (u (e i))) (fun i => _root_.AbcTwoNinths.Basic.nodeW a b (u (e i)))
    (fun i => _root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (v i)) (fun i => _root_.AbcTwoNinths.Basic.nodeW a b (v i)) hAi hBi
    (fun i => mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
    (by simpa using h₂) (fun i j => _root_.AbcTwoNinths.Basic.addNode (u (e i)) (v j))
    (by intro i j; simp [_root_.AbcTwoNinths.Basic.nodeZ, _root_.AbcTwoNinths.Basic.addNode, add_mul]; omega)
    (by intro i j; simp [_root_.AbcTwoNinths.Basic.nodeW, _root_.AbcTwoNinths.Basic.addNode, pow_add]; ring)
  let Q : Matrix (Fin (J+1) × Fin L) (Fin (J+1) × Fin L) ℚ :=
    Matrix.of fun k j => (Nat.choose (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ (f j)) k.1.val : ℚ) *
      _root_.AbcTwoNinths.Basic.nodeW a b (f j) ^ k.2.val
  have hQ : Q.det ≠ 0 := hf
  refine ⟨f, ?_⟩
  have hcast : (Matrix.of fun k d => (Nat.choose (_root_.AbcTwoNinths.Basic.nodeZ b₁ b₂ d) k.1.val : ℝ) *
      ((a : ℝ) ^ d.1.val * (b : ℝ) ^ d.2.val) ^ k.2.val :
      Matrix (Fin (J+1) × Fin L) (_root_.AbcTwoNinths.Basic.Rectangle (R+R') (S+S')) ℝ).submatrix id f =
      Q.map (Rat.castHom ℝ) := by
    ext k j
    simp [Q, _root_.AbcTwoNinths.Basic.nodeW]
  rw [hcast]
  exact _root_.AbcTwoNinths.ExteriorE1.mapMatrixDetNeZero (Rat.castHom ℝ) Q hQ

end

end AbcTwoNinths.ExteriorE1
