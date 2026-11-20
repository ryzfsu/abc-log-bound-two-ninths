/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic

/-!
# Roof Covolume

Eliminating a nonzero pivot divides the absolute determinant by the absolute pivot. The residue
image has cardinality equal to the absolute determinant of an integral basis of the kernel.

## Main results
* `AbcTwoNinths.Basic.absProject`
* `AbcTwoNinths.Basic.indexOld`
-/

@[expose] public section
namespace AbcTwoNinths.Basic

noncomputable section
section

open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Assemble a matrix with a distinguished scalar pivot, its row and column tails, and the remaining square block.
-/
def roofBlock {R : Type*} (k : R) (v c : ι → R) (Y : Matrix ι ι R) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (fun _ _ => k) (fun _ j => v j) (fun i _ => c i) Y

/--
Eliminate the pivot coordinate from each row by subtracting the corresponding multiple of the pivot row.
-/
def projectRows (k : ℝ) (v c : ι → ℝ) (Y : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => Y i j - c i / k * v j

/--
A nonzero pivot times the determinant of the projected rows equals the determinant of the block matrix.
-/
theorem detRoof (k : ℝ) (hk : k ≠ 0) (v c : ι → ℝ) (Y : Matrix ι ι ℝ) :
    (_root_.AbcTwoNinths.Basic.roofBlock k v c Y).det = k * (_root_.AbcTwoNinths.Basic.projectRows k v c Y).det := by
  let K : Matrix Unit Unit ℝ := fun _ _ => k
  let V : Matrix Unit ι ℝ := fun _ j => v j
  let C : Matrix ι Unit ℝ := fun i _ => c i
  let T : Matrix ι Unit ℝ := fun i _ => c i / k
  have hTK : T * K = C := by
    ext i j
    rw [Matrix.mul_apply]
    simp [T, K, C, hk]
  have hP : T * V + _root_.AbcTwoNinths.Basic.projectRows k v c Y = Y := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply]
    simp [T, V, _root_.AbcTwoNinths.Basic.projectRows]
  have factor : _root_.AbcTwoNinths.Basic.roofBlock k v c Y =
      (Matrix.fromBlocks 1 0 T 1) * (Matrix.fromBlocks K V 0 (_root_.AbcTwoNinths.Basic.projectRows k v c Y)) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, hTK, hP]
    rfl
  rw [factor, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique K]
  simp [K]

/--
The absolute determinant of the projected rows equals the absolute block determinant divided by the absolute pivot.
-/
theorem absProject (k : ℝ) (hk : k ≠ 0) (v c : ι → ℝ) (Y : Matrix ι ι ℝ) :
    |(_root_.AbcTwoNinths.Basic.projectRows k v c Y).det| = |(_root_.AbcTwoNinths.Basic.roofBlock k v c Y).det| / |k| := by
  rw [_root_.AbcTwoNinths.Basic.detRoof k hk, abs_mul]
  field_simp

/--
The cardinality of the residue image equals the absolute integer determinant of a basis of its kernel.
-/
theorem indexOld {G : Type*} [AddGroup G] (r : ((Unit ⊕ ι) → ℤ) →+ G)
    (b : Basis (Unit ⊕ ι) ℤ r.ker) :
    Nat.card r.range = (Matrix.of (fun i => (b i : (Unit ⊕ ι) → ℤ))).det.natAbs := by
  rw [← AddSubgroup.index_ker, AddSubgroup.index_eq_natAbs_det
    (Pi.basisFun ℤ (Unit ⊕ ι)) r.ker b, Pi.basisFun_det_apply]

/--
The integer-linear map subtracting the pivot multiple from the remaining exponent coordinates.
-/
def roofProjection (k : ℤ) (v : ι → ℤ) : ((Unit ⊕ ι) → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun x j := (x (.inr j) : ℝ) - (x (.inl ()) : ℝ) / k * (v j : ℝ)
  map_add' x y := by ext j; simp; ring
  map_smul' a x := by ext j; simp; ring

end
end

end AbcTwoNinths.Basic
