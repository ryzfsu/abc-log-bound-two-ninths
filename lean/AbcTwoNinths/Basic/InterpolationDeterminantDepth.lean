/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.CommonIndexLift
public import AbcTwoNinths.Basic.LocalInterpolationMatrix
public import AbcTwoNinths.Basic.PadicContact
public import AbcTwoNinths.Basic.RationalBinomialMinor

/-!
# Interpolation Determinant Depth

The module obtains a depth lower bound for an interpolation determinant with selected rows.

## Main results
* `AbcTwoNinths.Basic.actualDetDepth`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section


open scoped BigOperators

/--
A row of the rectangular interpolation matrix consists of a degree at most J and a level below L.
-/
abbrev Rows (J L : ℕ) := Fin (J+1) × Fin L

/--
The determinant depth exponent is the triangular degree of the full matrix less the sum of its row degrees.
-/
def Ejl (J L : ℕ) : ℕ :=
  ((J+1)*L)*((J+1)*L-1)/2 - L*((J+1)*J/2)

/-- The sum of the row degrees in the rectangular interpolation matrix is L times J(J+1)/2. -/
theorem rowSum (J L : ℕ) :
    (∑ i : _root_.AbcTwoNinths.Basic.Rows J L, i.1.val) = L*((J+1)*J/2) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun n : ℕ => n), Finset.sum_range_id]
  simp

/--
Contact of two coprime powers of principal units to the full row count forces their interpolation determinant to vanish modulo the stated prime power.
-/
theorem actualDetDepth (p J L c d : ℕ) [Fact p.Prime] (a b : ℚ)
    (hc : c.Coprime d) (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (hcontact : _root_.AbcTwoNinths.Basic.RatCongruent p ((J+1)*L) (a^c) (b^d))
    (r s : _root_.AbcTwoNinths.Basic.Rows J L → ℕ) :
    _root_.AbcTwoNinths.Basic.RatCongruent p (_root_.AbcTwoNinths.Basic.Ejl J L)
      (_root_.AbcTwoNinths.Basic.actualEntry a b (fun i => i.1.val) (fun i => i.2.val) r s c d).det 0 := by
  classical
  let I := _root_.AbcTwoNinths.Basic.Rows J L
  have hn : Fintype.card I = (J+1)*L := by simp [I]
  obtain ⟨g,hg,hgentry⟩ := _root_.AbcTwoNinths.Basic.gridCommonLift p c d ((J+1)*L) a b Fact.out hc ha hb hcontact
  let A := _root_.AbcTwoNinths.Basic.actualEntry a b (fun i : I => i.1.val) (fun i => i.2.val) r s c d
  let z (j : I) := r j*d+s j*c
  have hA (i j : I) : _root_.AbcTwoNinths.Basic.IntegralAt p (A i j) :=
    _root_.AbcTwoNinths.Basic.integralMul (_root_.AbcTwoNinths.Basic.integralMul (_root_.AbcTwoNinths.Basic.integralNat p _)
      (_root_.AbcTwoNinths.Basic.integralPow (le_of_eq ha.2.1.symm) _)) (_root_.AbcTwoNinths.Basic.integralPow (le_of_eq hb.2.1.symm) _)
  let B : Matrix I I (_root_.AbcTwoNinths.Basic.localRing p) := fun i j => _root_.AbcTwoNinths.Basic.localRat p (A i j) (hA i j)
  let F : Matrix I I (_root_.AbcTwoNinths.Basic.localRing p) := fun i j =>
    (Nat.choose (z j) i.1.val : _root_.AbcTwoNinths.Basic.localRing p) * (g : _root_.AbcTwoNinths.Basic.localRing p)^(i.2.val*z j)
  have he (i j : I) : (p : _root_.AbcTwoNinths.Basic.localRing p)^Fintype.card I ∣ (B-F) i j := by
    apply _root_.AbcTwoNinths.Basic.localErrorDvd
    rw [hn]
    exact hgentry (i.1.val,i.2.val) (r j,s j)
  have hgp : (p : _root_.AbcTwoNinths.Basic.localRing p) ∣ (g : _root_.AbcTwoNinths.Basic.localRing p) - 1 := by
    have hz : (g : ZMod p) = 1 := by
      apply ZMod.val_injective p
      simpa [ZMod.val_natCast, ZMod.val_one, (Fact.out : p.Prime).one_lt] using hg
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd ((g : ℤ)-1) p).mp (by push_cast; simp [hz])
    simpa using map_dvd (Int.castRingHom (_root_.AbcTwoNinths.Basic.localRing p)) hd
  have hE : _root_.AbcTwoNinths.Basic.Ejl J L + (∑ i : I, i.1.val) ≤ Fintype.card I * (Fintype.card I-1)/2 := by
    rw [hn, _root_.AbcTwoNinths.Basic.rowSum]
    unfold _root_.AbcTwoNinths.Basic.Ejl
    have hle : L*((J+1)*J/2) ≤ ((J+1)*L)*((J+1)*L-1)/2 := by
      cases L with
      | zero => simp
      | succ L =>
        have hb : J+1 ≤ (J+1)*(L+1) := by
          exact (Nat.mul_one (J+1)).symm.le.trans
            (Nat.mul_le_mul_left (J+1) (Nat.succ_le_succ (Nat.zero_le L)))
        have hX : J ≤ (J+1)*(L+1)-1 := by omega
        have h₂ := Nat.mul_le_mul_left ((J+1)*(L+1)) hX
        have h₃ : (L+1)*((J+1)*J/2)*2 ≤ ((J+1)*(L+1))*J := by
          rw [Nat.mul_assoc]
          calc
            _ ≤ (L+1)*((J+1)*J) := Nat.mul_le_mul_left _ (by omega)
            _ = _ := by ring
        omega
    omega
  have h := _root_.AbcTwoNinths.Basic.newtonMatrixDvd (p : _root_.AbcTwoNinths.Basic.localRing p) (g : _root_.AbcTwoNinths.Basic.localRing p)
    hgp (_root_.AbcTwoNinths.Basic.Ejl J L) 1 (fun i : I => i.1.val) (fun i => i.2.val) z (B-F) he hE
  simp only [one_mul] at h
  change (p : _root_.AbcTwoNinths.Basic.localRing p)^_root_.AbcTwoNinths.Basic.Ejl J L ∣ Matrix.det (fun i j => F i j+(B-F) i j) at h
  have hmat : (fun i j => F i j+(B-F) i j : Matrix I I (_root_.AbcTwoNinths.Basic.localRing p)) = B := by
    ext i j
    simp [Matrix.sub_apply]
  rw [hmat] at h
  have hh := (_root_.AbcTwoNinths.Basic.localDvdIff B.det).mp h
  have hbA : (_root_.AbcTwoNinths.Basic.localRing p).subtype.mapMatrix B = A := by ext i j; rfl
  have hdet : B.det.val = A.det := by
    change (_root_.AbcTwoNinths.Basic.localRing p).subtype B.det = A.det
    rw [RingHom.map_det, hbA]
  rwa [hdet] at hh

end

end AbcTwoNinths.Basic
