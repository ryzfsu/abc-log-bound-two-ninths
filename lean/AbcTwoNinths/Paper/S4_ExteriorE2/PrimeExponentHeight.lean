/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison
public import AbcTwoNinths.Paper.S4_ExteriorE2.GeneratorDepthAndMultiplicity
public import AbcTwoNinths.Paper.S4_ExteriorE2.KernelLine

/-!
# Prime Exponent Height

The module computes prime-exponent heights and constructs a kernel generator with a logarithmic height lower bound. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.generatorOfKernel`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real




/--
The weighted height of an exponent vector uses the logarithms of its bases as weights. This is used in the proof of Proposition 4.1 of the paper.
-/
noncomputable def weightedHeight {J : Type*} [Fintype J] (q : J → ℕ) (e : J → ℤ) : ℝ :=
  _root_.AbcTwoNinths.ExteriorE1.height (fun i => log (q i : ℝ)) (fun i => (e i : ℝ))

/--
For prime bases, the weighted height is the larger logarithm of the positive and negative monomial parts.
-/
theorem weightedHeightEqLogParts {J : Type*} [Fintype J]
    (q : J → ℕ) (hp : ∀ i, (q i).Prime) (e : J → ℤ) :
    _root_.AbcTwoNinths.ExteriorE2.weightedHeight q e = max (log (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℝ)) (log (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℝ)) := by
  have hlog (v : J → ℤ) :
      log (_root_.AbcTwoNinths.PolyCap.posPartNat q v : ℝ) = _root_.AbcTwoNinths.ExteriorE1.positiveWeight (fun i => log (q i : ℝ))
          (fun i => (v i : ℝ)) := by
    unfold _root_.AbcTwoNinths.PolyCap.posPartNat _root_.AbcTwoNinths.ExteriorE1.positiveWeight
    simp only [Nat.cast_prod, Nat.cast_pow]
    rw [log_prod (fun i _ => pow_ne_zero _ (by exact_mod_cast (hp i).ne_zero))]
    apply Finset.sum_congr rfl
    intro i _
    rw [log_pow, mul_comm]
    congr 1
    by_cases hi : 0 ≤ v i
    · rw [max_eq_left (by exact_mod_cast hi)]
      exact_mod_cast Int.toNat_of_nonneg hi
    · rw [max_eq_right (by exact_mod_cast le_of_not_ge hi),
        Int.toNat_eq_zero.mpr (le_of_not_ge hi), Nat.cast_zero]
  unfold _root_.AbcTwoNinths.ExteriorE2.weightedHeight _root_.AbcTwoNinths.ExteriorE1.height _root_.AbcTwoNinths.PolyCap.negPartNat
  rw [hlog, hlog]
  simp only [Pi.neg_def, Int.cast_neg]

private theorem weightedHeightNsmul {J : Type*} [Fintype J]
    (q : J → ℕ) (hp : ∀ i, (q i).Prime) (e : J → ℤ) (g : ℕ) :
    _root_.AbcTwoNinths.ExteriorE2.weightedHeight q (g • e) = (g : ℝ) * _root_.AbcTwoNinths.ExteriorE2.weightedHeight q e := by
  obtain ⟨hpos, hneg⟩ := _root_.AbcTwoNinths.ExteriorE2.partsNsmul q e g
  rw [_root_.AbcTwoNinths.ExteriorE2.weightedHeightEqLogParts q hp, _root_.AbcTwoNinths.ExteriorE2.weightedHeightEqLogParts q hp,
    hpos, hneg, Nat.cast_pow, Nat.cast_pow, log_pow, log_pow, mul_max_of_nonneg _ _ (by positivity)]

/--
A nonzero kernel vector on distinct prime bases coprime to the modulus has weighted height greater than its logarithm.
-/
theorem kernelWeightedHeightGtLog {I : Type*} [Fintype I] {M : ℕ}
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime) (hcop : ∀ i, (q i).Coprime M)
    (hq : Function.Injective q) (hM : 2 ≤ M) (e : Unit ⊕ I → ℤ)
    (he : e ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker) (hne : e ≠ 0) :
    log (M : ℝ) < _root_.AbcTwoNinths.ExteriorE2.weightedHeight q e := by
  rw [_root_.AbcTwoNinths.ExteriorE2.weightedHeightEqLogParts q hp]
  exact _root_.AbcTwoNinths.ExteriorE2.kernelHeightGtLog M hM q hp hq hcop e he hne

/--
A positive-pivot kernel vector with sufficient divisibility and mass has a line generator with controlled multiplicity, depth and height. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem generatorOfKernel {I : Type*} [Fintype I] {M L : ℕ} {H κ : ℝ}
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime) (hcop : ∀ i, (q i).Coprime M)
    (hq : Function.Injective q) (E : Unit ⊕ I → ℤ) (hEpivot : 0 < E (.inl ()))
    (hEk : E ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker) (hM : 2 ≤ M)
    (hpar : ¬ 2 ∣ M ∨ 4 ∣ M)
    (hdepth : (M : ℤ) ^ L ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q E : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q E : ℤ))
    (hH : 0 < H) (hκ : 0 < κ) (hmass : κ * H / 16 ≤ (L : ℝ) * log (M : ℝ))
    (hheight : _root_.AbcTwoNinths.ExteriorE2.weightedHeight q E ≤ 2 * H)
    (honset : 4 / (κ / 16) * log (8 / ((κ / 16) * log 2)) ≤ H) :
    ∃ (V : Unit ⊕ I → ℤ) (g : ℕ), 0 < g ∧ 0 < V (.inl ()) ∧
      V ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker ∧ E = g • V ∧
      (∀ z ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker,
        _root_.AbcTwoNinths.Basic.roofProjection (V (.inl ())) (fun i => V (.inr i)) z = 0 →
        ∃ n : ℤ, z = n • V) ∧
      (g : ℝ) ≤ 64 / κ ∧
      (M : ℤ) ^ (L - Nat.log 2 g) ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q V : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q V : ℤ) ∧
      (L : ℝ) * log (M : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V + log (g : ℝ) ∧
      (g : ℝ) * _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V ≤ 2 * H ∧ _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V ≤ 2 * H ∧
      log (M : ℝ) < _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V := by
  let r := _root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop
  have hshape : Sum.elim (fun _ : Unit => E (.inl ())) (fun i => E (.inr i)) = E := by
    funext i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  obtain ⟨p, w, m, hpivot, hm, hV, hE, hline⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.kernelRoofGenerator r hEpivot (fun i => E (.inr i)) (hshape.symm ▸ hEk)
  let V : Unit ⊕ I → ℤ := Sum.elim (fun _ => p) w
  let g := m.toNat
  have hg : 0 < g := by dsimp [g]; omega
  have hEg : E = g • V := by
    rw [hshape] at hE
    have hm' : (g : ℤ) = m := Int.toNat_of_nonneg hm.le
    rw [← hm', natCast_zsmul] at hE
    exact hE
  have hVne : V ≠ 0 := by
    intro h
    have hz : p = 0 := congrFun h (.inl ())
    exact hpivot.ne' hz
  have hfloor := _root_.AbcTwoNinths.ExteriorE2.kernelWeightedHeightGtLog q hp hcop hq hM V hV hVne
  have hVpos : 0 < _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V :=
    (log_pos (by exact_mod_cast (show 1 < M by omega))).trans hfloor
  have hroot : (g : ℝ) * _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V ≤ 2 * H := by
    rwa [hEg, weightedHeightNsmul q hp] at hheight
  have hbound : _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V ≤ 2 * H := by
    exact (le_mul_of_one_le_left hVpos.le (by exact_mod_cast hg)).trans hroot
  have hdepthV : (M : ℤ) ^ L ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q (g • V) : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q (g • V) : ℤ) :=
    hEg ▸ hdepth
  have hne : _root_.AbcTwoNinths.PolyCap.posPartNat q V ≠ _root_.AbcTwoNinths.PolyCap.negPartNat q V := by
    obtain ⟨_, hn, _, hrat, _, _⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime q hp hq V
    intro heq
    apply hVne
    have hqne : (_root_.AbcTwoNinths.PolyCap.negPartNat q V : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hone : _root_.AbcTwoNinths.PolyCap.prodMonomial q V = 1 := by rw [hrat, heq, div_self hqne]
    exact funext ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff q hp hq V).1 hone)
  have descend (a : Unit ⊕ I → ℤ) (ha : a ∈ r.ker)
      (hlt : _root_.AbcTwoNinths.PolyCap.negPartNat q a < _root_.AbcTwoNinths.PolyCap.posPartNat q a)
      (hbase : (M : ℤ) ^ L ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q (g • a) : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q (g • a) : ℤ))
      (hscale : (g : ℝ) * _root_.AbcTwoNinths.ExteriorE2.weightedHeight q a ≤ 2 * H) :
      (M : ℤ) ^ (L - Nat.log 2 g) ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q a : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q a : ℤ) ∧
      (L : ℝ) * log (M : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.weightedHeight q a + log (g : ℝ) ∧ (g : ℝ) ≤ 64 / κ := by
    obtain ⟨hpos, hneg⟩ := _root_.AbcTwoNinths.ExteriorE2.partsNsmul q a g
    have hpowers : _root_.AbcTwoNinths.PolyCap.negPartNat q (g • a) ≤ _root_.AbcTwoNinths.PolyCap.posPartNat q (g • a) := by
      rw [hpos, hneg]
      exact Nat.pow_le_pow_left hlt.le g
    have hbaseNat : M ^ L ∣ _root_.AbcTwoNinths.PolyCap.posPartNat q (g • a) - _root_.AbcTwoNinths.PolyCap.negPartNat q (g • a) := by
      rw [← Int.ofNat_sub hpowers, ← Int.natCast_pow] at hbase
      exact_mod_cast hbase
    have hlog_le : log (_root_.AbcTwoNinths.PolyCap.posPartNat q a : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.weightedHeight q a := by
      rw [_root_.AbcTwoNinths.ExteriorE2.weightedHeightEqLogParts q hp]
      exact le_max_left _ _
    have hθ : 0 < κ / 16 := by positivity
    have hshare : κ / 16 * H ≤ (L : ℝ) * log (M : ℝ) := by
      simpa [div_mul_eq_mul_div] using hmass
    have hscaled := (mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ (g : ℝ))).trans hscale
    obtain ⟨hd, hl, hg'⟩ := _root_.AbcTwoNinths.ExteriorE2.generatorKernelDepthAndMultiplicity q hcop a ha
      hM hg hlt hpar hbaseNat hH hθ hshare hscaled honset
    refine ⟨?_, hl.trans (add_le_add hlog_le le_rfl), ?_⟩
    · rw [← Int.ofNat_sub hlt.le, ← Int.natCast_pow]
      exact_mod_cast hd
    · norm_num [div_div_eq_mul_div] at hg'
      exact hg'
  have hnegHeight : _root_.AbcTwoNinths.ExteriorE2.weightedHeight q (-V) = _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V := by
    simp [_root_.AbcTwoNinths.ExteriorE2.weightedHeightEqLogParts q hp, _root_.AbcTwoNinths.PolyCap.negPartNat, max_comm]
  have hresult :
      (M : ℤ) ^ (L - Nat.log 2 g) ∣ (_root_.AbcTwoNinths.PolyCap.posPartNat q V : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q V : ℤ) ∧
      (L : ℝ) * log (M : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.weightedHeight q V + log (g : ℝ) ∧ (g : ℝ) ≤ 64 / κ := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hdepthNeg : (M : ℤ) ^ L ∣
          (_root_.AbcTwoNinths.PolyCap.posPartNat q (g • (-V)) : ℤ) - (_root_.AbcTwoNinths.PolyCap.negPartNat q (g • (-V)) : ℤ) := by
        simpa [smul_neg, _root_.AbcTwoNinths.PolyCap.negPartNat, neg_sub] using dvd_neg.mpr hdepthV
      obtain ⟨hd, hl, hg'⟩ := descend (-V) (r.ker.neg_mem hV)
        (by simpa [_root_.AbcTwoNinths.PolyCap.negPartNat] using h) hdepthNeg (by rwa [hnegHeight])
      refine ⟨?_, hnegHeight ▸ hl, hg'⟩
      simpa [_root_.AbcTwoNinths.PolyCap.negPartNat, neg_sub] using dvd_neg.mpr hd
    · exact descend V hV h hdepthV hroot
  obtain ⟨hd, hl, hg'⟩ := hresult
  exact ⟨V, g, hg, hpivot, hV, hEg, hline, hg', hd, hl, hroot, hbound, hfloor⟩

end

end AbcTwoNinths.ExteriorE2
