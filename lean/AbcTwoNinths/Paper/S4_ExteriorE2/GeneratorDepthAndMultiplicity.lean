/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueParts
public import AbcTwoNinths.Paper.S4_ExteriorE2.PartPowers
public import AbcTwoNinths.Basic.TwoBasePowerValuation
public import AbcTwoNinths.Paper.S4_ExteriorE2.NativeMultiplicity
public import AbcTwoNinths.Paper.S4_ExteriorE2.InterpolationGridMargin

/-!
# Generator depth and multiplicity

The module bounds the height, depth, and exponent multiplicity of a generator in the cutoff residue kernel. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.generatorKernelDepthAndMultiplicity`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
A modulus dividing the positive difference of two positive integers has logarithm below that of the larger integer.
-/
theorem kernelPartHeightGtLog {A D M : ℕ}
    (hD : 0 < D) (hlt : D < A) (hM : 2 ≤ M) (hdiv : M ∣ A - D) :
    Real.log (M : ℝ) < Real.log (A : ℝ) := by
  have hs := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdiv
  apply Real.log_lt_log (by exact_mod_cast (show 0 < M by omega))
  exact_mod_cast (show M < A by omega)

/--
The larger logarithmic part of a nonzero prime-exponent vector in the reduction kernel exceeds the logarithm of the modulus.
-/
theorem kernelHeightGtLog {I : Type*} [Fintype I] (M : ℕ) (hM : 2 ≤ M)
    (q : Unit ⊕ I → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hc : ∀ i, (q i).Coprime M) (e : Unit ⊕ I → ℤ)
    (he : e ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker) (hne : e ≠ 0) :
    Real.log (M : ℝ) <
      max (Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q e : ℝ)) (Real.log (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℝ)) := by
  obtain ⟨hp, hd, _, hratio, _, _⟩ := _root_.AbcTwoNinths.PolyCap.prodMonomialEqDivCoprime q hq hinj e
  have hnd : _root_.AbcTwoNinths.PolyCap.posPartNat q e ≠ _root_.AbcTwoNinths.PolyCap.negPartNat q e := by
    intro h
    apply hne
    have hqne : (_root_.AbcTwoNinths.PolyCap.negPartNat q e : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hprod : _root_.AbcTwoNinths.PolyCap.prodMonomial q e = 1 := by rw [hratio, h, div_self hqne]
    exact funext ((_root_.AbcTwoNinths.PolyCap.prodMonomialEqOneIff q hq hinj e).1 hprod)
  rcases lt_or_gt_of_ne hnd with hlt | hlt
  · have hen : -e ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker :=
      (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker.neg_mem he
    have hdiv := (_root_.AbcTwoNinths.ExteriorE2.kernelIffDiffDvd M q hc (-e)
      (A := _root_.AbcTwoNinths.PolyCap.negPartNat q e) (D := _root_.AbcTwoNinths.PolyCap.posPartNat q e)
      (by simp [_root_.AbcTwoNinths.PolyCap.negPartNat, _root_.AbcTwoNinths.PolyCap.posPartNat]) (by simp [_root_.AbcTwoNinths.PolyCap.posPartNat]) hlt.le).1 hen
    exact (_root_.AbcTwoNinths.ExteriorE2.kernelPartHeightGtLog hp hlt hM hdiv).trans_le (le_max_right _ _)
  · have hdiv := (_root_.AbcTwoNinths.ExteriorE2.kernelIffDiffDvd M q hc e
      (A := _root_.AbcTwoNinths.PolyCap.posPartNat q e) (D := _root_.AbcTwoNinths.PolyCap.negPartNat q e) rfl rfl hlt.le).1 he
    exact (_root_.AbcTwoNinths.ExteriorE2.kernelPartHeightGtLog hd hlt hM hdiv).trans_le (le_max_left _ _)

/--
Removing a positive factor g from a multiple of a modulus power costs at most floor(log₂ g) powers.
-/
theorem generatorDepthLoss {M L n g : ℕ} (hM : M ≠ 0) (hn : n ≠ 0)
    (hg : g ≠ 0) (h : M ^ L ∣ n * g) :
    M ^ (L - Nat.log 2 g) ∣ n := by
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ hM) hn).1
  intro p
  have hfac := (Nat.factorization_le_iff_dvd (pow_ne_zero L hM)
    (mul_ne_zero hn hg)).2 h p
  rw [Nat.factorization_mul hn hg] at hfac
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.add_apply] at hfac ⊢
  by_cases hp : M.factorization p = 0
  · simp [hp]
  · have hgp : g.factorization p ≤ Nat.log 2 g := by
      by_cases hprime : p.Prime
      · rw [Nat.factorization_def g hprime]
        exact (padicValNat_le_nat_log g).trans
          (Nat.log_antitone_left (by norm_num) hprime.one_lt hprime.two_le)
      · simp [Nat.factorization_eq_zero_of_not_prime g hprime]
    have hpg : Nat.log 2 g ≤ Nat.log 2 g * M.factorization p := by
      simpa using Nat.mul_le_mul_left (Nat.log 2 g) (show 1 ≤ M.factorization p by omega)
    by_cases hLg : Nat.log 2 g ≤ L
    · rw [Nat.sub_mul]
      omega
    · simp [Nat.sub_eq_zero_of_le (by omega : L ≤ Nat.log 2 g)]

/--
Divisibility of a power difference and the height hypotheses bound the base difference's depth loss, the logarithmic depth and the multiplicity.
-/
theorem generatorDepthAndMultiplicity {M L A D g : ℕ} {H θ : ℝ}
    (hM : 2 ≤ M) (hDA : D < A) (hg : 0 < g)
    (hunit : A.Coprime M) (hprincipal : M ∣ A - D)
    (hpar : ¬ 2 ∣ M ∨ 4 ∣ M) (hdepth : M ^ L ∣ A ^ g - D ^ g)
    (hH : 0 < H) (hθ : 0 < θ)
    (hshare : θ * H ≤ (L : ℝ) * Real.log (M : ℝ))
    (hroot : (g : ℝ) * Real.log (A : ℝ) ≤ 2 * H)
    (honset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H) :
    M ^ (L - Nat.log 2 g) ∣ A - D ∧
    (L : ℝ) * Real.log (M : ℝ) ≤ Real.log (A : ℝ) + Real.log (g : ℝ) ∧
    (g : ℝ) ≤ 4 / θ := by
  have hs : 0 < A - D := Nat.sub_pos_of_lt hDA
  have hsR : 0 < ((A - D : ℕ) : ℝ) := by exact_mod_cast hs
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hg
  have hd := _root_.AbcTwoNinths.Basic.twoBaseDepthProduct (show M ≠ 0 by omega) hDA hg.ne'
    hunit hprincipal (fun h => hpar.elim (fun hn => (hn h).elim)
      (fun h4 => h4.trans hprincipal)) hdepth
  have hl := Real.log_le_log (by positivity : 0 < (M : ℝ)^L)
    (by exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hs hg) hd :
      (M : ℝ)^L ≤ ((A - D : ℕ) : ℝ) * g)
  rw [Real.log_pow, Real.log_mul hsR.ne' hgR.ne'] at hl
  have hla := Real.log_le_log hsR
    (by exact_mod_cast Nat.sub_le A D : ((A - D : ℕ) : ℝ) ≤ A)
  have hlte : (L : ℝ) * Real.log (M : ℝ) ≤ Real.log (A : ℝ) + Real.log (g : ℝ) := by
    linarith
  have htwo := hM.trans ((Nat.le_of_dvd hs hprincipal).trans (Nat.sub_le A D))
  have hroot_lb : Real.log 2 ≤ Real.log (A : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast htwo)
  have hlog := _root_.AbcTwoNinths.ExteriorE2.logMultiplicityLeHalfShare
    (show 1 ≤ (g : ℝ) by exact_mod_cast hg) hH hθ
      ((mul_le_mul_of_nonneg_left hroot_lb hgR.le).trans hroot) honset
  refine ⟨_root_.AbcTwoNinths.ExteriorE2.generatorDepthLoss (show M ≠ 0 by omega) hs.ne' hg.ne' hd, hlte, ?_⟩
  exact (le_div_iff₀ hθ).2 (_root_.AbcTwoNinths.ExteriorE2.multiplicityOfRootBound hgR hH hshare hlte hroot hlog)

/--
For a generator in the reduction kernel, bounds the depth loss of its difference, the logarithmic depth and its multiplicity. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem generatorKernelDepthAndMultiplicity {I : Type*} [Fintype I]
    (q : Unit ⊕ I → ℕ) {M L g : ℕ} (hc : ∀ i, (q i).Coprime M)
    (V : Unit ⊕ I → ℤ) (hV : V ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hc).ker)
    (hM : 2 ≤ M) (hg : 0 < g) (hlt : _root_.AbcTwoNinths.PolyCap.negPartNat q V < _root_.AbcTwoNinths.PolyCap.posPartNat q V)
    (hpar : ¬ 2 ∣ M ∨ 4 ∣ M)
    (hdepth : M ^ L ∣ _root_.AbcTwoNinths.PolyCap.posPartNat q (g • V) - _root_.AbcTwoNinths.PolyCap.negPartNat q (g • V))
    {H θ : ℝ} (hH : 0 < H) (hθ : 0 < θ)
    (hshare : θ * H ≤ (L : ℝ) * Real.log (M : ℝ))
    (hroot : (g : ℝ) * Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q V : ℝ) ≤ 2 * H)
    (honset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H) :
    M ^ (L - Nat.log 2 g) ∣ _root_.AbcTwoNinths.PolyCap.posPartNat q V - _root_.AbcTwoNinths.PolyCap.negPartNat q V ∧
    (L : ℝ) * Real.log (M : ℝ) ≤
      Real.log (_root_.AbcTwoNinths.PolyCap.posPartNat q V : ℝ) + Real.log (g : ℝ) ∧
    (g : ℝ) ≤ 4 / θ := by
  have hprincipal := (_root_.AbcTwoNinths.ExteriorE2.kernelIffDiffDvd M q hc V
    (A := _root_.AbcTwoNinths.PolyCap.posPartNat q V) (D := _root_.AbcTwoNinths.PolyCap.negPartNat q V) rfl rfl hlt.le).1 hV
  have hunit : (_root_.AbcTwoNinths.PolyCap.posPartNat q V).Coprime M := by
    unfold _root_.AbcTwoNinths.PolyCap.posPartNat
    exact Nat.coprime_prod_left_iff.mpr fun i _ => (hc i).pow_left _
  obtain ⟨hp, hn⟩ := _root_.AbcTwoNinths.ExteriorE2.partsNsmul q V g
  rw [hp, hn] at hdepth
  exact _root_.AbcTwoNinths.ExteriorE2.generatorDepthAndMultiplicity hM hlt hg hunit hprincipal hpar hdepth
    hH hθ hshare hroot honset

end

end AbcTwoNinths.ExteriorE2
