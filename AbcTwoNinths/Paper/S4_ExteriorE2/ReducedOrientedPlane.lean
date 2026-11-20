/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedContactExclusion
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositePrincipalUnits
public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimeLogarithmicBounds

/-!
# Reduced Oriented Plane

The module excludes an oriented source plane by applying the composite contact estimate to its monomials. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.excludeOrientedPlaneOnHigh`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real


/--
The rational height of the composite monomial in distinct primes equals the signed exponent height with logarithmic prime weights.
-/
theorem compositeMonomialHeight {I : Type*} [Fintype I] {B : ℕ}
    (q : I → ℕ) (hp : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (hq : Function.Injective q) (e : I → ℤ) :
    let r := (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hc (Multiplicative.ofAdd e)).val.val
    log (max (r.num.natAbs : ℝ) (r.den : ℝ)) =
      _root_.AbcTwoNinths.ExteriorE1.height (fun i => log (q i : ℝ)) (fun i => (e i : ℝ)) := by
  dsimp only
  rw [← Nat.cast_max]
  change _root_.AbcTwoNinths.Basic.rationalHeight _ = _
  rw [_root_.AbcTwoNinths.ExteriorE2.compositeMonomialRational]
  have heval : ((_root_.AbcTwoNinths.ExteriorE2.monomial q hp)
      (Multiplicative.ofAdd e) : ℚ) = _root_.AbcTwoNinths.PolyCap.prodMonomial q e := by
    simp [_root_.AbcTwoNinths.ExteriorE2.monomial, _root_.AbcTwoNinths.ExteriorE2.eval,
      _root_.AbcTwoNinths.ExteriorE2.ratUnit, _root_.AbcTwoNinths.PolyCap.prodMonomial,
      Units.val_zpow_eq_zpow_val]
  rw [heval]
  rw [(_root_.AbcTwoNinths.PolyCap.ratHeightProdMonomial q hp hq e).1]
  unfold _root_.AbcTwoNinths.ExteriorE1.height _root_.AbcTwoNinths.ExteriorE1.positiveWeight
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> simp only [Pi.neg_apply]
  · rw [mul_max_of_nonneg _ _ (Real.log_nonneg (by exact_mod_cast (hp i).one_le)), mul_zero, mul_comm]
  · rw [mul_max_of_nonneg _ _ (Real.log_nonneg (by exact_mod_cast (hp i).one_le)), mul_zero, mul_neg, mul_comm]

/--
The depth, mass, area, and logarithmic bounds exclude an independent oriented kernel plane with coprime positive coefficients.
-/
theorem excludeOrientedPlane {I : Type*} [Fintype I]
    {M c d L G : ℕ} {H x κ Q U Z : ℝ}
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime)
    (hcop : ∀ i, (q i).Coprime M) (hq : Function.Injective q)
    (V u z : Unit ⊕ I → ℤ)
    (hV : V = (c : ℤ) • u - (d : ℤ) • z)
    (huk : u ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker)
    (hzk : z ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker)
    (hind : ∀ m n : ℤ, m • u + n • z = 0 → m = 0 ∧ n = 0)
    (hdep : (M : ℤ) ^ (L - G) ∣ (↑(∏ i, q i ^ (V i).toNat) : ℤ) -
      (↑(∏ i, q i ^ (-V i).toNat) : ℤ))
    (hM : 3 ≤ M) (hH : 0 ≤ H) (hκ : 0 < κ) (hQ : 44236800 / κ ≤ Q)
    (hx : x ≤ 4 * log (M : ℝ)) (hmass : κ * H / 16 ≤ (L : ℝ) * log (M : ℝ))
    (harea : U * Z ≤ 24 * H * x / Q) (hL : 146 + 2 * (G : ℝ) ≤ L)
    (hu : log (M : ℝ) ≤ U) (hz : log (M : ℝ) ≤ Z)
    (hcd : c.Coprime d) (hc : 0 < c) (hd : 0 < d)
    (hlog : log ((d : ℝ) / (U / log (M : ℝ)) + (c : ℝ) / (Z / log (M : ℝ))) + 1 ≤
      15 * log (M : ℝ))
    (hhu : _root_.AbcTwoNinths.ExteriorE1.height (fun i => log (q i : ℝ)) (fun i => (u i : ℝ)) ≤ U)
    (hhz : _root_.AbcTwoNinths.ExteriorE1.height (fun i => log (q i : ℝ)) (fun i => (z i : ℝ)) ≤ Z) :
    False := by
  classical
  let f := _root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hp hcop
  let a := f (Multiplicative.ofAdd u)
  let b := f (Multiplicative.ofAdd z)
  refine _root_.AbcTwoNinths.ExteriorE2.excludeOrientedContact hM hH hκ hQ hx hmass harea hL hu hz a b
    (_root_.AbcTwoNinths.ExteriorE2.compositePrincipalOfKernel q hp hcop u huk)
    (_root_.AbcTwoNinths.ExteriorE2.compositePrincipalOfKernel q hp hcop z hzk) ?_ hcd hc hd hlog
    ((_root_.AbcTwoNinths.ExteriorE2.compositeMonomialHeight q hp hcop hq u).le.trans hhu)
    ((_root_.AbcTwoNinths.ExteriorE2.compositeMonomialHeight q hp hcop hq z).le.trans hhz)
    (_root_.AbcTwoNinths.ExteriorE2.compositeContactNumerator q hp hcop u z V hV hdep)
  · intro m n h
    apply _root_.AbcTwoNinths.ExteriorE2.monomialIndependent f (_root_.AbcTwoNinths.ExteriorE2.compositeMonomialInjective q hp hcop hq) u z hind m n
    let j := Units.map (Subring.subtype (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime M)).toMonoidHom
    apply (Units.map_injective (show Function.Injective (Subring.subtype (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime M)).toMonoidHom from Subtype.val_injective))
    change j (a ^ m * b ^ n) = j 1
    rw [map_mul, map_zpow, map_zpow, map_one]
    apply Units.ext
    simpa [j] using h



/--
On a high triple, the modulus and coordinate height bounds supply the logarithmic estimate excluding an oriented plane. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem excludeOrientedPlaneOnHigh {I : Type*} [Fintype I]
    {t : _root_.AbcTwoNinths.Basic.Triple} {η : ℚ} {X σ κ Q : ℝ} {M c d L G : ℕ}
    (q : Unit ⊕ I → ℕ) (hp : ∀ i, (q i).Prime)
    (hcop : ∀ i, (q i).Coprime M) (hq : Function.Injective q)
    (V u z : Unit ⊕ I → ℤ)
    (hV : V = (c : ℤ) • u - (d : ℤ) • z)
    (huk : u ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker)
    (hzk : z ∈ (_root_.AbcTwoNinths.ExteriorE2.monomialReduction M q hcop).ker)
    (hind : ∀ m n : ℤ, m • u + n • z = 0 → m = 0 ∧ n = 0)
    (hdep : (M : ℤ) ^ (L - G) ∣ (↑(∏ i, q i ^ (V i).toNat) : ℤ) -
      (↑(∏ i, q i ^ (-V i).toNat) : ℤ))
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hX : 0 ≤ X) (ht : _root_.AbcTwoNinths.Statement.High η X t)
    (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : 0 < κ)
    (hM : 3 ≤ M) (hQ : 44236800 / κ ≤ Q)
    (hx : t.thirdLogRadical ≤ 4 * log (M : ℝ))
    (hmass : κ * t.logHeight / 16 ≤ (L : ℝ) * log (M : ℝ))
    (hmod : (log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ log (M : ℝ))
    (hL : 146 + 2 * (G : ℝ) ≤ L)
    (hcd : c.Coprime d) (hc : 0 < c) (hd : 0 < d) :
    let ht' (e : Unit ⊕ I → ℤ) := _root_.AbcTwoNinths.ExteriorE1.height (fun i => log (q i : ℝ)) (fun i => (e i : ℝ))
    log (M : ℝ) ≤ ht' u → log (M : ℝ) ≤ ht' z →
    ht' V ≤ 2 * t.logHeight →
    ht' u * ht' z ≤ 24 * t.logHeight * t.thirdLogRadical / Q →
    (c : ℝ) * ht' u ≤ 3 * ht' V → (d : ℝ) * ht' z ≤ 2 * ht' V → False := by
  dsimp only
  intro hu hz hsource harea hcu hdz
  have hH := (Real.exp_pos _).trans_le ht.2
  have hl : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have ha : 1 ≤ _ / log (M : ℝ) := (le_div_iff₀ hl).2 (by simpa using hz)
  have hb : 1 ≤ _ / log (M : ℝ) := (le_div_iff₀ hl).2 (by simpa using hu)
  have hlog2 : log 2 ≤ log (M : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ M by omega))
  have hlog := _root_.AbcTwoNinths.ExteriorE2.nativeLogBudget hη hX ht hσ hM hmod ha hb
    (show 0 < c + d by omega) hH hsource (hlog2.trans hu) (hlog2.trans hz) hcu hdz
  exact _root_.AbcTwoNinths.ExteriorE2.excludeOrientedPlane q hp hcop hq V u z hV huk hzk hind hdep hM hH.le
    hκ hQ hx hmass harea hL hu hz hcd hc hd hlog le_rfl le_rfl

end

end AbcTwoNinths.ExteriorE2
