/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalGridTransport

/-!
# Common Index Lift

The module uses Bezout coefficients to represent congruent powers by one common principal base.

## Main results
* `AbcTwoNinths.Basic.gridCommonLift`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

set_option autoImplicit false

/-- Rational congruence at a fixed prime and precision is transitive. -/
theorem congrTrans {p e : ℕ} [Fact p.Prime] {a b c : ℚ}
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (h' : _root_.AbcTwoNinths.Basic.RatCongruent p e b c) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e a c := by
  rcases h with rfl | h
  · exact h'
  rcases h' with rfl | h'
  · exact Or.inr h
  by_cases h0 : a = c
  · exact Or.inl h0
  right
  have he : (a-b)+(b-c) = a-c := by ring
  have hn : (a-b)+(b-c) ≠ 0 := by rw [he]; exact sub_ne_zero.mpr h0
  rw [← he]
  exact (le_min h h').trans (padicValRat.min_le_padicValRat_add hn)

/-- Inversion preserves congruence between nonzero rationals of valuation zero. -/
theorem congrInv {p e : ℕ} [Fact p.Prime] {a b : ℚ}
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e a⁻¹ b⁻¹ := by
  rcases h with rfl | h
  · exact Or.inl rfl
  by_cases he : a = b
  · exact Or.inl (congrArg Inv.inv he)
  right
  rw [show a⁻¹-b⁻¹ = -(a-b)/(a*b) by field_simp; ring,
    padicValRat.div (neg_ne_zero.mpr (sub_ne_zero.mpr he)) (mul_ne_zero ha hb),
    padicValRat.neg, padicValRat.mul ha hb, hva, hvb, add_zero, sub_zero]
  exact h

/-- Integer powers preserve congruence between nonzero rationals of valuation zero. -/
theorem congrZpow {p e : ℕ} [Fact p.Prime] {a b : ℚ}
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0) (n : ℤ) :
    _root_.AbcTwoNinths.Basic.RatCongruent p e (a^n) (b^n) := by
  cases n with
  | ofNat n =>
    exact _root_.AbcTwoNinths.Basic.congrPow h hva.symm.le hvb.symm.le n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    apply _root_.AbcTwoNinths.Basic.congrPow (_root_.AbcTwoNinths.Basic.congrInv h ha hb hva hvb)
    · simp [_root_.AbcTwoNinths.Basic.IntegralAt, hva]
    · simp [_root_.AbcTwoNinths.Basic.IntegralAt, hvb]

/--
A congruence between coprime powers of rational units congruent to one modulo p gives a common rational base congruent to one modulo p.
-/
theorem bezoutBase {p e c d : ℕ} [Fact p.Prime] {a b : ℚ}
    (hc : c.Coprime d) (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0)
    (ha1 : _root_.AbcTwoNinths.Basic.RatCongruent p 1 a 1) (hb1 : _root_.AbcTwoNinths.Basic.RatCongruent p 1 b 1)
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e (a^c) (b^d)) :
    ∃ w : ℚ, w ≠ 0 ∧ padicValRat p w = 0 ∧
      _root_.AbcTwoNinths.Basic.RatCongruent p e (w^d) a ∧ _root_.AbcTwoNinths.Basic.RatCongruent p e (w^c) b ∧ _root_.AbcTwoNinths.Basic.RatCongruent p 1 w 1 := by
  let u := Nat.gcdB c d
  let v := Nat.gcdA c d
  have huv : u * (d : ℤ) + v * (c : ℤ) = 1 := by
    have h' := Nat.gcd_eq_gcd_ab c d
    rw [hc.gcd_eq_one] at h'
    simpa [u, v, mul_comm, add_comm] using h'.symm
  let w := a^u * b^v
  refine ⟨w, mul_ne_zero (zpow_ne_zero _ ha) (zpow_ne_zero _ hb), ?_, ?_, ?_, ?_⟩
  · simp [w, padicValRat.mul (zpow_ne_zero _ ha) (zpow_ne_zero _ hb), hva, hvb]
  · have hh := _root_.AbcTwoNinths.Basic.congrZpow (_root_.AbcTwoNinths.Basic.congrSymm h) (pow_ne_zero _ hb) (pow_ne_zero _ ha)
      (by simp [hvb]) (by simp [hva]) v
    have hh' := _root_.AbcTwoNinths.Basic.congrScale (c := (a^u)^d) hh (by simp [_root_.AbcTwoNinths.Basic.IntegralAt, hva])
    convert hh' using 1
    · simp only [w, mul_pow]
      congr 1
      rw [← zpow_natCast (b^v), ← zpow_mul, ← zpow_natCast b, ← zpow_mul, mul_comm v]
    · rw [← zpow_natCast (a^u), ← zpow_mul, ← zpow_natCast a, ← zpow_mul,
        ← zpow_add₀ ha, mul_comm (c : ℤ) v, huv, zpow_one]
  · have hh := _root_.AbcTwoNinths.Basic.congrZpow h (pow_ne_zero _ ha) (pow_ne_zero _ hb)
      (by simp [hva]) (by simp [hvb]) u
    have hh' := _root_.AbcTwoNinths.Basic.congrScale (c := (b^v)^c) hh (by simp [_root_.AbcTwoNinths.Basic.IntegralAt, hvb])
    convert hh' using 1
    · rw [show w^c = (b^v)^c * (a^u)^c by simp [w, mul_pow, mul_comm]]
      congr 1
      rw [← zpow_natCast (a^u), ← zpow_mul, ← zpow_natCast a, ← zpow_mul, mul_comm u]
    · rw [← zpow_natCast (b^v), ← zpow_mul, ← zpow_natCast b, ← zpow_mul,
        ← zpow_add₀ hb]
      have he : v * (c : ℤ) + (d : ℤ) * u = 1 := by simpa [mul_comm, add_comm] using huv
      rw [he, zpow_one]
  · have h₁ := _root_.AbcTwoNinths.Basic.congrZpow ha1 ha one_ne_zero hva (padicValRat.one (p := p)) u
    have h₂ := _root_.AbcTwoNinths.Basic.congrZpow hb1 hb one_ne_zero hvb (padicValRat.one (p := p)) v
    simpa [w] using _root_.AbcTwoNinths.Basic.congrMul h₁ h₂ (show _root_.AbcTwoNinths.Basic.IntegralAt p (a^u) by simp [_root_.AbcTwoNinths.Basic.IntegralAt,hva])
      (show _root_.AbcTwoNinths.Basic.IntegralAt p ((1 : ℚ)^v) by simp [_root_.AbcTwoNinths.Basic.IntegralAt])

/--
Principal rational units with congruent coprime powers admit a principal rational base whose opposite powers represent the units.
-/
theorem bezoutPrincipal {p e c d : ℕ} [Fact p.Prime] {a b : ℚ}
    (hc : c.Coprime d) (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e (a^c) (b^d)) :
    ∃ w : ℚ, w ≠ 0 ∧ padicValRat p w = 0 ∧ _root_.AbcTwoNinths.Basic.RatCongruent p e (w^d) a ∧
      _root_.AbcTwoNinths.Basic.RatCongruent p e (w^c) b ∧ _root_.AbcTwoNinths.Basic.RatCongruent p 1 w 1 :=
  _root_.AbcTwoNinths.Basic.bezoutBase hc ha.1 hb.1 ha.2.1 hb.2.1 (ha.2.2.imp id (by intro h'; norm_num; omega))
    (hb.2.2.imp id (by intro h'; norm_num; omega)) h

/-- A nonzero rational of valuation zero has a natural representative modulo every power of p. -/
theorem representative {p : ℕ} [Fact p.Prime] (e : ℕ) (w : ℚ)
    (_hw : w ≠ 0) (hv : padicValRat p w = 0) :
    ∃ g : ℕ, _root_.AbcTwoNinths.Basic.RatCongruent p e (g : ℚ) w := by
  have hp : p.Prime := Fact.out
  have hd : ¬ p ∣ w.den := by
    intro h
    have hnum : ¬ p ∣ w.num.natAbs := fun ha =>
      hp.not_dvd_one (w.reduced.gcd_eq_one ▸ Nat.dvd_gcd ha h)
    have hn : padicValNat p w.num.natAbs = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hnum))
    have hpos : 1 ≤ padicValNat p w.den :=
      (padicValNat_dvd_iff_le w.den_ne_zero).mp (by simpa using h)
    change (padicValNat p w.num.natAbs : ℤ) - (padicValNat p w.den : ℤ) = 0 at hv
    omega
  have hc : w.den.Coprime (p^e) := ((hp.coprime_iff_not_dvd.mpr hd).symm).pow_right e
  let _ : NeZero (p^e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let D := ZMod.unitOfCoprime w.den hc
  let q : ZMod (p^e) := (w.num : ZMod (p^e)) * ↑D⁻¹
  let g := q.val
  have hg : (g : ZMod (p^e)) * w.den = w.num := by
    change (q.val : ZMod (p^e)) * (D : ZMod (p^e)) = _
    rw [ZMod.natCast_zmod_val]
    simp [q, mul_assoc, ← Units.val_mul]
  refine ⟨g, ?_⟩
  let n : ℤ := (g : ℤ) * (w.den : ℤ) - w.num
  have hdiv : ((p^e : ℕ) : ℤ) ∣ n := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd n (p^e)).mp
    simp [n, hg]
  have hdq : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_ne_zero
  have heq : (g : ℚ) - w = (n : ℚ) / w.den := by
    conv_lhs => rw [← w.num_div_den]
    push_cast [n]
    field_simp
  by_cases hn : n = 0
  · exact Or.inl (sub_eq_zero.mp (by simp [heq, hn]))
  · right
    have hdv : padicValRat p (w.den : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast (padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hd)) :
        padicValNat p w.den = 0)
    rw [heq, padicValRat.div (by exact_mod_cast hn) hdq, hdv, sub_zero, padicValRat.of_int]
    exact_mod_cast ((padicValInt_dvd_iff (p := p) e n).mp
      (by exact_mod_cast hdiv)).resolve_left hn

/--
Principal rational units with congruent coprime powers admit a natural base congruent to one modulo p whose opposite powers represent the units.
-/
theorem commonBaseLiftCoprime (p c d e : ℕ) (a b : ℚ)
    (hp : p.Prime) (hc : c.Coprime d)
    (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e (a^c) (b^d)) :
    ∃ g : ℕ, g % p = 1 ∧ _root_.AbcTwoNinths.Basic.RatCongruent p e ((g : ℚ)^d) a ∧
      _root_.AbcTwoNinths.Basic.RatCongruent p e ((g : ℚ)^c) b := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, hwv, hwa, hwb, hw1⟩ := _root_.AbcTwoNinths.Basic.bezoutPrincipal hc ha hb h
  obtain ⟨g, hg⟩ := _root_.AbcTwoNinths.Basic.representative (max 1 e) w hw hwv
  have weaken {x y : ℚ} {m n : ℕ} (hn : m ≤ n) (hxy : _root_.AbcTwoNinths.Basic.RatCongruent p n x y) :
      _root_.AbcTwoNinths.Basic.RatCongruent p m x y := hxy.imp id (fun h' => le_trans (by exact_mod_cast hn) h')
  have h1 := _root_.AbcTwoNinths.Basic.congrTrans (weaken (le_max_left 1 e) hg) hw1
  have hmod : g % p = 1 := by
    have hd : (p : ℤ) ∣ (g : ℤ) - 1 := by
      rcases h1 with h1 | h1
      · have hh : g = 1 := by exact_mod_cast h1
        simp [hh]
      · rw [show (g : ℚ) - 1 = (((g : ℤ) - 1 : ℤ) : ℚ) by push_cast; rfl] at h1
        rw [padicValRat.of_int] at h1
        simpa using (padicValInt_dvd_iff (p := p) 1 ((g : ℤ)-1)).mpr
          (.inr (by exact_mod_cast h1))
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    push_cast at he
    have he' := congrArg ZMod.val (sub_eq_zero.mp he)
    simpa [ZMod.val_natCast, ZMod.val_one, hp.one_lt] using he'
  have hi : _root_.AbcTwoNinths.Basic.IntegralAt p (g : ℚ) := by simp [_root_.AbcTwoNinths.Basic.IntegralAt]
  exact ⟨g,hmod,_root_.AbcTwoNinths.Basic.congrTrans (_root_.AbcTwoNinths.Basic.congrPow (weaken (le_max_right 1 e) hg) hi hwv.symm.le d) hwa,
    _root_.AbcTwoNinths.Basic.congrTrans (_root_.AbcTwoNinths.Basic.congrPow (weaken (le_max_right 1 e) hg) hi hwv.symm.le c) hwb⟩

/--
A common natural base congruent to one modulo p represents every determinant entry by a binomial coefficient times a power of the base.
-/
theorem gridCommonLift (p c d e : ℕ) (a b : ℚ)
    (hp : p.Prime) (hc : c.Coprime d)
    (ha : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p b)
    (h : _root_.AbcTwoNinths.Basic.RatCongruent p e (a^c) (b^d)) :
    ∃ g : ℕ, g % p = 1 ∧ ∀ kt rs : ℕ × ℕ,
      _root_.AbcTwoNinths.Basic.RatCongruent p e (_root_.AbcTwoNinths.Basic.determinantEntry a b c d kt rs)
        ((Nat.choose (rs.1*d + rs.2*c) kt.1 : ℚ) *
          (g : ℚ)^(kt.2*(rs.1*d + rs.2*c))) := by
  obtain ⟨g,hg,hga,hgb⟩ := _root_.AbcTwoNinths.Basic.commonBaseLiftCoprime p c d e a b hp hc ha hb h
  exact ⟨g,hg,_root_.AbcTwoNinths.Basic.determinantEntryCongruent p e c d g a b hp hg ha hb hga hgb⟩

end

end AbcTwoNinths.Basic
