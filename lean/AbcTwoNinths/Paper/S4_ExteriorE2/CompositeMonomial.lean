/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeQuotient
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModularResidueLattice

/-!
# Composite Monomial

Evaluates prime monomials in the unit group of the rational subring with denominators coprime to
the modulus, and identifies their images in the rationals. It supports Proposition 4.1 of the
paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeMonomial`
* `AbcTwoNinths.ExteriorE2.compositeMonomialRational`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
A prime coprime to the modulus is a unit in the ring of rationals with denominator coprime to that modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
def compositePrimeUnit {B q : ℕ} (hq : q.Prime) (hc : q.Coprime B) :
    (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ where
  val := q
  inv := ⟨(q : ℚ)⁻¹, by
    change ((q : ℚ)⁻¹).den.Coprime B
    simpa [Rat.den_inv, hq.ne_zero] using hc⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (by exact_mod_cast hq.ne_zero))
  inv_val := Subtype.ext (inv_mul_cancel₀ (by exact_mod_cast hq.ne_zero))

/--
Evaluate integer exponent vectors as products of prime units in the coprime-denominator ring. This is used in the proof of Proposition 4.1 of the paper.
-/
def compositeMonomial {I : Type*} [Fintype I] {B : ℕ}
    (q : I → ℕ) (hq : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B) :
    _root_.AbcTwoNinths.ExteriorE2.Exponents I →* (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ :=
  _root_.AbcTwoNinths.ExteriorE2.eval (fun i => _root_.AbcTwoNinths.ExteriorE2.compositePrimeUnit (hq i) (hc i))

/--
The rational value of the monomial is the usual product of the indexed primes to their integer exponents. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeMonomialRational {I : Type*} [Fintype I] {B : ℕ}
    (q : I → ℕ) (hq : ∀ i, (q i).Prime) (hc : ∀ i, (q i).Coprime B)
    (w : _root_.AbcTwoNinths.ExteriorE2.Exponents I) :
    (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hq hc w).val.val = (_root_.AbcTwoNinths.ExteriorE2.monomial q hq w).val := by
  have hbase (i : I) :
      Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom (_root_.AbcTwoNinths.ExteriorE2.compositePrimeUnit (hq i) (hc i)) =
        _root_.AbcTwoNinths.ExteriorE2.ratUnit q hq i := Units.ext rfl
  have h : Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom
      (_root_.AbcTwoNinths.ExteriorE2.compositeMonomial q hq hc w) = _root_.AbcTwoNinths.ExteriorE2.monomial q hq w := by
    change Units.map (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.toMonoidHom
        (∏ i, _root_.AbcTwoNinths.ExteriorE2.compositePrimeUnit (hq i) (hc i) ^ w.toAdd i) =
      ∏ i, _root_.AbcTwoNinths.ExteriorE2.ratUnit q hq i ^ w.toAdd i
    simp only [map_prod, map_zpow, hbase]
  exact congrArg Units.val h

end

end AbcTwoNinths.ExteriorE2
