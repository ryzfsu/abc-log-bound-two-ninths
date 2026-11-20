/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Bézout identity in the composite quotient

Constructs a common principal-unit base for two units whose coprime powers agree in the composite
residue quotient. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.principalCommonBase`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
If `a ^ c = b ^ d` and `c, d` are coprime, the Bézout combination `w` satisfies `w ^ d = a`
and `w ^ c = b` .
-/
theorem explicitCommonBase {G : Type*} [CommGroup G] {c d : ℕ}
    (hc : c.Coprime d) {a b : G} (h : a ^ c = b ^ d) :
    let w := a ^ (c.gcdB d) * b ^ (c.gcdA d)
    w ^ d = a ∧ w ^ c = b := by
  let u := Nat.gcdB c d
  let v := Nat.gcdA c d
  have huv : (d : ℤ) * u + (c : ℤ) * v = 1 := by
    simpa [u, v, hc.gcd_eq_one, add_comm] using (Nat.gcd_eq_gcd_ab c d).symm
  refine ⟨?_, ?_⟩
  · have hd : (b ^ v) ^ d = a ^ ((c : ℤ) * v) := by
      rw [← zpow_natCast (b ^ v), ← zpow_mul, mul_comm v, zpow_mul,
        zpow_natCast, ← h, ← zpow_natCast a, ← zpow_mul]
    rw [mul_pow, hd, ← zpow_natCast (a ^ u), ← zpow_mul, mul_comm u,
      ← zpow_add, huv, zpow_one]
  · have ha : (a ^ u) ^ c = b ^ ((d : ℤ) * u) := by
      rw [← zpow_natCast (a ^ u), ← zpow_mul, mul_comm u, zpow_mul,
        zpow_natCast, h, ← zpow_natCast b, ← zpow_mul]
    rw [mul_pow, ha, ← zpow_natCast (b ^ v), ← zpow_mul, mul_comm v,
      ← zpow_add, huv, zpow_one]

/--
If `a` and `b` lie in the kernel of `f` and satisfy `a ^ c = b ^ d` with coprime exponents,
there is a common base `w` in that kernel with `a ^ r * b ^ s = w ^ (r * d + s * c)` .
-/
theorem principalCommonBase {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) {c d : ℕ} (hc : c.Coprime d) {a b : G}
    (ha : f a = 1) (hb : f b = 1) (h : a ^ c = b ^ d) :
    ∃ w : G, f w = 1 ∧ ∀ r s : ℕ, a ^ r * b ^ s = w ^ (r * d + s * c) := by
  let w := a ^ (c.gcdB d) * b ^ (c.gcdA d)
  have ⟨hwa, hwb⟩ : w ^ d = a ∧ w ^ c = b := _root_.AbcTwoNinths.ExteriorE2.explicitCommonBase hc h
  refine ⟨w, by simp [w, ha, hb], fun r s => ?_⟩
  rw [pow_add, mul_comm r d, mul_comm s c, pow_mul, pow_mul]
  exact congrArg₂ (· * ·) (congrArg (· ^ r) hwa.symm) (congrArg (· ^ s) hwb.symm)

end

end AbcTwoNinths.ExteriorE2
