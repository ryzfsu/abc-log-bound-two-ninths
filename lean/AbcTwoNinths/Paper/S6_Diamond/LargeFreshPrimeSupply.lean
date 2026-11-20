/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeSupply

/-!
# Large Fresh Prime Supply

The module guarantees a supply of sufficiently large fresh primes after excluding the source support. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.freshPrimeSupply`
-/

@[expose] public section

namespace AbcTwoNinths.Diamond

section



/--
At the admissible cutoff, the eligible primes satisfy the shell count and include a prime above its square root avoiding twice the radical. This is used in Section 6 of the paper.
-/
theorem freshPrimeSupply {R : ℕ} (hR : 0 < R) {p H η x : ℝ}
    (hx : Real.log R = 3 * x) (a : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x)
    (hX : max 128 (16 * (1 + 6 / _root_.AbcTwoNinths.ExteriorE2.margin η)) / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ x) :
    let S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
    S / (4 * Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ) ∧
      ∃ q ∈ _root_.AbcTwoNinths.ExteriorE2.fresh R S, q.Prime ∧ Real.sqrt S < (q : ℝ) ∧
        (q : ℝ) ≤ S ∧ ¬ q ∣ 2 * R := by
  dsimp
  have hc := _root_.AbcTwoNinths.ExteriorE2.adaptiveFreshSupply hR hx a hX
  have hlog : 0 < Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) :=
    lt_of_lt_of_le (mul_pos (_root_.AbcTwoNinths.ExteriorE2.marginPos a.eta_lt) a.hx) (_root_.AbcTwoNinths.ExteriorE2.shellSlack a).1
  have hs : 1 < _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x :=
    (Real.log_pos_iff (_root_.AbcTwoNinths.ExteriorE2.MPos p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x).le).mp hlog
  exact ⟨hc, _root_.AbcTwoNinths.ExteriorE2.freshWitness hs hc⟩

end

end AbcTwoNinths.Diamond
