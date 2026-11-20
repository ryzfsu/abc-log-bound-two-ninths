/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SideData

/-!
# Side Projection

The two entries complementary to the selected side are coprime, are at least the smaller summand,
and have product dividing the product of the three entries. This supports Proposition 2.1 of the
paper.

## Main results
* `AbcTwoNinths.PolyCap.selectedSideProjection`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section


private theorem casesProp {D : Type} {P : D → Prop} (s : _root_.AbcTwoNinths.Statement.Side)
    (a : s = .a → D) (b : s = .b → D) (c : s = .c → D)
    (ha : ∀ h, P (a h)) (hb : ∀ h, P (b h)) (hc : ∀ h, P (c h)) :
    P (_root_.AbcTwoNinths.Statement.Side.casesOn (motive := fun k => s = k → D) s a b c rfl) := by
  cases s <;> first | exact ha rfl | exact hb rfl | exact hc rfl

private theorem castProp {D : Type} {P : D → Prop} {s k : _root_.AbcTwoNinths.Statement.Side}
    (f : s = k → D) (h : k = s) (hf : ∀ e, P (f e)) :
    P (Eq.ndrec (motive := fun x => s = x → D) f h rfl) := by
  cases h
  exact hf rfl

/--
For a prime on the minimum-radical side of an ordered triple, the selected numerator and denominator
are coprime, each is at least `a`, and their product divides `abc`.
-/
theorem selectedSideProjection (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) (ho : t.a ≤ t.b) :
    let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    s.n.Coprime s.d ∧ t.a ≤ s.n ∧ t.a ≤ s.d ∧ s.n*s.d ∣ t.a*t.b*t.c := by
  have hac : t.a.Coprime t.c := by
    rw [← t.add, Nat.add_comm t.a t.b, Nat.coprime_add_self_right]
    exact t.coprime
  have hbc : t.b.Coprime t.c := by
    rw [← t.add, Nat.coprime_add_self_right]
    exact t.coprime.symm
  have hle : t.a ≤ t.c := by rw [← t.add]; omega
  let P := fun s : _root_.AbcTwoNinths.PolyCap.SideData t p => s.n.Coprime s.d ∧ t.a ≤ s.n ∧ t.a ≤ s.d ∧ s.n*s.d ∣ t.a*t.b*t.c
  change P (_root_.AbcTwoNinths.PolyCap.selectedSideData t hp)
  apply casesProp (P := P)
  all_goals intro h; apply castProp (P := P); intro e
  · exact ⟨hbc.symm, hle, ho, ⟨t.a, by dsimp; ring⟩⟩
  · exact ⟨hac.symm, hle, le_rfl, ⟨t.b, by dsimp; ring⟩⟩
  · exact ⟨t.coprime, le_rfl, ho, ⟨t.c, rfl⟩⟩

end

end AbcTwoNinths.PolyCap
