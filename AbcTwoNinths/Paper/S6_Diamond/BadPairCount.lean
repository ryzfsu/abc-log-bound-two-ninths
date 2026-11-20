/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.BadPairFiber
public import AbcTwoNinths.Paper.S6_Diamond.CollisionConsumer
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Bad Pair Count

The module encodes prime products by tuples and counts pairs with restricted projection cost. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.integralDifference`
-/

@[expose] public section
namespace AbcTwoNinths.Diamond

section



open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/--
The product of the coordinate bases raised to their natural exponents. This is used in Section 6 of the paper.
-/
def primeProduct (q : ι → ℕ) (n : ι → ℕ) : ℕ := ∏ i, q i ^ n i

/--
Encode a signed exponent vector by the products of its positive and negative parts. This is used in Section 6 of the paper.
-/
def tupleCode (q : ι → ℕ) (u : ι → ℤ) : ℕ × ℕ :=
  (_root_.AbcTwoNinths.Diamond.primeProduct q (fun i => (u i).toNat), _root_.AbcTwoNinths.Diamond.primeProduct q (fun i => (-u i).toNat))

/--
The sum of absolute integer exponents weighted by the logarithms of the bases. This is used in Section 6 of the paper.
-/
noncomputable def length (q : ι → ℕ) (u : ι → ℤ) : ℝ :=
  ∑ i, |(u i : ℝ)| * Real.log (q i)

/-- The product of prime powers is positive. -/
theorem primeProductPos (q n : ι → ℕ) (hp : ∀ i, (q i).Prime) :
    0 < _root_.AbcTwoNinths.Diamond.primeProduct q n :=
  Finset.prod_pos fun i _ => pow_pos (hp i).pos _

/-- Distinct prime bases determine every natural exponent from their product. -/
theorem primeProductInjective (q : ι → ℕ) (hp : ∀ i, (q i).Prime)
    (hq : Function.Injective q) : Function.Injective (_root_.AbcTwoNinths.Diamond.primeProduct q) := by
  classical
  have coord (n : ι → ℕ) (j : ι) : (_root_.AbcTwoNinths.Diamond.primeProduct q n).factorization (q j) = n j := by
    rw [_root_.AbcTwoNinths.Diamond.primeProduct, Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (hp i).ne_zero)]
    rw [Finset.sum_eq_single j]
    · exact Nat.factorization_pow_self (hp j)
    · intro i _ hij
      rw [Nat.factorization_pow, Finsupp.smul_apply,
        (hp i).factorization, Finsupp.single_eq_of_ne (fun h => hij (hq h.symm))]
      simp
    · simp
  intro m n h
  funext j
  rw [← coord m j, ← coord n j, h]

/-- The two product coordinates recover the signed exponents on distinct prime bases. -/
theorem tupleCodeInjective (q : ι → ℕ) (hp : ∀ i, (q i).Prime)
    (hq : Function.Injective q) : Function.Injective (_root_.AbcTwoNinths.Diamond.tupleCode q) := by
  intro u v h
  have hpos := _root_.AbcTwoNinths.Diamond.primeProductInjective q hp hq (congrArg Prod.fst h)
  have hneg := _root_.AbcTwoNinths.Diamond.primeProductInjective q hp hq (congrArg Prod.snd h)
  funext i
  have h1 := congrFun hpos i
  have h2 := congrFun hneg i
  omega

/--
Subtract the source vector scaled by the ratio of the two roof coordinates. This is used in Section 6 of the paper.
-/
noncomputable def roofProjection (roof : ι) (v : ι → ℤ) : (ι → ℤ) →+ (ι → ℝ) where
  toFun u i := (u i : ℝ) - (u roof : ℝ) / (v roof : ℝ) * (v i : ℝ)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp [add_div, add_mul]; ring

/--
The sum of absolute real coordinates weighted by the logarithms of the bases. This is used in Section 6 of the paper.
-/
noncomputable def cost (q : ι → ℕ) (u : ι → ℝ) : ℝ :=
  ∑ i, |u i| * Real.log (q i)

omit [Fintype ι] in
/-- Roof projection kills the source vector when its roof coordinate is nonzero. -/
theorem roofProjectionSelf (roof : ι) {v : ι → ℤ} (hv : v roof ≠ 0) :
    _root_.AbcTwoNinths.Diamond.roofProjection roof v v = 0 := by
  ext i
  have hv' : (v roof : ℝ) ≠ 0 := by exact_mod_cast hv
  simp [_root_.AbcTwoNinths.Diamond.roofProjection, div_self hv']

/-- With prime bases the cost of a difference is at most the sum of the two costs. -/
theorem costSubLe (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (u w : ι → ℝ) :
    _root_.AbcTwoNinths.Diamond.cost q (u - w) ≤ _root_.AbcTwoNinths.Diamond.cost q u + _root_.AbcTwoNinths.Diamond.cost q w := by
  unfold _root_.AbcTwoNinths.Diamond.cost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub _ _)
    (Real.log_nonneg (by exact_mod_cast (hp i).one_lt.le))

/--
In a common roof and residue cell the difference is a multiple of the positive fresh exponent, with quotient of log length at most twice the cost bound. This is used in Section 6 of the paper.
-/
theorem integralDifference (q : ι → ℕ) (hp : ∀ i, (q i).Prime)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) {b : ℕ} (hb : 0 < b)
    (a a₀ : ℤ) (u u₀ : ι → ℤ) (T : ℝ)
    (hmod : a % (b : ℤ) = a₀ % (b : ℤ))
    (hroof : (a • v + b • u) roof = (a₀ • v + b • u₀) roof)
    (hu : _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v u) ≤ T)
    (hu₀ : _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v u₀) ≤ T) :
    ∃ d : ι → ℤ, (a • v + b • u) - (a₀ • v + b • u₀) = b • d ∧
      _root_.AbcTwoNinths.Diamond.length q d ≤ 2 * T := by
  let d := (a / (b : ℤ) - a₀ / (b : ℤ)) • v + (u - u₀)
  have hd : (a • v + b • u) - (a₀ • v + b • u₀) = b • d := by
    have ha := Int.emod_add_mul_ediv a (b : ℤ)
    have ha₀ := Int.emod_add_mul_ediv a₀ (b : ℤ)
    have haf : a - a₀ = (b : ℤ) * (a / (b : ℤ) - a₀ / (b : ℤ)) := by
      rw [mul_sub]
      rw [hmod] at ha
      linarith
    ext i
    change a * v i + (b : ℤ) * u i - (a₀ * v i + (b : ℤ) * u₀ i) =
      (b : ℤ) * ((a / (b : ℤ) - a₀ / (b : ℤ)) * v i + (u i - u₀ i))
    calc
      _ = (a - a₀) * v i + (b : ℤ) * (u i - u₀ i) := by ring
      _ = _ := by rw [haf]; ring
  have hdz : d roof = 0 := by
    have hh := congrFun hd roof
    change (a • v + b • u) roof - (a₀ • v + b • u₀) roof = (b : ℤ) * d roof at hh
    rw [hroof, sub_self] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast hb.ne')
  have hpi : _root_.AbcTwoNinths.Diamond.roofProjection roof v d =
      _root_.AbcTwoNinths.Diamond.roofProjection roof v u - _root_.AbcTwoNinths.Diamond.roofProjection roof v u₀ := by
    change _root_.AbcTwoNinths.Diamond.roofProjection roof v ((a / (b : ℤ) - a₀ / (b : ℤ)) • v + (u - u₀)) = _
    rw [map_add, map_zsmul, _root_.AbcTwoNinths.Diamond.roofProjectionSelf roof hv, smul_zero,
      zero_add, map_sub]
  have heq : _root_.AbcTwoNinths.Diamond.length q d = _root_.AbcTwoNinths.Diamond.cost q (_root_.AbcTwoNinths.Diamond.roofProjection roof v d) := by
    simp [_root_.AbcTwoNinths.Diamond.length, _root_.AbcTwoNinths.Diamond.cost, _root_.AbcTwoNinths.Diamond.roofProjection, hdz]
  refine ⟨d, hd, ?_⟩
  rw [heq, hpi]
  exact (_root_.AbcTwoNinths.Diamond.costSubLe q hp _ _).trans (by linarith)

/--
Sum the positive parts of the exponents with logarithmic weights. This is used in Section 6 of the paper.
-/
noncomputable def side (q : ι → ℕ) (u : ι → ℤ) : ℝ :=
  ∑ i, max (u i : ℝ) 0 * Real.log (q i)

/--
The larger of the positive and negative logarithmic sums gives the monomial height. This is used in Section 6 of the paper.
-/
noncomputable def height (q : ι → ℕ) (u : ι → ℤ) : ℝ :=
  max (_root_.AbcTwoNinths.Diamond.side q u) (_root_.AbcTwoNinths.Diamond.side q (-u))




/--
The class of a residue unit in the quotient by the subgroup of signs. This is used in Section 6 of the paper.
-/
def quotientLabel {p : ℕ} (z : (ZMod p)ˣ) : _root_.AbcTwoNinths.ExteriorE2.Label p :=
  QuotientGroup.mk' (_root_.AbcTwoNinths.ExteriorE2.signs p) z

/--
A trivial quotient label for the product of an old unit and a fresh unit power gives residue one or minus one.
-/
theorem signedOfQuotient {p : ℕ} [Fact p.Prime]
    (z ρ : (ZMod p)ˣ) (b : ℕ) (h : _root_.AbcTwoNinths.Diamond.quotientLabel z * _root_.AbcTwoNinths.Diamond.quotientLabel ρ ^ b = 1) :
    (z : ZMod p) * (ρ : ZMod p) ^ b = 1 ∨ (z : ZMod p) * (ρ : ZMod p) ^ b = -1 := by
  have h' : _root_.AbcTwoNinths.Diamond.quotientLabel (z * ρ ^ b) = 1 := by
    simpa only [_root_.AbcTwoNinths.Diamond.quotientLabel, map_mul, map_pow] using h
  have hs := (QuotientGroup.eq_one_iff (N := _root_.AbcTwoNinths.ExteriorE2.signs p) _).mp h'
  change z * ρ ^ b = 1 ∨ z * ρ ^ b = -1 at hs
  rcases hs with hs | hs
  · exact Or.inl (by simpa using congrArg Units.val hs)
  · exact Or.inr (by simpa using congrArg Units.val hs)

end

end AbcTwoNinths.Diamond
