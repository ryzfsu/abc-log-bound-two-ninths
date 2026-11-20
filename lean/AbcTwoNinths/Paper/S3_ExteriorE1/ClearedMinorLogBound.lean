/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.RationalBinomialMinor
public import AbcTwoNinths.Basic.DeterminantLogBound
public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Cleared Minor Log Bound

The module combines denominator clearing and centered width to bound the logarithm of the normalized minor. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.clearedSelectedMinorLogIneqFrom`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

open scoped BigOperators


/--
Clearing the denominators of a nonzero selected minor bounds one by its determinant scale times the two height factors.
-/
theorem clearedMinorHeight {I : Type*} [Fintype I] [DecidableEq I]
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (k t r s : I → ℕ) (b₁ b₂ R S U₁ V₁ U₂ V₂ : ℕ)
    (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (he₁ : ∀ σ : Equiv.Perm I, U₁ ≤ ∑ j, t (σ j) * r j ∧
      (∑ j, t (σ j) * r j) ≤ V₁)
    (he₂ : ∀ σ : Equiv.Perm I, U₂ ≤ ∑ j, t (σ j) * s j ∧
      (∑ j, t (σ j) * s j) ≤ V₂)
    (η₁ η₂ A : ℝ) (hA : 0 ≤ A)
    (hh₁ : Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ) ≤ η₁)
    (hh₂ : Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ) ≤ η₂)
    (hdet : ((Rat.castHom ℝ).mapMatrix (_root_.AbcTwoNinths.Basic.actualEntry q₁ q₂ k t r s b₁ b₂)).det ≠ 0)
    (hbound : |((Rat.castHom ℝ).mapMatrix (_root_.AbcTwoNinths.Basic.actualEntry q₁ q₂ k t r s b₁ b₂)).det| ≤
      A * (q₁ : ℝ)^V₁ * (q₂ : ℝ)^V₂) :
    1 ≤ A * Real.exp ((V₁ - U₁ : ℕ) * η₁) * Real.exp ((V₂ - U₂ : ℕ) * η₂) := by
  have hp₁ : 0 < (q₁ : ℝ) := by exact_mod_cast (by linarith : 0 < q₁)
  have hp₂ : 0 < (q₂ : ℝ) := by exact_mod_cast (by linarith : 0 < q₂)
  have qdet : (_root_.AbcTwoNinths.Basic.actualEntry q₁ q₂ k t r s b₁ b₂).det ≠ 0 := by
    intro h
    apply hdet
    rw [← RingHom.map_det, h, map_zero]
  obtain ⟨Z, hZ, _⟩ := _root_.AbcTwoNinths.Basic.selectedMinorBound q₁ q₂ (by linarith) (by linarith)
    k t r s b₁ b₂ R S U₁ V₁ U₂ V₂ hr hs he₁ he₂
  have hcast := congrArg (Rat.castHom ℝ) hZ
  simp only [map_mul, map_inv₀, map_pow, Rat.coe_castHom, Rat.cast_intCast,
    Rat.cast_natCast] at hcast
  have hmap := RingHom.map_det (Rat.castHom ℝ) (_root_.AbcTwoNinths.Basic.actualEntry q₁ q₂ k t r s b₁ b₂)
  rw [Rat.coe_castHom] at hmap
  rw [hmap] at hcast
  have hZne : Z ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hcast
    exact (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) hdet) hcast.symm
  have h1 : (1 : ℝ) ≤ |(Z : ℝ)| := by exact_mod_cast Int.one_le_abs hZne
  have hc (q : ℚ) (hq : 0 < (q : ℝ)) (U V : ℕ) (hUV : U ≤ V)
      (η : ℝ) (hh : Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ η) :
      ((q : ℝ)^U)⁻¹ * (q.den : ℝ)^(V-U) * (q : ℝ)^V ≤
        Real.exp ((V-U : ℕ) * η) := by
    have hqden : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Rat.mul_den_eq_num q
    have hnum : 0 ≤ q.num := by
      have ht : (0 : ℝ) ≤ (q.num : ℝ) := by rw [← hqden]; positivity
      exact_mod_cast ht
    have hmax : 0 < ((max q.num.natAbs q.den : ℕ) : ℝ) := by positivity
    have hn : (q.num : ℝ) ≤ Real.exp η := by
      calc
        (q.num : ℝ) ≤ ((max q.num.natAbs q.den : ℕ) : ℝ) := by
          rw [← Int.cast_natCast]
          exact Int.cast_le.mpr (by omega)
        _ = _ := (Real.exp_log hmax).symm
        _ ≤ _ := Real.exp_le_exp.mpr hh
    have heq : (q : ℝ)^V = (q : ℝ)^U * (q : ℝ)^(V-U) := by
      rw [← pow_add, Nat.add_sub_cancel' hUV]
    calc
      _ = ((q : ℝ) * (q.den : ℝ))^(V-U) := by
        rw [heq, mul_pow]
        field_simp
      _ = (q.num : ℝ)^(V-U) := by rw [hqden]
      _ ≤ (Real.exp η)^(V-U) := pow_le_pow_left₀ (by exact_mod_cast hnum) hn _
      _ = _ := by rw [Real.exp_nat_mul]
  have h₁ := hc q₁ hp₁ U₁ V₁ ((he₁ 1).1.trans (he₁ 1).2) η₁ hh₁
  have h₂ := hc q₂ hp₂ U₂ V₂ ((he₂ 1).1.trans (he₂ 1).2) η₂ hh₂
  rw [hcast, abs_mul, abs_of_nonneg (show 0 ≤ _ * _ by positivity)] at h1
  calc
    _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = A * (((q₁ : ℝ)^U₁)⁻¹ * (q₁.den : ℝ)^(V₁-U₁) * (q₁ : ℝ)^V₁) *
        (((q₂ : ℝ)^U₂)⁻¹ * (q₂.den : ℝ)^(V₂-U₂) * (q₂ : ℝ)^V₂) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h₁ hA) h₂ (by positivity) (by positivity)

/--
Taking logarithms of the positive determinant product gives the normalized radius inequality.
-/
theorem minorLogNormalize (N E J L K : ℕ) (M Q ηR ηS dR dS : ℝ)
    (hN : 0 < N) (hQ : 0 < Q)
    (hE : 2 * (E : ℝ) = (N : ℝ) * ((K : ℝ) * ((L - 1 : ℕ) : ℝ)))
    (hR : dR ≤ (N : ℝ) * ((L : ℝ) * ηR / 4))
    (hS : dS ≤ (N : ℝ) * ((L : ℝ) * ηS / 4))
    (P : ℝ) (hP : 0 < P)
    (hPlog : Real.log P ≤ (N : ℝ) * ((J : ℝ) / 2 * Real.log (Real.exp 2 * M / J)))
    (hprod : 1 ≤ (2 : ℝ)^N * (N.factorial : ℝ) * P *
      (Real.exp 1 / Q)^E * Real.exp 1 * Real.exp dR * Real.exp dS) :
    (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log (Q / Real.exp 1) ≤
      2 * Real.log 2 + 2 * Real.log (N : ℝ) + 2 / (N : ℝ) +
        (J : ℝ) * Real.log (Real.exp 2 * M / J) +
        (1 / 2 : ℝ) * (L : ℝ) * (ηR + ηS) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hF : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    have hu : (N.factorial : ℝ) ≤ (N : ℝ)^N := by
      exact_mod_cast _root_.AbcTwoNinths.Basic.factorialUpper N
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hu
  have hp := Real.log_le_log zero_lt_one hprod
  simp only [Real.log_one] at hp
  repeat rw [Real.log_mul (by positivity) (by positivity)] at hp
  rw [Real.log_pow, Real.log_pow] at hp
  simp only [Real.log_exp] at hp
  rw [Real.log_div (by positivity) hQ.ne', Real.log_exp] at hp
  rw [Real.log_div hQ.ne' (by positivity), Real.log_exp]
  have hz : (N : ℝ) * (2 / (N : ℝ)) = 2 := by field_simp
  apply le_of_mul_le_mul_left _ hNp
  nlinarith only [hp, hF, hPlog, hR, hS, hz,
    congrArg (fun x : ℝ => x * (Real.log Q - 1)) hE]

private theorem exponentIdentity (K L : ℕ) (hL : 2 ≤ L) :
    2 * ((K * L * K * (L - 1) / 2 : ℕ) : ℝ) =
      ((K * L : ℕ) : ℝ) * ((K : ℝ) * ((L - 1 : ℕ) : ℝ)) := by
  have hD : 2 ∣ L * (L - 1) := by
    have h := Nat.mod_lt L (by decide : 0 < 2)
    rcases (show L % 2 = 0 ∨ L % 2 = 1 by omega) with he | ho
    · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero he) _
    · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega : (L - 1) % 2 = 0)) _
  have hD' : 2 ∣ K * L * K * (L - 1) := by
    rw [show K * L * K * (L - 1) = (L * (L - 1)) * (K * K) by ring]
    exact dvd_mul_of_dvd_left hD _
  have hn : 2 * (K * L * K * (L - 1) / 2) = K * L * K * (L - 1) := by omega
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hn
  push_cast at hr ⊢
  linarith only [hr]

private theorem widthHeight (K L R d : ℕ) (η : ℝ)
    (hη : 0 ≤ η) (hd : d ≤ K * (L * L / 4) * R) :
    (d : ℝ) * η ≤ ((K * L : ℕ) : ℝ) * ((L : ℝ) * ((R : ℝ) * η) / 4) := by
  have h₀ : 4 * (L * L / 4) ≤ L * L := by omega
  have h₁ : 4 * d ≤ K * L * L * R := calc
    _ ≤ 4 * (K * (L * L / 4) * R) := Nat.mul_le_mul_left _ hd
    _ = K * (4 * (L * L / 4)) * R := by ring
    _ ≤ K * (L * L) * R := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h₀)
    _ = _ := by ring
  have h₂ : (4 : ℝ) * d ≤ (K : ℝ) * L * L * R := by exact_mod_cast h₁
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right h₂ hη]

/--
The nonvanishing of the selected minor gives a logarithmic restriction on `Q₀` in
Proposition 3.1, using the permutation width, determinant upper bound, and row product
estimate. The row logarithm may have either sign.
-/
theorem clearedSelectedMinorLogIneqFrom {J L R S b₁ b₂ : ℕ}
    (hL : 2 ≤ L) (hM : 0 < R * b₂ + S * b₁)
    (q₁ q₂ : ℚ) (hq₁ : 1 < q₁) (hq₂ : 1 < q₂)
    (η₁ η₂ Q₀ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hh₁ : Real.log ((max q₁.num.natAbs q₁.den : ℕ) : ℝ) ≤ η₁)
    (hh₂ : Real.log ((max q₂.num.natAbs q₂.den : ℕ) : ℝ) ≤ η₂)
    (hQ₀ : 2 ≤ Q₀)
    (f : (Fin (J + 1) × Fin L) ↪ _root_.AbcTwoNinths.Basic.Rectangle R S)
    (hdet : (Matrix.of fun k j : Fin (J + 1) × Fin L =>
      (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
        (q₁ : ℝ) ^ (k.2.val * (f j).1.val) *
        (q₂ : ℝ) ^ (k.2.val * (f j).2.val)).det ≠ 0)
    (width : ∀ T (a : Fin (J + 1) × Fin L → ℕ), (∀ j, a j ≤ T) →
      ∀ σ τ : Equiv.Perm (Fin (J + 1) × Fin L),
        (∑ j, (σ j).2.val * a j) ≤ (∑ j, (τ j).2.val * a j) + (J + 1) * (L * L / 4) * T)
    (detBound : ∀ V₁ V₂ : ℕ,
      (∀ σ : Equiv.Perm (Fin (J + 1) × Fin L), ∑ j, (σ j).2.val * (f j).1.val ≤ V₁) →
      (∀ σ : Equiv.Perm (Fin (J + 1) × Fin L), ∑ j, (σ j).2.val * (f j).2.val ≤ V₂) →
      let N := (J + 1) * L
      let E := N * (J + 1) * (L - 1) / 2
      let M : ℝ := (R * b₂ + S * b₁ : ℕ)
      |(Matrix.of fun k j : Fin (J + 1) × Fin L =>
        (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
          (q₁ : ℝ) ^ (k.2.val * (f j).1.val) *
          (q₂ : ℝ) ^ (k.2.val * (f j).2.val)).det| ≤
      (2 : ℝ)^N * (N.factorial : ℝ) *
        (∏ i : Fin (J + 1) × Fin L, M ^ i.1.val / (i.1.val.factorial : ℝ)) *
        (Real.exp 1 / Q₀)^E * (q₁ : ℝ)^V₁ * (q₂ : ℝ)^V₂ * Real.exp 1)
    (rowLog :
      let N := (J + 1) * L
      let M : ℝ := (R * b₂ + S * b₁ : ℕ)
      Real.log (∏ i : Fin (J + 1) × Fin L, M ^ i.1.val / (i.1.val.factorial : ℝ)) ≤
        (N : ℝ) * (J : ℝ) / 2 * Real.log (Real.exp 2 * M / J)) :
    let K := J + 1
    let N := K * L
    let M : ℝ := (R * b₂ + S * b₁ : ℕ)
    (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log (Q₀ / Real.exp 1) ≤
      2 * Real.log 2 + 2 * Real.log (N : ℝ) + 2 / (N : ℝ) +
        (J : ℝ) * Real.log (Real.exp 2 * M / (J : ℝ)) +
        (1 / 2 : ℝ) * (L : ℝ) * ((R : ℝ) * η₁ + (S : ℝ) * η₂) := by
  let K := J + 1
  let N := K * L
  let E := N * K * (L - 1) / 2
  let M : ℝ := (R * b₂ + S * b₁ : ℕ)
  let P : ℝ := ∏ i : Fin K × Fin L, M ^ i.1.val / (i.1.val.factorial : ℝ)
  let A := (2 : ℝ)^N * (N.factorial : ℝ) * P * (Real.exp 1 / Q₀)^E * Real.exp 1
  let r (j : Fin K × Fin L) := (f j).1.val
  let s (j : Fin K × Fin L) := (f j).2.val
  have hr : ∀ j, r j ≤ R := fun j => Nat.le_of_lt_succ (f j).1.isLt
  have hs : ∀ j, s j ≤ S := fun j => Nat.le_of_lt_succ (f j).2.isLt
  obtain ⟨U₁, V₁, he₁, hw₁⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * r j) (K * (L * L / 4) * R) (width R r hr)
  obtain ⟨U₂, V₂, he₂, hw₂⟩ := _root_.AbcTwoNinths.Basic.attainedExponentInterval
    (fun σ => ∑ j, (σ j).2.val * s j) (K * (L * L / 4) * S) (width S s hs)
  have hm :
      (Rat.castHom ℝ).mapMatrix (_root_.AbcTwoNinths.Basic.actualEntry q₁ q₂ (fun i : Fin K × Fin L => i.1.val)
        (fun i => i.2.val) r s b₁ b₂) =
      Matrix.of (fun k j : Fin K × Fin L =>
        (Nat.choose ((f j).1.val * b₂ + (f j).2.val * b₁) k.1.val : ℝ) *
          (q₁ : ℝ) ^ (k.2.val * (f j).1.val) *
          (q₂ : ℝ) ^ (k.2.val * (f j).2.val)) := by
    ext i j
    simp [RingHom.mapMatrix, _root_.AbcTwoNinths.Basic.actualEntry, r, s]
  have hMp : 0 < M := Nat.cast_pos.mpr hM
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q₀ := by linarith
  have hu := detBound V₁ V₂ (fun σ => (he₁ σ).2) (fun σ => (he₂ σ).2)
  change _ ≤ (2 : ℝ)^N * (N.factorial : ℝ) * P * (Real.exp 1 / Q₀)^E *
    (q₁ : ℝ)^V₁ * (q₂ : ℝ)^V₂ * Real.exp 1 at hu
  rw [show (2 : ℝ)^N * (N.factorial : ℝ) * P * (Real.exp 1 / Q₀)^E *
    (q₁ : ℝ)^V₁ * (q₂ : ℝ)^V₂ * Real.exp 1 = A * (q₁ : ℝ)^V₁ * (q₂ : ℝ)^V₂ by
      dsimp [A]; ring] at hu
  have hp := _root_.AbcTwoNinths.ExteriorE1.clearedMinorHeight q₁ q₂ hq₁ hq₂ (fun i : Fin K × Fin L => i.1.val)
    (fun i => i.2.val) r s b₁ b₂ R S U₁ V₁ U₂ V₂ hr hs he₁ he₂ η₁ η₂ A
    (by dsimp [A]; positivity) hh₁ hh₂ (by rw [hm]; exact hdet) (by rw [hm]; exact hu)
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos J) (by omega)
  have hrow : Real.log P ≤ (N : ℝ) * ((J : ℝ) / 2 * Real.log (Real.exp 2 * M / J)) := by
    convert rowLog using 1
    ring
  exact _root_.AbcTwoNinths.ExteriorE1.minorLogNormalize N E J L K M Q₀ ((R : ℝ) * η₁) ((S : ℝ) * η₂) _ _
    hN hQ (exponentIdentity K L hL) (widthHeight K L R _ η₁ hη₁ hw₁)
    (widthHeight K L S _ η₂ hη₂ hw₂) P hP hrow hp

end

end AbcTwoNinths.ExteriorE1
