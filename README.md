# An upper bound for log c in the abc conjecture with exponent 2/9

Ruiyi Zhang

This package formalizes Theorem 1.1 of the companion paper (see [Citation](#citation)).
For every real $`\varepsilon>0`$, there is a real $`C>0`$ such that all positive
coprime integers $`a,b`$, with $`a+b=c`$, satisfy

```math
\log\, c \leq C\,\mathrm{rad}(abc)^{2/9+\varepsilon}.
```

The radical is the product of the distinct prime factors. This estimate concerns
the logarithm of $`c`$. The abc conjecture itself remains open.

`Challenge.lean` presents Theorem 1.1 with only Mathlib as its dependency.
`Solution.lean` supplies the proof under the same name,
`AbcTwoNinths.twoNinths`. The target Lean version is `v4.35.0-rc4`, with Mathlib
and its dependencies pinned in `lake-manifest.json`.

The definition of `AbcTwoNinths.twoNinthsStatement` is:

```lean
def twoNinthsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : Nat, TwoNinthsTriple a b c →
      Real.log c ≤ C * (radNat (a * b * c) : ℝ) ^ ((2 : ℝ) / 9 + ε)
```

## Paper and module map

The following folders contain the formal proof. [PaperMap.lean](PaperMap.lean)
names the numbered declarations and is checked by the default `lake build`.

| Paper result | Proof folder under `AbcTwoNinths/Paper/` |
|---|---|
| Theorem 1.1, statement | `S1_Statement` and `AbcTwoNinths/Statement.lean` |
| Proposition 2.1 | `S2_PolyCap` |
| Proposition 3.1 | `S3_ExteriorE1` |
| Proposition 4.1 | `S4_ExteriorE2` |
| Proposition 5.1 | `S5_Selection` |
| Proposition 6.1 and Lemma 6.2 | `S6_Diamond` |
| Proposition 7.1 and Lemmas 7.2–7.3 | `S7_Terminal` |
| Proposition 8.1, Lemma 8.2 and final proof | `S8_Assembly` |

## Differences from the paper

1. **Proposition 2.1.** Lean obtains the polynomial cap from the elementary support bound in `polyCapOfMaster`. The paper applies the Stewart and Yu estimate quoted in Fact F1. Both proofs take $`k=20`$.
2. **Proposition 3.1.** Lean deduces the real estimate from a variable-radius two-logarithm bound and a reduction to slabs. The paper applies the real-place estimate in Fact F2 to $`b/c`$. Both exterior estimates use Zhang's Fact F3 and Lemma 2.1, equations (2.3), (2.4), (2.6) and (2.8). Their thresholds use the height bound already present in (2.6).
3. **Proposition 4.1.** Lean uses `tightModulusExclusion` for a composite modulus. The paper sums the finite-place estimate in Fact F2 over primes up to the cutoff. Both constructions take $`\sigma=\nu=(\lambda-2/3)/100`$ and $`\kappa=(1-9\eta)/32`$.
4. **Proposition 5.1.** `selectedPrimeOfExteriorBounds` selects the unique prime divisor of the least-radical side above the cutoff and proves the lower depth bound for that prime. The upper depth bound, the logarithmic interval for the prime and the identity relating its depth to the signed ratio follow from the definitions and the cutoff inequalities.
5. **Proposition 6.1.** Lean indexes the old primes by `Unit ⊕ I`, putting a maximal coordinate first. `SelectedDeterminantInput` records the divisibility, shell and depth conditions. Lean proves projection separation using `twoLogUnbounded147` and unimodular reduced bases. The paper uses Bugeaud and Laurent's Corollary 2 and Minkowski's second theorem.
6. **Lemma 6.2.** `existsFreshPrimePair` uses the same indexing, allows any natural number $`W`$, and absorbs the initial size and weight bounds into its threshold. Lean counts the available primes with an explicit Chebyshev bound. The paper invokes Rosser and Schoenfeld (1962), Corollary 1, (3.5), directly. The Lean lemma allows every real $`0<\eta<1/9`$. Lemma 6.2 takes its rational specialization under the standing choice of $`\eta`$ in Section 2.
7. **Proposition 7.1.** Lean selects the $`2K`$ rows by an embedding of `Fin K ⊕ Fin K` into the sites. Both statements select one nonzero integer minor with the upper bound and, when $`4K\le3m`$, the lower bound. Both allow $`p=2`$ and $`m=0`$. At positive depth the paper requires $`\gamma(1,0)\ne1`$, as follows from Lean's valuation hypothesis and `padicValRat p 0 = 0`. At depth zero both formulations allow $`\gamma(1,0)=1`$.
8. **Section 7, row heights and the short basis.** For outer radius $`\rho_1=\rho+\delta`$, the paper integrates the counting lower bound $`A(y-\delta)_+^2`$, obtaining the upper bound $`A[\rho_1(\rho_1+\delta)^2-(\rho_1-\delta)_+^3/3]`$ for the row-height sum. Here $`(\rho_1-\delta)_+=\rho`$. Lean's `ballRowSum` uses $`(y-\delta)_+^2\ge y^2-2\delta y`$. Its bound is $`A[\rho_1(\rho_1+\delta)^2-\rho_1^3/3+\delta\rho_1^2+\rho_1^3/(2J)]`$ for each positive integer $`J`$. Letting $`J`$ grow removes the last term and retains the loss from the quadratic estimate. Lean constructs the short basis with `dirichletBasis`. The paper uses Minkowski's second theorem.
9. **Lemmas 7.2 and 7.3.** Lean obtains `selectedDiamondProvider` by applying `False.elim` to the contradiction supplied by `fineShellConflict`. Then `bandEngineOfSelectedDiamond` applies `packet.conflict`. The paper constructs the sites and their two determinant bounds in Lemma 7.2 and invokes Proposition 7.1 in Lemma 7.3.
10. **Proposition 8.1 and Lemma 8.2.** `CommonTailExclusion` expresses $`H<R^{1/3-\eta}`$ by negating the weak inequality in the opposite direction. `FixedMarginExterior` includes $`X\ge0`$. Lemma 8.2 takes its polynomial-cap constants $`(C_0,k)`$ from Proposition 2.1 independently of the constants in the exterior estimates. The final use of the polynomial cap and the tail bound is `twoNinthsOfPolycapAndTail`.

In the terminal argument, `SelectedDiamondProvider` supplies the determinant
data, `DiamondPacket` records the sites and height budget, and `BandEngine`
states the exclusion of high ordered triples satisfying both exterior estimates.

## Build and verification

Install [Elan](https://github.com/leanprover/elan) and Git. From the root of a
fresh checkout of this package, Elan reads `lean-toolchain` and Lake uses the
pinned `lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean SolutionAxioms.lean
```

`Challenge.lean` contains the statement for independent comparison, so the
default build reports its expected `sorry` warning. The axiom check for the
solution prints:

```text
'AbcTwoNinths.twoNinths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For the strict source and statement checks, start from a fresh checkout with
no project build directory and run:

```bash
lake exe cache get
bash verification/verify.sh
```

A reference strict build of the 361 proof modules took about 10 minutes with
about 7 GiB peak resident memory. The full fresh-checkout script, including
statement comparison, took about 46 minutes and reached about 12 GiB peak
resident memory. These timings exclude fetching the Mathlib cache. See
[verification/README.md](verification/README.md) for the checks performed.

## Citation

Ruiyi Zhang. *An upper bound for log c in the abc conjecture with exponent 2/9*.
Preprint, Zenodo, 2026. Theorem 1.1. DOI: [10.5281/zenodo.24405683](https://doi.org/10.5281/zenodo.24405683). [ORCID](https://orcid.org/0009-0003-3110-8524).
[Repository](https://github.com/ryzfsu/abc-log-bound-two-ninths).

## Use of AI tools

The author devised the method of proof. Codex (OpenAI, GPT-6 Astra) and Antigravity (Google, Gemini 4 Neon) ran blind reviews of the manuscript, and Codex assisted with the Lean formalization. Claude Code (Anthropic, Claude Fable 5) checked the proofs and the references. The author checked every step of the proof and every reference, and takes full responsibility for the content of the paper.

## Licence

The Lean source is licensed under the Apache License, Version 2.0.
See [LICENSE](LICENSE).
