# An upper bound for log c in the abc conjecture with exponent 2/9

Ruiyi Zhang

DOI: [10.5281/zenodo.24405683](https://doi.org/10.5281/zenodo.24405683)

For positive coprime integers $a+b=c$, put $R=\mathrm{rad}(abc)$.
Theorem 1.1 gives $\log c\ll_\varepsilon R^{2/9+\varepsilon}$ for every
$\varepsilon>0$.

## Contents

- [Paper](main.pdf) and [LaTeX source](source/)
- [Lean formalization](lean/) and its [README](lean/README.md)

## Lean formalization

The Lean 4 formalization of Theorem 1.1 is in [lean/](lean/). The same tree
is at the root of the [palomar](https://github.com/ryzfsu/abc-log-bound-two-ninths/tree/palomar)
branch. The main declaration, `AbcTwoNinths.twoNinths`, proves this statement:

```lean
def twoNinthsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : Nat, TwoNinthsTriple a b c →
      Real.log c ≤ C * (radNat (a * b * c) : ℝ) ^ ((2 : ℝ) / 9 + ε)
```

## Build

See [BUILD.md](BUILD.md) for the LaTeX build and the
[Lean README](lean/README.md) for build and verification commands. The root
`SHA256SUMS` covers the paper package. The Lean package has its own checksums.

## License

The paper and its source are licensed under CC BY 4.0. The Lean formalization
is licensed under Apache 2.0. See [LICENSE.md](LICENSE.md) for details.

## Citation

Ruiyi Zhang, *An upper bound for log c in the abc conjecture with exponent 2/9*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.24405683

```bibtex
@misc{zhang2026twoninths,
  author    = {Zhang, Ruiyi},
  title     = {An upper bound for $\log c$ in the $abc$ conjecture with exponent $2/9$},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.24405683},
  url       = {https://doi.org/10.5281/zenodo.24405683}
}
```
