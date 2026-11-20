# Lean formalization of Theorem 1.1

`AbcTwoNinths.twoNinths` proves the uniform bound on `Real.log c` stated in
Ruiyi Zhang's *An upper bound for log c in the abc conjecture with exponent 2/9*.
The statement uses positive coprime natural numbers `a` and `b` with sum `c`
and the product of the distinct prime factors of `a * b * c`.

`Challenge.lean` presents the statement using only Mathlib. `Solution.lean`
provides the proof, and `PaperMap.lean` indexes the numbered results. The
[paper comparison](README.md#differences-from-the-paper) records differences
in intermediate arguments and quantitative bounds.

The toolchain is `leanprover/lean4:v4.35.0-rc4` with Mathlib at
`25e572b8074098af3f09d4cb2a4231cbdc584534`. To check the package hashes, run
`sha256sum -c SHA256SUMS SOURCE-SHA256SUMS`. The
[verification instructions](verification/README.md) give the commands for
the strict build, statement comparison and theorem axiom check.
