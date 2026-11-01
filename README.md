# MahlerLeanII

Lean 4 formalization of Theorem 1.2 of Diego Marques, *Mahler's Problem on
Liouville Numbers II. Rational Maps*.

The main declaration is [`MahlerLeanII.rational_classification`](MahlerLeanII/Classification.lean).
For a nonconstant real rational function it proves the equivalence of three
conditions.

1. The function is defined over the coefficient field of Definition 1.1.
2. At each Liouville number in its real domain, its value is rational or Liouville.
3. The same holds on some nonempty open interval in its domain.

The coefficient field is constructed as a subfield of the reals. The proof
uses simultaneous approximation, rational reconstruction and counting at
obstructed scales. For necessity, nested intervals give a Liouville point
whose value is irrational and non-Liouville. This single-point conclusion
suffices for the equivalence. The full Cantor-set assertion of Theorem 1.3
is a separate result.

## Reproduce the proof

With elan installed, run the following in the repository root.

```bash
lake exe cache get
bash scripts/check.sh
```

The script builds the project, checks the Lean files with warnings treated
as errors, and audits transitive axioms. The permitted standard axioms are
`propext`, `Classical.choice` and `Quot.sound`. The output is written to
`build/verification.log`. GitHub Actions runs the same script on pushes
and pull requests.

The toolchain is Lean 4.24.0. The Lake manifest pins
[mathlib](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7)
and the [Part I repository](https://github.com/DiegoMarquesMath/MahlerLean/tree/145368f4a99befffec239d285fdef0adefd53aed).
The imports from Part I supply elementary Farey estimates and lemmas about
rational approximation and intervals. The proof of Theorem 1.2 is independent
of the analytic rigidity theorem of Part I.

[Manuscript correspondence](docs/STATUS.md) · [Verification record](docs/VERIFICATION.md) · [Citation](docs/CITATION.md)
