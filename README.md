# MahlerLeanII

Lean 4 proofs accompanying Diego Marques, *Mahler's Problem on Liouville
Numbers II. Rational Maps*.

The author ran the build and axiom audit on macOS with Lean 4.24.0 on
31 October 2026. All 23 declarations required by the audit passed. They cover
the elementary inclusions in Lemma 2.1, the obstruction criterion in Lemma 5.1
and the algebraic part of the reconstruction argument in Lemma 4.1.

For reconstruction, `Reconstruction.rational_reconstruction_bounds` proves
(4.2) and (4.3) for the **same** integer vector and positive denominator.
The constants depend on the normalized polynomial pair and the pole-free
compact set and are chosen before the rational samples and their heights.
`Reconstruction.normalized_stability_on_compact` also gives the coefficient
error for arbitrary real ordinates. These are the estimates used in (5.14).
The global pole exclusion for the perturbed polynomial is a separate part
of Lemma 4.1. The counting, escape and classification results are tracked
in the roadmap.

See the [correspondence with the paper](docs/STATUS.md),
[Section 4 declarations](docs/SECTION4.md) and [verification record](docs/VERIFICATION.md).
Part I has a [separate repository](https://github.com/DiegoMarquesMath/MahlerLean).

## Reproduce the check

With elan installed, run from the repository root:

```bash
lake exe cache get
bash scripts/check.sh
```

The project pins mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
The script builds the project, checks each module with warnings treated as
errors and audits the transitive axiom dependencies of the declarations in
the project namespace. It permits `propext`, `Classical.choice` and
`Quot.sound`. The terminal output is saved in `build/verification.log`.

The [Lean verification workflow](.github/workflows/lean.yml) runs the same
script on pushes and pull requests. For citation, identify the commit whose
workflow passed and specify the corresponding results as in the
[citation guide](docs/CITATION.md).
