# Mahler's Problem on Liouville Numbers II. Rational Maps

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/workflows/lean.yml)

Lean 4 formalization of **Theorem 1.2** of Diego Marques's manuscript
*Mahler's Problem on Liouville Numbers II. Rational Maps*.

The theorem characterizes the real rational functions whose values at
Liouville numbers are rational or Liouville. A canonical subfield of the
reals determines exactly which functions have this property, and the same
coefficient condition follows from the inclusion on a single open interval.

## Theorem 1.2 — Rational classification

Let $\mathcal L$ denote the set of Liouville numbers and let $\mathbb L$ be
the coefficient field defined below. For a nonconstant rational function
$R\in\mathbb R(X)$, write $D_R$ for its real domain, excluding its poles.

The following conditions are equivalent.

1. $R\in\mathbb L(X)$.
2. $R(\mathcal L\cap D_R)\subseteq\mathbb Q\cup\mathcal L$.
3. There is a nonempty open interval $V\subseteq D_R$ such that
   $R(\mathcal L\cap V)\subseteq\mathbb Q\cup\mathcal L$.

The complete equivalence is proved in
[`MahlerLeanII.rational_classification`](MahlerLeanII/Classification.lean).
The Lean statement uses mathlib's `RatFunc ℝ` and `Liouville`, with the
domain defined by the nonvanishing of the canonical reduced denominator.

## The coefficient field

A real number $\alpha$ belongs to $\mathbb L$ if, for every integer
$N\ge1$, there are integers $D\ge1$ and $H_0\ge2$ such that every integer
$H\ge H_0$ admits $p\in\mathbb Z$ and $q\in\mathbb Z_{>0}$ satisfying

$$
q\le H^D,
\qquad
\left|\alpha-\frac pq\right|\le(Hq)^{-N}.
$$

The exponent and cutoff may depend on $\alpha$ and $N$, while the
approximation must exist at every subsequent scale $H$.

The development constructs this set as a subfield of $\mathbb R$ and proves

$$
\mathbb Q\subseteq\mathbb L\subseteq\mathbb Q\cup\mathcal L.
$$

Membership in $\mathbb L(X)$ is represented by the natural embedding of
rational function fields. It is proved equivalent to all coefficients of
the monic reduced pair belonging to $\mathbb L$.

## Proof architecture

1. **Simultaneous approximation and rational evaluation.** A common
   denominator for finite families of coefficients gives the field structure
   and the implication from the coefficient condition to rational or
   Liouville values.
2. **Reconstruction and counting.** Nearby rational values reconstruct the
   normalized coefficients with controlled error and a common denominator.
   At scales where a coefficient fails the defining approximation property,
   these bounds limit the number of rational arguments with sufficiently
   accurate rational images.
3. **Nested intervals and necessity.** The counting estimate supplies a
   Liouville point whose image is irrational and non-Liouville in every
   nonempty open interval without poles. This proves the converse implication.

## Correspondence with the Lean development

Declaration names below are relative to the namespace `MahlerLeanII`.

| Manuscript result | Lean declaration |
| --- | --- |
| Lemma 2.1 — elementary inclusions | [`rational_scaleApproximable`, `scaleApproximable_rationalOrLiouville`](MahlerLeanII/Basic.lean) |
| Lemma 2.2 — simultaneous approximation | [`simultaneous_approximation`](MahlerLeanII/Synchronization.lean) |
| Proposition 2.3 — field structure | [`coefficientSubfield`](MahlerLeanII/CoefficientField.lean) |
| Remark 2.4 — normalized coefficients | [`definedOver_iff_normalized_coefficients`](MahlerLeanII/RationalCoefficients.lean) |
| Proposition 3.1 — rational evaluation | [`evaluation_of_coefficients`](MahlerLeanII/RationalEvaluation.lean) |
| Lemma 4.1 — coefficient error and denominator bounds, (4.2)–(4.3) | [`Reconstruction.rational_reconstruction_bounds`](MahlerLeanII/RationalReconstruction.lean) |
| Lemma 5.1 — obstructed scales | [`not_scaleApproximable_iff`](MahlerLeanII/Obstruction.lean) |
| Proposition 5.3 — two-height counting | [`Counting.two_height_count`](MahlerLeanII/TwoHeightCount.lean) |
| Proposition 6.1 — single-point consequence | [`Escape.point_escape_of_sparse_count`](MahlerLeanII/SparseEscape.lean) |
| Theorem 1.3 — single-point consequence | [`escape_of_bad_coefficients`](MahlerLeanII/RationalEscape.lean) |
| Theorem 1.2 — complete classification | [`rational_classification`](MahlerLeanII/Classification.lean) |

The detailed correspondence records the hypotheses and scope of each
formal statement. [Manuscript correspondence](docs/STATUS.md)

## Verification

The formalization uses **Lean 4.24.0**. The toolchain and dependency revisions
are fixed in `lean-toolchain` and `lake-manifest.json`.

With [elan](https://github.com/leanprover/elan) installed, run

```bash
git clone https://github.com/DiegoMarquesMath/MahlerLeanII.git
cd MahlerLeanII
lake exe cache get
bash scripts/check.sh
```

The verification script builds the complete project, checks every project
source with warnings treated as errors, and audits the transitive axioms
of every declaration in the project namespace. It also requires the
presence of 51 principal declarations. The permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The log is saved to `build/verification.log`. For the main theorem, the
verified run records

```text
AUDITED MahlerLeanII.rational_classification: [propext, Quot.sound, Classical.choice]
All project declarations use only the permitted standard axioms.
Build and axiom audit passed for the current declared scope.
```

The proof is available at the verified commit
[`668b542bbd5bb582e0dbf534e71375026c52b5fd`](https://github.com/DiegoMarquesMath/MahlerLeanII/tree/668b542bbd5bb582e0dbf534e71375026c52b5fd).
The corresponding build and audit passed on GitHub Actions.
[Verification run](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/runs/41273103486) · [Verification record](docs/VERIFICATION.md)

## Scope and relation to Part I

The completed formalization covers Theorem 1.2 and the results needed for
both directions of its classification. The necessity argument uses the
single-point conclusion of the escape construction. The full Cantor-set
and uniform irrationality-exponent conclusions of Theorem 1.3, along with
the subsequent corollaries and examples, are further formalization work.
[Remaining scope](docs/ROADMAP.md)

Part I establishes analytic rigidity, reducing the preservation problem
for real-analytic functions to rational functions. The present theorem
identifies the coefficient condition for rational maps. Its proof is
independent of the analytic rigidity theorem. [Part I repository](https://github.com/DiegoMarquesMath/MahlerLean)

This project imports elementary Farey, approximation and interval lemmas
from Part I at a fixed revision. Both that revision and the mathlib revision
are recorded in the dependency configuration. [Pinned dependencies](lakefile.toml)

## Citation

Suggested wording for the manuscript is

> A Lean 4 formalization of the rational classification theorem
> (Theorem 1.2) is available in the MahlerLeanII repository.

The citation guide includes a ready-to-use LaTeX sentence and bibliography
entry identifying the exact verified commit. [Citation guide](docs/CITATION.md)

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
