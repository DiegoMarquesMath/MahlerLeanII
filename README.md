# MahlerLeanII

Lean 4 formalization project for Diego Marques,
*Mahler's Problem on Liouville Numbers II. Rational Maps*.

**Status: initial development sources; compilation and axiom audit have not
yet passed. This repository does not currently certify any theorem of the paper.**

The initial files propose formal statements and proofs for Definition 1.1,
Lemma 2.1 and Lemma 5.1. The coefficient field structure, rational evaluation,
counting argument, Cantor construction and classification are not yet formalized.
See [the exact scope](docs/STATUS.md) and [the roadmap](docs/ROADMAP.md).

The development uses mathlib's `Liouville` predicate. It does not define
Liouville numbers by the manuscript's scale property or assume the
classification as an axiom.

## Reproduce the proposed proofs

Lean and mathlib are pinned to the versions used by the Part I project:

- Lean: `leanprover/lean4:v4.24.0`.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (`v4.24.0`).

With `elan` installed, run from this directory:

```bash
lake exe cache get
bash scripts/check.sh
```

The second command builds the project, checks its source files with warnings
treated as errors, and audits the transitive axioms of every declaration in
the `MahlerLeanII` namespace. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. It also requires all five intended initial theorem
declarations to be present. The log is written to `build/verification.log`.
An unsuccessful command is not a verification result.

The GitHub Actions workflow repeats these checks on pushes and pull requests.
Its configuration is included, but no successful workflow run is being claimed
for this initial commit.

## Relation to Part I

The separate Part I repository is
<https://github.com/DiegoMarquesMath/MahlerLean>. This project currently has
no dependency on its proofs. Any future reuse must cite the originating file
and pin the precise commit. The rational classification in Part II is to be
formalized independently; the analytic consequences additionally depend on
the analytic rigidity theorem of Part I.

## Publication and citation

The intended repository name is `DiegoMarquesMath/MahlerLeanII`. The initial
delivery is a local Git repository; it still needs to be created and pushed
to GitHub. Follow [the Portuguese instructions](docs/QUICKSTART-PT.md).

Do not describe the manuscript as formally verified on the basis of this
initial repository. A citable verified version needs a successful build and
axiom audit, a checked correspondence between statements and manuscript, and
an immutable commit or release tag. See [citation instructions](docs/CITATION.md).

## Initial environment limitation

The preparation environment installed the official Lean 4.24.0 toolchain,
but `lean --version` failed before loading any project source:

```text
error: failed to locate application
```

Consequently, the included Lean proofs remain candidates. The shell script
and project metadata can be checked separately, but those checks do not
establish that the Lean proofs compile. No admitted proof or replacement
axiom is used to conceal this limitation.
