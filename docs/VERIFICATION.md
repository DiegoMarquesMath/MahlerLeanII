# Verification record

## Classification

GitHub Actions ran `bash scripts/check.sh` successfully on the
[proof commit `668b542bbd5b`](https://github.com/DiegoMarquesMath/MahlerLeanII/tree/668b542bbd5bb582e0dbf534e71375026c52b5fd).
The [workflow log](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/runs/41273103486) records the clean build, the individual
source checks with warnings treated as errors and the axiom audit.
All 51 required declarations were present. In particular the log contains

```text
AUDITED MahlerLeanII.rational_classification: [propext, Quot.sound, Classical.choice]
All project declarations use only the permitted standard axioms.
Build and axiom audit passed for the current declared scope.
```

Earlier stages were verified independently at
[coefficient reconstruction](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/runs/41271784169)
and [sparse counting and point escape](https://github.com/DiegoMarquesMath/MahlerLeanII/actions/runs/41272817424).
The [correspondence table](STATUS.md) identifies the manuscript statements covered.

## Earlier determinant revision

On 31 October 2026, the author ran `bash scripts/check.sh` on the Mac checkout
after applying the two Section 4 patches. The transcript identifies Lean
4.24.0 for `arm64-apple-darwin23.6.0`, compiler commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. Lake reported a successful
build (3100 jobs), including `ReconstructionMatrix` and the root module.
The audit listed all 23 required declarations. Its last two lines were:

```text
All project declarations use only the permitted standard axioms.
Build and axiom audit passed for the current declared scope.
```

Five declarations concern elementary inclusions and the obstruction criterion.
The other eighteen are the nine algebraic and general determinant results of
the first Section 4 block and the nine results for the normalized matrix in
the second block. The latter include `reconstruction_coefficient_det_ne_zero`,
`normalized_det_factorization` and `reconstruction_determinant_constant`.

This record describes the author's local run. The transcript identifies the
Lean compiler commit. The project commit for a paper citation should be taken
from the successful GitHub Actions run at the published revision.
