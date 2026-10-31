# Section 4: reconstruction

The author requested that formalization proceed from Section 4, having
reviewed Sections 1–3 manually. Manual review is not recorded as a Lean proof.
The reconstruction modules use mathlib and the project algebraic helpers;
they do not assume any unformalized coefficient-field result.

## First block: reported build and axiom audit passed

The author supplied the successful output of `bash scripts/check.sh` after
applying `MahlerLeanII-section4.patch`. Lean 4.24.0 on macOS built
`ReconstructionAlgebra`, `ReconstructionDeterminant` and the root module
(3095 jobs). The audit printed all 14 required declarations and concluded:

```text
All project declarations use only the permitted standard axioms.
Build and axiom audit passed for the current declared scope.
```

The nine Section 4 declarations checked in that run are:

| File | Declaration |
| --- | --- |
| `ReconstructionAlgebra.lean` | `kernel_trivial` |
| `ReconstructionAlgebra.lean` | `polynomial_map_injective` |
| `ReconstructionAlgebra.lean` | `relation_natDegree_le` |
| `ReconstructionAlgebra.lean` | `relation_eq_zero_of_samples` |
| `ReconstructionAlgebra.lean` | `kernel_trivial_of_samples` |
| `ReconstructionDeterminant.lean` | `evaluation_matrix_factorization` |
| `ReconstructionDeterminant.lean` | `evaluation_det_factorization` |
| `ReconstructionDeterminant.lean` | `evaluation_det_ne_zero` |
| `ReconstructionDeterminant.lean` | `divided_evaluation_det_factorization` |

All names are in namespace `MahlerLeanII.Reconstruction`. Their reported
transitive axioms are restricted to `propext`, `Classical.choice` and
`Quot.sound`. The other five audited results are the earlier elementary
inclusions and obstructed-scale lemmas. This is author-reported verification;
no independent GitHub Actions run or verified release is being claimed.

## Second block: reported build and axiom audit passed

`ReconstructionMatrix.lean` specializes the first block to the exact matrix
used in the manuscript. The author’s subsequent successful run included this
module. Its declarations include:

| Manuscript step | Declaration |
| --- | --- |
| The bounded-degree map in `eq:polynomial-map` | `boundedPolynomialMap` |
| Its injectivity from coprimality | `bounded_polynomial_map_injective` |
| Its columns are `X^j Q` and `-X^j P` | `bounded_polynomial_map_basis` |
| All column degrees are below the matrix size | `reconstruction_family_natDegree_lt` |
| The coefficient determinant is nonzero | `reconstruction_coefficient_det_ne_zero` |
| The manuscript's square matrix at arbitrary ordinates | `normalizedMatrix` |
| Its relation to polynomial evaluation at exact ordinates | `normalized_matrix_eq_divided_evaluation` |
| The formula in `eq:vandermonde-minor` | `normalized_det_factorization` |
| Nonsingularity at distinct, pole-free abscissae | `normalized_det_ne_zero` |
| A nonzero constant chosen before the abscissae | `reconstruction_determinant_constant` |

The coefficient determinant is proved nonzero using the injective polynomial
map and equality of the finite dimensions. It is not assumed as a new
hypothesis. The map's inverse is used only to establish invertibility of its
matrix. No new axiom or admitted proof is introduced.

The source file is imported by the root module. The audit now requires 23
principal declarations and continues checking transitive axioms of project
declarations. The author’s Lean 4.24.0 run passed all of these checks. See
[the run record](VERIFICATION.md).

## Hypotheses and boundary cases

- The dimension is written `(r+1)+s`, equal to the manuscript's `r+s+1`, to
  match the numerator and denominator coefficient blocks.
- The domain is `degreeLT Real (r+1) × degreeLT Real s`. The second factor is
  the zero space when `s=0`; no impossible natural-degree inequality for its
  zero polynomial is used.
- The nonzero determinant requires `IsCoprime P Q`, `Q ≠ 0`,
  `P.natDegree ≤ r` and **exactly** `Q.natDegree = s`. Merely bounding the
  denominator degree would not justify this conclusion.
- The determinant identity divides by `Q(x_i)` only under explicit nonzero
  hypotheses. Distinct abscissae are additionally required for nonsingularity.
- Monicity is not needed for this algebraic identity. The manuscript's monic
  reduced pair satisfies the stated hypotheses. Monicity of the reconstructed
  denominator still needs to be accounted for in the full interpolation lemma.
- The constant is the determinant of a matrix depending only on `P,Q,r,s`.
  For the manuscript's fixed degree parameters, it therefore depends only on
  the normalized rational function. Its existence is quantified before any
  choice of abscissae.

## Remaining parts of Lemma 4.1

The following steps remain to complete the formal proof:

1. Uniform determinant and cofactor bounds on the compact interval, including
   the perturbation estimate and the existence of the required constants.
2. Cramer's rule and the coefficient error bound `C₀ δ/V`.
3. The reconstructed denominator's nonvanishing on the whole interval and the
   resulting interpolation identities.
4. Clearing rational denominators and proving the common-denominator estimate
   `h ≤ C₀ S^(n*d) B^n`, with the manuscript's exact constant dependencies.

Neither the complete stable interpolation lemma nor the counting or Cantor
construction is claimed as formalized by these two blocks.
