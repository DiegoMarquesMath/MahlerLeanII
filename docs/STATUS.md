# Correspondence with the manuscript

The manuscript is Diego Marques, *Mahler's Problem on Liouville Numbers II.
Rational Maps*. The source used for the correspondence is `2-29OCT.tex`,
SHA-256 `bbebf03f5073299afc3e5403897466b5e9a50d082a6c8c372d63ad6e0b14e117`.

## Theorem 1.2

[`rational_classification`](../MahlerLeanII/Classification.lean) states the
three-way equivalence in `thm:classification` with `List.TFAE`. The only
hypothesis on `R : RatFunc ℝ` is nonconstancy, expressed by exclusion from
the image of `RatFunc.C`.

| Paper | Lean |
| --- | --- |
| (i) Membership in the rational function field over the coefficient field | Membership in the image of the ring homomorphism `coefficientEmbedding coefficientSubfield` |
| (ii) Rational or Liouville values at every Liouville argument off the poles | `Set.MapsTo` on the intersection of mathlib's `Liouville` set with `realDomain R` |
| (iii) The same inclusion on some nonempty open interval in the domain | `Set.Nonempty`, `IsOpen`, `Set.OrdConnected`, containment in `realDomain R` and the restricted `Set.MapsTo` predicate |

The domain is defined by the nonvanishing of mathlib's canonical reduced
denominator. Evaluation is `RatFunc.eval (RingHom.id ℝ)`. The codomain set
uses the ordinary image of the rationals in the reals and mathlib's
Liouville predicate.

## Proof dependencies

All declarations below are in the namespace `MahlerLeanII`.

| Manuscript result | Lean declaration | Role |
| --- | --- | --- |
| Definition 1.1 | `ScaleApproximable` | At each positive order, one exponent and one cutoff work at every subsequent integer scale. |
| Lemma 2.1 | `rational_scaleApproximable`, `scaleApproximable_rationalOrLiouville` | Elementary inclusions. |
| Lemma 2.2 | `simultaneous_approximation` | One denominator for a finite tuple at each sufficiently large scale. |
| Proposition 2.3 | `coefficientSubfield`, `mem_coefficientSubfield` | Field operations preserve the defining property. |
| Remark 2.4 | `definedOver_iff_normalized_coefficients` | Scalar extension agrees with membership of every normalized coefficient. |
| Proposition 3.1 | `evaluation_of_coefficients` | A rational function with such coefficients takes rational or Liouville values at Liouville arguments off its poles. |
| Lemma 4.1, (4.2) and (4.3) | `Reconstruction.rational_reconstruction_bounds` | The same reconstructed vector has both the perturbation and denominator bounds. See [Section 4](SECTION4.md). |
| Lemma 5.1 | `not_scaleApproximable_iff` | One obstruction order precedes the quantifiers on denominator exponents and cutoffs. |
| Proposition 5.3 | `Counting.two_height_count` | Uniform sparse-scale count for finite families of resonant centers. |
| Proposition 6.1, single-point consequence | `Escape.point_escape_of_sparse_count` | Nested intervals and exclusion of rational and Liouville images, including unreduced rational representations. |
| Theorem 1.3, single-point consequence | `escape_of_bad_coefficients` | Every nonempty open pole-free interval contains a witness when a normalized coefficient fails the field condition. |
| Theorem 1.2 | `rational_classification` | All three implications. |

Theorem 1.2 only needs one counterexample in each interval. The proof follows
one branch of the construction in Section 6. The perfect set and uniform
irrationality-exponent conclusions of Theorem 1.3, the remaining assertions
of the full interpolation lemma, and the subsequent corollaries and examples
are outside this verification claim.
