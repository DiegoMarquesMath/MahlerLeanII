# Formalization roadmap

## First checkpoint: make the initial project compile

Run `lake exe cache get` and `bash scripts/check.sh`. Resolve every elaboration
or proof error without changing the mathematical statements, introducing
admitted proofs, or weakening the audit. Update `docs/STATUS.md` only after a
successful check. A statement mismatch requires an explicit explanation and
review, not a silent replacement.

## Coefficient field

1. Formalize simultaneous approximation for a finite family. Preserve the
   order of dependence of all exponents and thresholds. In the induction,
   approximate the previous family at scale `H*k`, then use common denominator
   `h=k*l`; check the bound `D_b + D_a*(D_b+1)`.
2. Prove closure under subtraction, addition, multiplication and reciprocal
   using the exact scale definition. Construct a `Subfield ℝ` with carrier
   `coefficientSet`; do not assume such a structure beforehand.
3. Prove the normalization statement for a reduced rational function. Retain
   coprimality after extending the coefficient field and account for the
   nonzero normalization coefficient.

## Rational evaluation

Formalize Proposition 3.1, with nonzero denominators at the evaluation point.
Track the common coefficient denominator, degree and reduced denominator of
the rational approximations. Show separately that an irrational limit yields
unbounded reduced denominators. Check that constants and rational images are
handled without assuming every image is Liouville.

## Necessity of the coefficient condition

1. Reconstruction: prove the kernel dimension, Vandermonde minor,
   perturbation bound, preservation of a pole-free compact interval and
   common-denominator estimate.
2. Counting: prove the elementary rational supply and separation bounds,
   then the small and large target-height estimates. Keep constants uniform
   in the source interval and target cutoff. The sets of scales may depend
   on the approximation order and need only be unbounded.
3. Cantor construction: prove containment, separation, shrinking diameters,
   perfection, Liouville membership and avoidance at **all** sufficiently
   large target denominators, including unreduced representations. Avoidance
   for reduced fractions alone does not automatically exclude rational images.
4. Derive the escape theorem and classification, with pole exclusions and
   local/global quantifiers matching the paper.

## Further results

Formalize the fixed-gap example, the strengthened non-generation statement,
and the absence of a uniform escape exponent. Treat the real-analytic and
entire consequences as a separate layer depending on the verified Part I
rigidity result.

## Reuse from Part I

Potentially relevant files in `DiegoMarquesMath/MahlerLean` include the
Liouville bridge, Farey estimates, Cantor construction and irrationality
exponent lemmas. Inspect exact hypotheses and licensing before copying or
depending on them. Pin any dependency to a specific commit; shared names do
not establish that a theorem applies here.
