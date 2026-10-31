# Working instructions for MahlerLeanII

This project formalizes results of Diego Marques's Part II manuscript. The
initial sources have not yet compiled. Read README.md and docs/STATUS.md first.

## Required mathematical fidelity

- Keep mathlib's standard `Liouville` predicate.
- Preserve Definition 1.1 exactly: for each positive order there exist an
  exponent and cutoff valid at every subsequent integer scale.
- Do not assume the field structure or classification as a hypothesis or axiom.
- Do not strengthen hypotheses, weaken conclusions, or redefine a predicate
  to make a theorem easy to prove. Explain genuine statement changes first.
- Track nonzero denominators, unreduced target fractions, interval restrictions,
  uniform constants and the order of quantifiers explicitly.

## Proof checks

- No `sorry`, `admit`, custom mathematical axioms, `native_decide`, unchecked
  kernel options, or replacement of mathematical declarations by unsafe code.
- Retain the axiom audit. Only `propext`, `Classical.choice` and `Quot.sound`
  are permitted among transitive axioms of project declarations.
- Run `bash scripts/check.sh` after a substantive proof change. If Lean cannot
  run, report that blocker; do not claim that the proof has been verified.
- A completed result needs a manuscript label, exact formal declaration,
  successful check and documented scope. Add each new principal theorem to
  the required-declarations list in `scripts/Audit.lean`.
- Keep the root import file exhaustive for project mathematical modules.
  Do not hide incomplete files outside the build and call the project complete.

## Project boundaries

- Keep Lean and mathlib versions pinned unless there is an explained reason
  to update them. Commit the Lake manifest.
- Do not alter the Part I repository, paper files, audit script or workflow
  simply to obtain a passing build.
- Do not mark all of Part II as formalized when only the initial lemmas pass.
- Never store access tokens, passwords, local credential files, `.lake`, or
  downloaded toolchain binaries in Git.
