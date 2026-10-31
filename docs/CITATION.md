# Citation and scope

The initial commit is an unverified development project. It must not be cited
as evidence that the paper, its classification theorem, or its initial lemmas
have already been checked by Lean.

After the initial lemmas compile, pass the axiom audit and have their statements
reviewed against the paper, a precise manuscript sentence is:

```latex
The inclusions in \Cref{lem:elementary-field} and the obstruction
criterion in \Cref{lem:obstruction} have been formalized in Lean~4;
the source files and reproduction instructions are available
in \cite{MarquesLeanII}.
```

Use that sentence only after these specific claims have been established.
It does not claim formalization of the field structure, counting argument,
escape theorem or classification. Expand the sentence only when those proofs
are actually present and checked.

For a bibliography using `thebibliography`, the following is a template.
Replace the angle-bracket fields with the actual version and full commit hash;
do not leave placeholders in a submitted manuscript.

```latex
\bibitem{MarquesLeanII}
D.~Marques,
\emph{MahlerLeanII: Lean~4 formalization for Mahler's Problem
on Liouville Numbers II},
version~\texttt{<verified-tag>},
\url{https://github.com/DiegoMarquesMath/MahlerLeanII/tree/<full-commit-hash>}.
```

For a verified release:

1. Run `bash scripts/check.sh` and review the formal statements.
2. Update `docs/STATUS.md` and `CITATION.cff` to report exactly what is verified.
3. Commit and push. Check that GitHub Actions passes on that exact commit.
4. Create a release tag at that commit and record the tag and full hash in
   the citation. Use the repository URL only after publication actually exists.

Example release commands, to be executed only after these conditions hold:

```bash
git rev-parse HEAD
gh release create v0.1.0 --target main \
  --title "v0.1.0: elementary inclusions and obstructed scales" \
  --notes-file docs/STATUS.md
```

Confirm the release points to the checked commit. A release or DOI is a means
of identifying a version; neither substitutes for proof checking. A DOI may
be added later through an archival service if desired.
