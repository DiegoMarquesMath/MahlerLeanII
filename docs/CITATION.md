# Citing the formalization

Once GitHub Actions has passed on the revision used for the paper, cite the
full commit hash in the bibliography. The following sentence identifies the
scope of the author's successful local check.

```latex
Lean~4 formalizations of the elementary inclusions in
\Cref{lem:elementary-field}, the obstruction criterion in
\Cref{lem:obstruction}, and the determinant identity
\eqref{eq:vandermonde-minor} are available in \cite{MarquesLeanII}.
```

For a bibliography using `thebibliography`, replace both occurrences of
`<COMMIT>` below with the same full hash.

```latex
\bibitem{MarquesLeanII}
D.~Marques, \emph{MahlerLeanII: Lean~4 proofs for Mahler's Problem on
Liouville Numbers II. Rational Maps}, commit~\texttt{<COMMIT>},
\url{https://github.com/DiegoMarquesMath/MahlerLeanII/tree/<COMMIT>}.
```

The [Section 4 record](SECTION4.md) lists the determinant results and the
remaining estimates in the stable interpolation lemma.
