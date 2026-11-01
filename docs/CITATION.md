# Citing the formalization

A sentence for the paper is

```latex
A Lean~4 formalization of \Cref{thm:classification} is
available in \cite{MarquesLeanII}.
```

Use a revision whose **Lean verification** workflow passed and whose audit
lists `MahlerLeanII.rational_classification`. Cite its full commit hash to
identify the exact proof. For a manual bibliography, replace both instances
of `<COMMIT>` below with that hash.

```latex
\bibitem{MarquesLeanII}
D.~Marques, \emph{MahlerLeanII: Lean~4 formalization of the rational
classification in Mahler's problem on Liouville numbers},
commit~\texttt{<COMMIT>},
\url{https://github.com/DiegoMarquesMath/MahlerLeanII/tree/<COMMIT>}.
```
