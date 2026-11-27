# Rudin's conjecture on squares in arithmetic progressions from abc

**Alexey Kravatskiy**, MIRIAI (Moscow Independent Research Institute of Artificial Intelligence), Moscow, Russia.

This English-language preprint gives a conditional proof of the original square-root bound. It assumes the classical integer abc inequality at one fixed exponent and does not claim the stronger exact extremal conjecture. A Lean formalization is not included in this directory.

## Build

With a standard TeX Live installation:

    latexmk -pdf rudin-abc.tex

Alternatively, run pdfLaTeX, BibTeX, and then pdfLaTeX twice. The editable bibliography is in `references.bib`. The generated `rudin-abc.bbl` is included for source submission.
