# Rudin's conjecture on squares in arithmetic progressions from abc

**Alexey Kravatskiy**, MIRIAI (Moscow Independent Research Institute of Artificial Intelligence), Moscow, Russia.

This English-language preprint gives a conditional proof of the original square-root bound. It assumes the classical integer abc inequality at one fixed exponent and does not claim the stronger exact extremal conjecture. The matching [Lean formalization](../lean/) is in a separate directory. See the preprint’s Acknowledgments and the [repository README](../README.md#contributions-and-ai-use) for the author’s and Dot’s roles.

## Build

With a standard TeX Live installation:

    latexmk -pdf rudin-abc.tex

Alternatively, run pdfLaTeX, BibTeX, and then pdfLaTeX twice. The editable bibliography is in `references.bib`. The generated `rudin-abc.bbl` is included for source submission.
