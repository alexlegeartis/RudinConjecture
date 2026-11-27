# Rudin's conjecture on squares in arithmetic progressions

A conditional proof of Rudin's original conjecture, by **Alexey Kravatskiy** (MIRIAI, Moscow).

[Read the preprint (PDF)](preprint/rudin-abc.pdf) · [LaTeX source and bibliography](preprint/)

## Result

Assume the classical integer **abc conjecture** at one fixed exponent \(1+\varepsilon\), with \(0<\varepsilon<1/3\). Then every arithmetic progression of length \(N\) and nonzero common difference contains \(O(\sqrt N)\) squares, with a constant independent of its initial term and common difference. This proves the original square-root bound under the stated hypothesis. It does not prove the stronger claim that the progression \(1,25,49,\ldots\) always attains the maximum for \(N\ge6\).

The proof uses five representations of the same integer as a sum of two squares. Gaussian factorization and the Plücker relation give quartic equations to which abc applies. A weighted cut argument bounds the common difference polynomially, and a count of roots modulo that difference gives the square-root bound.

## Build and status

With TeX Live and `latexmk` installed, run:

    cd preprint
    latexmk -pdf rudin-abc.tex

The preprint is available here on GitHub. No arXiv identifier is assigned yet. Lean formalization is planned; this repository does not currently contain a Lean-verified proof.

## Cite

Alexey Kravatskiy, *Rudin's conjecture on squares in arithmetic progressions from abc*, preprint, November 2026. For a reproducible citation, use a GitHub permalink to the version you read.
