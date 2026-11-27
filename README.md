# Rudin's conjecture on squares in arithmetic progressions

A preprint by **Alexey Kravatskiy** (MIRIAI, Moscow) on the implication from [abc](https://en.wikipedia.org/wiki/Abc_conjecture) to [Rudin’s original conjecture](https://en.wikipedia.org/wiki/Rudin%27s_conjecture). The proof and its Lean 4 formalization were developed with OpenAI’s Dot.

[Read the preprint (PDF)](preprint/rudin-abc.pdf) · [LaTeX source and bibliography](./preprint/README.md) · [Lean verification](lean/README.md) · [Exact Lean theorem](https://github.com/alexlegeartis/RudinConjecture/blob/3fd777450db94362b38a173a2b0652daca43a6e7/lean/RudinABC/PinnedDeepMind.lean#L19)

## Result

Assume the classical integer [**abc conjecture**](https://en.wikipedia.org/wiki/Abc_conjecture) at one fixed exponent $1+\varepsilon$, with $0<\varepsilon<1/3$. Then every arithmetic progression of length $N$ and nonzero common difference contains $O(\sqrt N)$ squares, with a constant independent of its initial term and common difference. This proves the original square-root bound under the stated hypothesis. It does not prove the stronger claim that the progression $1,25,49,\ldots$ always attains the maximum for $N\ge6$.

The proof uses five representations of the same integer as a sum of two squares. Gaussian factorization and the Plücker relation give quartic equations to which abc applies. A weighted cut argument bounds the common difference polynomially, and a count of roots modulo that difference gives the square-root bound. The [introduction](preprint/rudin-abc.pdf#page=1) explains the difference from the earlier circle and $abc$ approaches.

## Contributions and AI use

Alexey Kravatskiy posed the problem and asked whether the Riemann hypothesis could be used to prove Rudin’s conjecture. OpenAI’s Dot, using GPT-6.2 Astra with Ultra reasoning effort, proposed the route through the classical abc conjecture and developed the conditional proof. At Kravatskiy’s request, Dot also formalized the same argument in Lean 4.

## Build and status

With TeX Live and `latexmk` installed, run:

    cd preprint
    latexmk -pdf rudin-abc.tex

The preprint is available here on GitHub. No arXiv identifier is assigned yet. The [Lean 4 project](lean/README.md) verifies the same argument at $\varepsilon=1/4$, with classical abc as an explicit hypothesis. The final theorem is [`RudinABC.formalConjectures_abc_implies_rudin`](https://github.com/alexlegeartis/RudinConjecture/blob/3fd777450db94362b38a173a2b0652daca43a6e7/lean/RudinABC/PinnedDeepMind.lean#L19), in the exact pinned DeepMind `Qmax` formulation. See the [proof crosswalk](lean/CROSSWALK.md) and [verification record](lean/VERIFICATION.txt).

## Cite

Alexey Kravatskiy, *Rudin's Conjecture on Squares in Arithmetic Progressions from the abc Conjecture*, preprint, November 2026. For a reproducible citation, use a GitHub permalink to the version you read. Citation metadata is in [`CITATION.cff`](CITATION.cff).
