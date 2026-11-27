# Rudin's conjecture on squares in arithmetic progressions, conditional on abc

Lean 4 formalization of Alexey Kravatskiy's [preprint proof at 8dc8f1d](https://github.com/alexlegeartis/RudinConjecture/blob/8dc8f1d21c697c9f304612843091fa36e269439a/preprint/rudin-abc.tex), following its Gaussian factorization, Plücker, weighted-cut and CRT argument at ε = 1/4. Classical abc is a hypothesis. The stronger 24n+1 maximizer conjecture is not part of this formalization.

- `RudinABC.uniformIntegerRudin_of_classicalABC`: one bound `C * sqrt N` for the squares in every length-N progression with signed integer starting term and nonzero signed integer difference.
- `RudinABC.formalConjectures_abc_implies_rudin`: the exact ordinary `RudinsConjecture.Qmax` Big-O type from [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8), with the precise classical abc finite-exceptions statement as an explicit hypothesis.
- [English ↔ Lean crosswalk](CROSSWALK.md): declaration-by-declaration correspondence and technical representations.

## Replay

Use [elan](https://github.com/leanprover/elan) with the included `lean-toolchain`. The lock file pins Lean v4.33.1 / 819816b2 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. In this directory:

```sh
# Optional: skip compiling Mathlib by downloading compiled imported dependencies.
./tools/fetch-cache.sh
./tools/verify.sh --clean
```

`verify.sh` checks the proof sources, builds the project, and audits the declarations with `#print axioms`. Only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` are admitted by the audit. Neither `sorryAx` nor an axiom for abc is a dependency.

`CanonicalDefinitions.lean` contains only the four definitions copied verbatim from the pinned DeepMind revision, with its Apache-2.0 attribution. It contains none of that repository's conjecture stubs. Check the exact source pins with:

```sh
python3 tools/extract_pinned_definitions.py --check RudinABC/CanonicalDefinitions.lean
```

The standalone proof verifies the exact named upstream statement with those definitions. For a downstream replay **inside** the original Formal Conjectures environment, use `integration/CheckDeepMind.lean` with both packages at the pinned revisions. It imports `RudinABC.Main` rather than `RudinABC` to avoid redeclaring the four upstream definitions. The combined full-upstream application was not part of the standalone local replay.
