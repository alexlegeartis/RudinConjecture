/-
Copyright 2025–2026 The Formal Conjectures Authors.
The definitions below are copied verbatim under Apache-2.0 from
google-deepmind/formal-conjectures at ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8.
No proof stubs are included. See https://www.apache.org/licenses/LICENSE-2.0.
-/
import RudinABC.Statements
import RudinABC.ABC

namespace ABC

def radical (n : ℕ) : ℕ := n.primeFactors.prod id

end ABC

namespace RudinsConjecture

noncomputable abbrev Q (N q a : ℕ) : ℕ := {n : ℕ | n < N ∧ IsSquare (q * n + a)}.ncard

def IsNontrivial (q a : ℕ) : Prop :=
  1 ≤ q ∧ 1 ≤ a ∧ Nat.Coprime q a ∧ (q, a) ≠ (1, 1)

noncomputable def Qmax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}

end RudinsConjecture
