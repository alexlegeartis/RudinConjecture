import RudinABC.Main
import FormalConjectures.Wikipedia.ABC
import FormalConjectures.Wikipedia.RudinsConjecture

/-!
Optional downstream verification using the original upstream modules.
Build in an environment containing this project and the pinned official
Formal Conjectures project. Do not also import CanonicalDefinitions there.
-/

open Filter Asymptotics

theorem formalConjectures_abc_implies_rudin
    (h : ∀ (ε : ℝ), 0 < ε →
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
        ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
        (ABC.radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite) :
    (fun N : ℕ => (RudinsConjecture.Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  change RudinABC.ClassicalABC at h
  change (fun N : ℕ => (RudinABC.Upstream.Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N
  exact RudinABC.rudin_of_classicalABC h

#print axioms formalConjectures_abc_implies_rudin
