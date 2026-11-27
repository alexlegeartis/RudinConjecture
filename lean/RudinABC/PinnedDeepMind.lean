import RudinABC.Main
import RudinABC.CanonicalDefinitions

/-! # Exact-source, official-name statement compatibility
Only the four definitions copied verbatim at the pinned revision are needed.
The independent full-upstream adapter has the same theorem body.
-/

namespace RudinABC

open Filter Asymptotics

/-- The Nat Qmax definitions are definitionally equal, not merely
comparable asymptotically. -/
theorem pinned_qmax_defeq (N : ℕ) : RudinsConjecture.Qmax N = Upstream.Qmax N := rfl

/-- Exact DeepMind theorem conclusion, assuming its explicit classical ABC
finite-exceptions assertion as a theorem argument. -/
theorem formalConjectures_abc_implies_rudin
    (h : ∀ (ε : ℝ), 0 < ε →
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
        ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
        (ABC.radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite) :
    (fun N : ℕ => (RudinsConjecture.Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  change ClassicalABC at h
  change (fun N : ℕ => (Upstream.Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N
  exact rudin_of_classicalABC h

end RudinABC
