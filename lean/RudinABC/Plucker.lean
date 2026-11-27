import Mathlib.Tactic.Ring

/-! # Four vectors and the Plücker relation (preprint §4, eq. (5)) -/

namespace RudinABC

/-- Signed determinant of two two-dimensional column vectors. -/
def minor {R : Type*} [Ring R] (x y : R × R) : R :=
  x.1 * y.2 - x.2 * y.1

theorem plucker {R : Type*} [CommRing R] (x₁ x₂ x₃ x₄ : R × R) :
    minor x₁ x₂ * minor x₃ x₄ + minor x₁ x₄ * minor x₂ x₃ =
      minor x₁ x₃ * minor x₂ x₄ := by
  unfold minor
  ring

/-- After substituting the Gaussian minor formula, the common factor (q²)
cancels exactly. This is the preprint's `A₁ X₁² + A₂ X₂² = A₃ X₃²`. -/
theorem plucker_cancel_common_factor {R : Type*} [CommRing R] [IsDomain R]
    (x₁ x₂ x₃ x₄ : R × R) (q j₁₂ j₃₄ j₁₄ j₂₃ j₁₃ j₂₄ k₁₂ k₃₄ k₁₄ k₂₃ k₁₃ k₂₄ : R)
    (hq : q ≠ 0)
    (h₁₂ : minor x₁ x₂ = q*j₁₂*k₁₂^2) (h₃₄ : minor x₃ x₄ = q*j₃₄*k₃₄^2)
    (h₁₄ : minor x₁ x₄ = q*j₁₄*k₁₄^2) (h₂₃ : minor x₂ x₃ = q*j₂₃*k₂₃^2)
    (h₁₃ : minor x₁ x₃ = q*j₁₃*k₁₃^2) (h₂₄ : minor x₂ x₄ = q*j₂₄*k₂₄^2) :
    (j₁₂*j₃₄)*(k₁₂*k₃₄)^2 + (j₁₄*j₂₃)*(k₁₄*k₂₃)^2 =
      (j₁₃*j₂₄)*(k₁₃*k₂₄)^2 := by
  have hp := plucker x₁ x₂ x₃ x₄
  rw [h₁₂,h₃₄,h₁₄,h₂₃,h₁₃,h₂₄] at hp
  refine mul_left_cancel₀ (pow_ne_zero 2 hq) ?_
  calc
    _ = (q*j₁₂*k₁₂^2)*(q*j₃₄*k₃₄^2) + (q*j₁₄*k₁₄^2)*(q*j₂₃*k₂₃^2) := by ring
    _ = (q*j₁₃*k₁₃^2)*(q*j₂₄*k₂₄^2) := hp
    _ = _ := by ring

end RudinABC
