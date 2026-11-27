import RudinABC.Cuts
import Mathlib.Tactic.FinCases

/-! # The elementary rounding argument in preprint §4, equation (7)
Use twice each valuation so that the half-error bounds stay integral.
The tie is always assigned to the low side, once and for all.
-/

namespace RudinABC

/-- Whether the exponent is closer to `e` than to zero. -/
def highBit (e a : ℕ) : Bool := decide (e < 2*a)

def idealSame (e a b : ℕ) : ℕ := if highBit e a = highBit e b then e else 0

/-- The absolute error in an edge norm, expressed as two inequalities
after multiplying by 2. This is the preprint's rounding estimate. -/
theorem rounded_gcd_edge (e a b da db : ℕ)
    (ha : a≤e) (hb : b≤e) (hda : 2*min a (e-a)≤da) (hdb : 2*min b (e-b)≤db) :
    let actual := min a b + min (e-a) (e-b)
    let ideal := idealSame e a b
    2*actual ≤ 2*ideal+da+db ∧ 2*ideal ≤ 2*actual+da+db := by
  dsimp [idealSame,highBit]
  by_cases ha' : e < 2*a <;> by_cases hb' : e < 2*b <;>
    simp only [ha',hb',decide_true,decide_false,Bool.true_eq_false,
      Bool.false_eq_true,if_true,if_false] <;>
    simp only [Nat.min_def] at * <;>
    split_ifs at * <;> omega

/-- In the three pairings on a quartet, the ideal exponent divided by e
is the number of equal-label edges in the matching. -/
def matchingEqualCount (s : Finset (Fin 5)) (o : Fin 5) (r : Fin 3) : ℕ :=
  let X := pairing r
  let b := fun i => sideBit s (retained o i)
  (if b X.1.1 = b X.1.2 then 1 else 0) + (if b X.2.1 = b X.2.2 then 1 else 0)

def min3 (f : Fin 3 → ℕ) : ℕ := min (f 0) (min (f 1) (f 2))

/-- The 2-2 pattern is exactly what survives subtraction of the
common minimum; its matching term retains two copies of the exponent. -/
theorem matchingEqualCount_after_min :
    ∀ (s : Finset (Fin 5)) (o : Fin 5) (r : Fin 3),
      matchingEqualCount s o r - min3 (matchingEqualCount s o) =
        if matchesPairing s o r then 2 else 0 := by decide

theorem min3_le (f : Fin 3 → ℕ) (r : Fin 3) : min3 f ≤ f r := by
  fin_cases r <;> simp [min3]

theorem le_min3 (f : Fin 3 → ℕ) (n : ℕ) (h : ∀ r, n ≤ f r) :
    n ≤ min3 f := by
  unfold min3
  exact le_min (h 0) (le_min (h 1) (h 2))

theorem min3_attained (f : Fin 3 → ℕ) : ∃ r, min3 f = f r := by
  by_cases h01 : f 0 ≤ min (f 1) (f 2)
  · exact ⟨0,min_eq_left h01⟩
  · rw [min3,min_eq_right (le_of_not_ge h01)]
    rcases le_total (f 1) (f 2) with h | h
    · exact ⟨1,min_eq_left h⟩
    · exact ⟨2,min_eq_right h⟩

/-- Both actual and ideal minima differ by no more than half the common
budget. Subtracting the minima therefore doubles the possible error. -/
theorem after_min_error (X I : Fin 3 → ℕ) (D : ℕ)
    (h : ∀ r, 2*X r ≤ 2*I r+D ∧ 2*I r ≤ 2*X r+D) :
    ∀ r, X r-min3 X ≤ I r-min3 I+D ∧ I r-min3 I ≤ X r-min3 X+D := by
  have h1 : 2*min3 X ≤ 2*min3 I+D := by
    obtain ⟨r,hr⟩ := min3_attained I
    have hh := min3_le X r
    have hi := (h r).1
    omega
  have h2 : 2*min3 I ≤ 2*min3 X+D := by
    obtain ⟨r,hr⟩ := min3_attained X
    have hh := min3_le I r
    have hi := (h r).2
    omega
  intro r
  have hX := min3_le X r
  have hI := min3_le I r
  have hr := h r
  omega

end RudinABC
