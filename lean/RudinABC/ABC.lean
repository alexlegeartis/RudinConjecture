import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The classical finite-exceptions hypothesis and the quarter-power form

The definitions of `radical` and the exceptional set match DeepMind's
`FormalConjectures/Wikipedia/ABC.lean`. The conjecture is a theorem argument,
not an axiom and not a reference to the placeholder proof in that file.
-/

namespace RudinABC

/-- Product of the distinct prime factors, including the empty product. -/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/-- This predicate spells out the conclusion of the upstream `ABC.abc` verbatim. -/
def ABCExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {(a, b, c) : ℕ × ℕ × ℕ |
    0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}

/-- Classical integer ABC, as an explicit hypothesis. -/
def ClassicalABC : Prop :=
  ∀ (ε : ℝ), 0 < ε → (ABCExceptions ε).Finite

/-- Equation (1) in the preprint at ε=1/4, raised to the fourth power.
The positive natural constant absorbs the fourth power of the real constant. -/
def abcAtQuarter : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ a b c : ℕ,
    0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →
    a + b = c → c^4 ≤ K * (radical (a*b*c))^5

theorem radical_pos (n : ℕ) : 0 < radical n := by
  unfold radical
  exact Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors hp

/-- A finite list of exceptional triples gives a uniform natural constant, with
no need for any numerical bound on the exceptional triples. -/
theorem abcAtQuarter_of_classical (h : ClassicalABC) : abcAtQuarter := by
  classical
  let F := (h (1/4) (by norm_num)).toFinset
  let K : ℕ := 1 + ∑ t ∈ F, t.2.2 ^ 4
  refine ⟨K, by simp [K], ?_⟩
  intro a b c ha hb hc hpair habc
  by_cases hmem : (a,b,c) ∈ ABCExceptions (1/4)
  · have hF : (a,b,c) ∈ F := by simpa [F] using hmem
    have hsum : c^4 ≤ ∑ t ∈ F, t.2.2 ^ 4 :=
      Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => t.2.2 ^ 4)
        (fun _ _ => Nat.zero_le _) hF
    have hKR : K ≤ K * (radical (a*b*c))^5 := by
      conv_lhs => rw [← mul_one K]
      have hR : 0 < (radical (a*b*c))^5 := pow_pos (radical_pos _) _
      exact Nat.mul_le_mul_left K (by omega)
    have hSK : (∑ t ∈ F, t.2.2 ^ 4) ≤ K := by simp [K]
    exact hsum.trans (hSK.trans hKR)
  · have hle : (c : ℝ) ≤ (radical (a*b*c) : ℝ) ^ (1 + (1/4 : ℝ)) := by
      apply le_of_not_gt
      intro hlt
      exact hmem ⟨ha, hb, hc, hpair, habc, hlt⟩
    have hpow :
        ((radical (a*b*c) : ℝ) ^ (1 + (1/4 : ℝ))) ^ (4 : ℕ) =
          (radical (a*b*c) : ℝ) ^ (5 : ℕ) := by
      calc
        _ = (radical (a*b*c) : ℝ) ^ ((1 + (1/4 : ℝ)) * (4 : ℝ)) := by
          rw [Real.rpow_mul (by positivity)]
          exact (Real.rpow_natCast _ 4).symm
        _ = (radical (a*b*c) : ℝ) ^ ((5 : ℕ) : ℝ) := by norm_num
        _ = _ := Real.rpow_natCast _ 5
    have hnat : c^4 ≤ radical (a*b*c)^5 := by
      exact_mod_cast (pow_le_pow_left₀ (by positivity) hle 4).trans hpow.le
    have hk : 1 ≤ K := by simp [K]
    have hrK := Nat.mul_le_mul_right (radical (a*b*c)^5) hk
    rw [one_mul] at hrK
    exact hnat.trans hrK

end RudinABC
