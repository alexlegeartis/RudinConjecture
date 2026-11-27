import Mathlib.Data.Set.Card
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Order.Lattice.Nat

/-! # Statement-level adapters (preprint §1 and DeepMind Qmax) -/

namespace RudinABC

/-- All indices of square terms in the integer progression, including zero if it occurs. -/
noncomputable def squareIndices (N : ℕ) (q a : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n => IsSquare (q * (n : ℤ) + a)

/-- The count in the preprint for all signed starting terms and nonzero differences. -/
noncomputable def QZ (N : ℕ) (q a : ℤ) : ℕ := (squareIndices N q a).card

/-- The actual uniform conclusion of the integer progression argument. -/
def UniformIntegerRudin : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (q a : ℤ), q ≠ 0 →
    (QZ N q a : ℝ) ≤ C * Real.sqrt (N : ℝ)

theorem mem_squareIndices (N n : ℕ) (q a : ℤ) :
    n ∈ squareIndices N q a ↔ n < N ∧ IsSquare (q*(n : ℤ) + a) := by
  classical
  simp [squareIndices]

theorem QZ_le_length (N : ℕ) (q a : ℤ) : QZ N q a ≤ N := by
  classical
  unfold QZ squareIndices
  simpa using Finset.card_filter_le (s := Finset.range N) (p := fun n => IsSquare (q*(n:ℤ) + a))

theorem isSquare_intNatCast_iff (m : ℕ) : IsSquare (m : ℤ) ↔ IsSquare m := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.natAbs, ?_⟩
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using (congrArg Int.natAbs hx)
  · rintro ⟨x, hx⟩
    exact ⟨(x : ℤ), by exact_mod_cast hx⟩

namespace Upstream

/-- Exact definition from FormalConjectures/Wikipedia/RudinsConjecture.lean. -/
noncomputable abbrev Q (N q a : ℕ) : ℕ := {n : ℕ | n < N ∧ IsSquare (q * n + a)}.ncard

/-- Exact definition from FormalConjectures/Wikipedia/RudinsConjecture.lean. -/
def IsNontrivial (q a : ℕ) : Prop :=
  1 ≤ q ∧ 1 ≤ a ∧ Nat.Coprime q a ∧ (q, a) ≠ (1, 1)

/-- Exact definition from FormalConjectures/Wikipedia/RudinsConjecture.lean. -/
noncomputable def Qmax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}

theorem count_eq_integer (N q a : ℕ) : Q N q a = QZ N (q : ℤ) (a : ℤ) := by
  have hset :
      {n : ℕ | n < N ∧ IsSquare (q * n + a)} = ↑(squareIndices N (q : ℤ) (a : ℤ)) := by
    ext n
    change (n < N ∧ IsSquare (q*n+a)) ↔ n ∈ squareIndices N (q : ℤ) (a : ℤ)
    rw [mem_squareIndices, ← Int.natCast_mul, ← Int.natCast_add, isSquare_intNatCast_iff]
  change ({n : ℕ | n < N ∧ IsSquare (q*n+a)}).ncard =
    (squareIndices N (q : ℤ) (a : ℤ)).card
  rw [hset, Set.ncard_coe_finset]

theorem Qmax_attained (N : ℕ) : ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = Qmax N := by
  let S : Set ℕ := {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}
  have hne : S.Nonempty := ⟨Q N 24 1, 24, 1, by unfold IsNontrivial; decide, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨q,a,_,rfl⟩ := hm
    simpa only [count_eq_integer] using QZ_le_length N (q : ℤ) (a : ℤ)
  exact Nat.sSup_mem hne hbd

open Filter Asymptotics in
/-- Bridge to precisely the upstream asymptotic statement. The upstream
conjectural declarations, including the stronger ones, are never used. -/
theorem bigO_of_uniform_integer (h : UniformIntegerRudin) :
    (fun N : ℕ => (Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  obtain ⟨C, _, HC⟩ := h
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall ?_⟩
  intro N
  obtain ⟨q,a,hqa,hQ⟩ := Qmax_attained N
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqa.1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _), ← hQ, count_eq_integer]
  exact HC N q a hq

end Upstream
end RudinABC
