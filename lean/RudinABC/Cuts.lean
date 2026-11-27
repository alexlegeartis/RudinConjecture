import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The weighted five-label cut (preprint §5, eq. (10)) -/

namespace RudinABC

/-- The ten unordered pairs of the five labels, each written in increasing order. -/
def edges : Finset (Fin 5 × Fin 5) :=
  (Finset.univ : Finset (Fin 5)).product Finset.univ |>.filter fun ij => ij.1 < ij.2

/-- A cut is represented by the labels on one side. -/
def sideBit (s : Finset (Fin 5)) (i : Fin 5) : Bool := decide (i ∈ s)
def separates (s : Finset (Fin 5)) (ij : Fin 5 × Fin 5) : Bool :=
  sideBit s ij.1 != sideBit s ij.2

def balanced (s : Finset (Fin 5)) : Bool := (s.card == 2) || (s.card == 3)
def separationCount (s : Finset (Fin 5)) : ℕ := (edges.filter (fun ij => separates s ij = true)).card

/-- The three pairing indices used in the preprint's Plücker equation:
`12|34`, `14|23`, and `13|24`, now with vertices numbered from `0`. -/
def pairing (r : Fin 3) : (Fin 4 × Fin 4) × (Fin 4 × Fin 4) :=
  if r = 0 then ((0,1),(2,3)) else if r = 1 then ((0,3),(1,2)) else ((0,2),(1,3))

/-- The retained four labels after omitting one label from the five. -/
def retained (o : Fin 5) (i : Fin 4) : Fin 5 := o.succAbove i

/-- Whether the cut restricts to a `2+2` cut on this quartet whose
equal-label pairs are precisely the ones paired by `r`. -/
def matchesPairing (s : Finset (Fin 5)) (o : Fin 5) (r : Fin 3) : Bool :=
  let e := pairing r
  let b := fun i => sideBit s (retained o i)
  (b e.1.1 == b e.1.2) && (b e.2.1 == b e.2.2) && (b e.1.1 != b e.2.1)

theorem edges_card : edges.card = 10 := by decide

/-- This is the exact arithmetic of the ten edges: a `2+3` cut hits six;
a singleton cut hits four, and a trivial cut hits none. -/
theorem separationCount_formula : ∀ s : Finset (Fin 5),
    separationCount s = s.card * (5-s.card) := by decide

theorem separationCount_bound : ∀ s : Finset (Fin 5),
    separationCount s ≤ (if balanced s then 6 else 4) := by decide

/-- Every `2+3` cut yields a `2+2` cut by dropping a label from its
three-element side. The matching pairing in that quartet is included. -/
theorem balanced_covered : ∀ s : Finset (Fin 5),
    balanced s = true → ∃ o : Fin 5, ∃ r : Fin 3, matchesPairing s o r = true := by decide

/-- For any fixed quartet and cut, equal-label matching is unique when it
exists. This ensures a prime is assigned to no more than one pairing. -/
theorem matchesPairing_unique :
    ∀ (s : Finset (Fin 5)) (o : Fin 5) (r t : Fin 3),
      matchesPairing s o r = true → matchesPairing s o t = true → r = t := by decide

section Weights

variable {ι : Type*}

/-- The separation weight of one pair of labels. -/
def separationWeight (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ)
    (ij : Fin 5 × Fin 5) : ℝ :=
  ∑ p ∈ P, if separates (s p) ij then w p else 0

/-- The total weight of balanced `2+3` cuts. -/
def balancedWeight (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ) : ℝ :=
  ∑ p ∈ P, if balanced (s p) then w p else 0

/-- For a quartet/pairing, this will be `log P_ν` once
`w(p) = e(p) log p` and `P_ν` is defined by the preprint. -/
def pairingWeight (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ)
    (o : Fin 5) (r : Fin 3) : ℝ :=
  ∑ p ∈ P, if matchesPairing (s p) o r then w p else 0

/-- Assign weight six to a balanced prime and at most four to any other.
This is the upper half of the preprint's equation (10). -/
theorem total_separation_le (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    ∑ ij ∈ edges, separationWeight P s w ij ≤
       4*(∑ p ∈ P, w p) + 2*balancedWeight P s w := by
  unfold separationWeight balancedWeight
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change (separationCount (s p) : ℝ)*w p ≤
    4*w p + 2*(if balanced (s p) then w p else 0)
  have h := separationCount_bound (s p)
  by_cases hb : balanced (s p) = true
  · simp only [hb, if_true] at h ⊢
    have hc : (separationCount (s p) : ℝ) ≤ 6 := by exact_mod_cast h
    linarith [mul_le_mul_of_nonneg_right hc (hw p hp)]
  · rw [if_neg hb] at h ⊢
    have hc : (separationCount (s p) : ℝ) ≤ 4 := by exact_mod_cast h
    linarith [mul_le_mul_of_nonneg_right hc (hw p hp)]

/-- The balanced weight is bounded by the sum of the fifteen pairing weights.
It is enough that each balanced cut is counted at least once. -/
theorem balanced_le_pairing_sum (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    balancedWeight P s w ≤ ∑ or : Fin 5 × Fin 3, pairingWeight P s w or.1 or.2 := by
  unfold balancedWeight pairingWeight
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hb : balanced (s p) = true
  · rw [if_pos hb]
    obtain ⟨o,r,hpair⟩ := balanced_covered (s p) hb
    have hc := Finset.single_le_sum
      (f := fun or : Fin 5 × Fin 3 => if matchesPairing (s p) or.1 or.2 then w p else 0)
      (fun x _ => ite_nonneg (hw p hp) le_rfl) (Finset.mem_univ (o,r))
    simpa only [hpair, if_true] using hc
  · rw [if_neg hb]
    exact Finset.sum_nonneg fun x _ => ite_nonneg (hw p hp) le_rfl

/-- The actual weighted-cut inference, with the logarithmic variables left
abstract to reuse the exact arithmetic/valuation lemmas of §§3–4. -/
theorem weighted_cut_bound (P : Finset ι) (s : ι → Finset (Fin 5)) (w : ι → ℝ)
    (logS logN bound : ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    (hW : (∑ p ∈ P, w p) ≤ logS)
    (hpair : ∀ ij ∈ edges, logS/2 - 3*logN/2 ≤ separationWeight P s w ij)
    (hquartet : ∀ o r, pairingWeight P s w o r ≤ bound) :
    logS ≤ 15*logN + 30*bound := by
  have hlow0 : (∑ ij ∈ edges, (logS/2-3*logN/2)) ≤
      ∑ ij ∈ edges, separationWeight P s w ij := Finset.sum_le_sum hpair
  rw [Finset.sum_const, nsmul_eq_mul, edges_card] at hlow0
  have hf : balancedWeight P s w ≤ ∑ or : Fin 5 × Fin 3, pairingWeight P s w or.1 or.2 :=
    balanced_le_pairing_sum P s w hw
  have hu0 : (∑ or : Fin 5 × Fin 3, pairingWeight P s w or.1 or.2) ≤
      (∑ _ : Fin 5 × Fin 3, bound) :=
    Finset.sum_le_sum fun or _ => hquartet or.1 or.2
  have hn : (Finset.univ : Finset (Fin 5 × Fin 3)).card = 15 := by decide
  rw [Finset.sum_const, nsmul_eq_mul, hn] at hu0
  norm_num at hlow0 hu0
  linarith [total_separation_le P s w hw]

end Weights
end RudinABC
