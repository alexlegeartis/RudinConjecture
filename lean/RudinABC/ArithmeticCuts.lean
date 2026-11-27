import RudinABC.MinorBounds
import RudinABC.PrimeCases
import RudinABC.Rounding

/-! # Assign one cut to each odd split prime and control the rounding
by the four or five actual differences, as in preprint equation (7). -/

namespace RudinABC
open Zsqrtd

/-- The paper's odd split primes, tested by a Gaussian factor of norm p. -/
def OddSplit (p : ℕ) : Prop := p.Prime ∧ p≠2 ∧ ∃ π : GaussianInt, normN π=p

/-- A fixed Gaussian factor for every odd split prime. Use a dummy unit
away from the split prime support. -/
noncomputable def selectedProbe (p : ℕ) : GaussianInt := by
  classical
  exact if h : OddSplit p then Classical.choose h.2.2 else 1

theorem selectedProbe_norm {p : ℕ} (hp : OddSplit p) : normN (selectedProbe p)=p := by
  simp [selectedProbe,hp,Classical.choose_spec hp.2.2]

namespace Circle

variable {N : ℕ} {q a : ℤ} (c : Circle N q a)

/-- The norm valuation e at a rational prime. -/
def exponent (p : ℕ) : ℕ := c.S.natAbs.factorization p

/-- The exponent at the fixed Gaussian prime over p (only used when split). -/
noncomputable def alpha (p : ℕ) (i : Fin 5) : ℕ :=
  multiplicity (selectedProbe p) (c.gaussian i)

/-- The cuts in the paper have one fixed nearest-endpoint bit at each label. -/
noncomputable def primeCut (p : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter fun i => highBit (c.exponent p) (c.alpha p i) = true

theorem cutBit (p : ℕ) (i : Fin 5) :
    sideBit (c.primeCut p) i = highBit (c.exponent p) (c.alpha p i) := by
  simp [sideBit,primeCut]

/-- The finite set of odd split prime factors of S. -/
noncomputable def splitSupport : Finset ℕ := by
  classical
  exact c.S.natAbs.primeFactors.filter OddSplit

theorem normN_eq (i : Fin 5) : normN (c.gaussian i)=c.S.natAbs :=
  congrArg Int.natAbs (c.gauss_norm i)

theorem S_natPos : 0<c.S.natAbs := by
  exact Int.natAbs_pos.2 c.SPos.ne'

theorem alpha_complement {p : ℕ} (hs : OddSplit p) (i : Fin 5) :
    c.alpha p i + multiplicity (star (selectedProbe p)) (c.gaussian i) = c.exponent p := by
  have H := split_norm_value hs.1 hs.2.1 (selectedProbe_norm hs) (c.gauss_nonzero i)
  rw [c.normN_eq] at H
  exact H.symm

theorem alpha_le {p : ℕ} (hs : OddSplit p) (i : Fin 5) :
    c.alpha p i ≤ c.exponent p := by have H := c.alpha_complement hs i; omega

theorem rational_not_dvd_q {p : ℕ} (hp : p.Prime) (hp2 : p≠2)
    (hc : IsCoprime a q) (hS : p∣c.S.natAbs) : ¬p∣q.natAbs := by
  intro hq
  have hdiv := Int.dvd_gcd (Int.natCast_dvd.2 hq) (Int.natCast_dvd.2 hS)
  have h2 : p∣2 := hdiv.trans (Int.natCast_dvd_natCast.1 (c.gcd_dvd_two hc))
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1|h2
  · exact hp.ne_one h1
  · exact hp2 h2

/-- The first inequality in equation (7), without fractions. -/
theorem alpha_deviation_bound (hq : 0<q) (hc : IsCoprime a q)
    {p : ℕ} (hp : p ∈ c.splitSupport) (i : Fin 5) :
    2*min (c.alpha p i) (c.exponent p-c.alpha p i) ≤ (c.d i).factorization p := by
  classical
  have hm := (Finset.mem_filter.1 hp)
  have hs := hm.2
  let π := selectedProbe p
  have hnorm : normN π=p := selectedProbe_norm hs
  let m := min (c.alpha p i) (c.exponent p-c.alpha p i)
  have hπ : Prime π := gauss_prime_of_normN_prime (hnorm.symm ▸ hs.1)
  have hcop : IsCoprime π (star π) :=
    (EuclideanDomain.dvd_or_coprime π (star π) hπ.irreducible).resolve_left
      (split_not_dvd_star hs.1 hs.2.1 hnorm)
  have hd₁ : π^m ∣ c.gaussian i := pow_dvd_of_le_multiplicity (min_le_left _ _)
  have he : c.exponent p-c.alpha p i = multiplicity (star π) (c.gaussian i) := by
    have hh := c.alpha_complement hs i
    change _ + multiplicity (star π) (c.gaussian i) = _ at hh
    omega
  have hd₂ : (star π)^m ∣ c.gaussian i :=
    pow_dvd_of_le_multiplicity ((min_le_right _ _).trans he.le)
  have hzp : (p:GaussianInt)^m ∣ c.gaussian i := by
    rw [natCast_normN_eq hnorm,mul_pow]
    exact hcop.pow_left.pow_right.mul_dvd hd₁ hd₂
  obtain ⟨hx,hy⟩ := (Zsqrtd.intCast_dvd ((p:ℤ)^m) (c.gaussian i)).1 (by
    simpa only [Int.cast_pow,Int.cast_natCast] using hzp)
  have hxd : (p:ℤ)^(m*2) ∣ c.x i^2 := by rw [pow_mul]; exact pow_dvd_pow_of_dvd hx 2
  have hyd : (p:ℤ)^(m*2) ∣ c.y i^2 := by rw [pow_mul]; exact pow_dvd_pow_of_dvd hy 2
  have hqa : (p:ℤ)^(m*2) ∣ q*(c.d i:ℤ) := by
    rw [← c.diff_eq]
    exact dvd_sub hxd hyd
  have hqd : p^(m*2) ∣ q.natAbs*c.d i := by
    have h := Int.natCast_dvd.1
      (show ((p^(m*2):ℕ):ℤ) ∣ q*(c.d i:ℤ) by simpa only [Nat.cast_pow] using hqa)
    simpa [Int.natAbs_mul] using h
  have hq0 : q.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hq.ne'
  have hd0 : c.d i ≠ 0 := (c.dPos i).ne'
  have hf := (hs.1.pow_dvd_iff_le_factorization (mul_ne_zero hq0 hd0)).1 hqd
  have hqfact : q.natAbs.factorization p=0 :=
    Nat.factorization_eq_zero_of_not_dvd (c.rational_not_dvd_q hs.1 hs.2.1 hc (Nat.dvd_of_mem_primeFactors hm.1))
  rw [Nat.factorization_mul hq0 hd0,Finsupp.add_apply,hqfact,Nat.zero_add,Nat.mul_comm m 2] at hf
  exact hf

theorem kp_factorization_split {p : ℕ} (hs : OddSplit p) {i j : Fin 5}
    (M : c.MinorData i j) :
    M.kp.factorization p = min (c.alpha p i) (c.alpha p j) +
      min (c.exponent p-c.alpha p i) (c.exponent p-c.alpha p j) := by
  rw [M.kpIsNorm]
  change (normN (gaussGcd (c.gaussian i) (c.gaussian j))).factorization p = _
  have hcS := (c.normN_eq i).trans (c.normN_eq j).symm
  have hr := split_gcd_norm_value hs.1 hs.2.1 (selectedProbe_norm hs)
    (c.gauss_nonzero i) (c.gauss_nonzero j) hcS
  simpa only [c.normN_eq,alpha,exponent] using hr

/-- No rounding loss at any prime outside the odd split support. -/
theorem kp_factorization_unselected {p : ℕ} (hp : p∉c.splitSupport)
    {i j : Fin 5} (M : c.MinorData i j) :
    M.kp.factorization p = c.exponent p := by
  classical
  by_cases hS : p ∈ c.S.natAbs.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hS
    have hfalse : ¬OddSplit p := fun hs => hp (Finset.mem_filter.2 ⟨hS,hs⟩)
    have hcS := (c.normN_eq i).trans (c.normN_eq j).symm
    rw [M.kpIsNorm]
    change (normN (gaussGcd (c.gaussian i) (c.gaussian j))).factorization p = _
    by_cases hp2 : p=2
    · subst p
      rw [ramified_gcd_norm_value (c.gauss_nonzero i) (c.gauss_nonzero j) hcS,c.normN_eq]
      rfl
    · rcases gauss_prime_or_norm hpp with hinert | hsplit
      · rw [inert_gcd_norm_value hpp hinert (c.gauss_nonzero i) (c.gauss_nonzero j) hcS,c.normN_eq]
        rfl
      · exact False.elim (hfalse ⟨hpp,hp2,hsplit⟩)
  · have he : c.exponent p=0 := by
      change p ∉ c.S.natAbs.factorization.support at hS
      exact Finsupp.notMem_support_iff.1 hS
    have hdiv : M.kp ∣ c.S.natAbs := ⟨M.k,M.normProduct.symm⟩
    have hle := (Nat.factorization_le_iff_dvd M.kpPos.ne' c.S_natPos.ne').2 hdiv p
    change M.kp.factorization p ≤ c.exponent p at hle
    omega

theorem norm_factors {p : ℕ} {i j : Fin 5} (M : c.MinorData i j) :
    M.kp.factorization p + M.k.factorization p = c.exponent p := by
  have h := Nat.factorization_mul M.kpPos.ne' M.kPos.ne'
  rw [M.normProduct] at h
  exact (congrArg (fun f : ℕ →₀ ℕ => f p) h).symm

/-- The factor (2) clears the half-error bound for (K'). -/
theorem kp_round_error (hq : 0<q) (hc : IsCoprime a q) {p : ℕ}
    (hp : p∈c.splitSupport) {i j : Fin 5} (M : c.MinorData i j) :
    let V := M.kp.factorization p
    let I := if sideBit (c.primeCut p) i=sideBit (c.primeCut p) j then c.exponent p else 0
    let D := (c.d i).factorization p+(c.d j).factorization p
    2*V ≤ 2*I+D ∧ 2*I ≤ 2*V+D := by
  classical
  have hs := (Finset.mem_filter.1 hp).2
  dsimp only
  rw [c.cutBit,c.cutBit,c.kp_factorization_split hs M]
  have h := rounded_gcd_edge (c.exponent p) (c.alpha p i) (c.alpha p j)
    ((c.d i).factorization p) ((c.d j).factorization p)
    (c.alpha_le hs i) (c.alpha_le hs j) (c.alpha_deviation_bound hq hc hp i)
    (c.alpha_deviation_bound hq hc hp j)
  simpa only [idealSame,Nat.add_assoc] using h

end Circle
end RudinABC
