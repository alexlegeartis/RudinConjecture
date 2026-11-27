import RudinABC.QuarticExtract

/-! # Apply the weighted cut to the actual Gaussian valuations (preprint §5) -/

namespace RudinABC.Circle

variable {N : ℕ} {q a : ℤ} (c : Circle N q a)

noncomputable def separationSupport (e : EdgeIndex) : Finset ℕ :=
  c.splitSupport.filter fun p => separates (c.primeCut p) e.1 = true

noncomputable def separationProduct (e : EdgeIndex) : ℕ :=
  ∏ p ∈ c.separationSupport e, p^(c.exponent p)

theorem separationSupport_prime (e : EdgeIndex) :
    ∀ p∈c.separationSupport e, p.Prime := by
  classical
  intro p hp
  exact (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.1

theorem separationProduct_pos (e : EdgeIndex) : 0<c.separationProduct e :=
  Finset.prod_pos fun p hp => Nat.pow_pos (c.separationSupport_prime e p hp).pos

theorem separationProduct_factor (e : EdgeIndex) (p : ℕ) :
    (c.separationProduct e).factorization p =
      if p∈c.separationSupport e then c.exponent p else 0 :=
  prime_product_factorization _ _ (c.separationSupport_prime e) p

theorem separationProduct_log (e : EdgeIndex) :
    Real.log (c.separationProduct e:ℝ) =
      separationWeight c.splitSupport c.primeCut
        (fun p => (c.exponent p:ℝ)*Real.log (p:ℝ)) e.1 := by
  unfold separationProduct separationWeight
  rw [log_prime_product _ _ (c.separationSupport_prime e),separationSupport,Finset.sum_filter]

/-- Exponentiating the needed side of the valuation estimate gives
(K_{ij}^2\mid W_{ij}^2d_i d_j). -/
theorem K_sq_divides_sep (hq : 0<q) (hc : IsCoprime a q)
    (e : EdgeIndex) (M : c.MinorData e.1.1 e.1.2) :
    M.k^2 ∣ (c.separationProduct e)^2*c.d e.1.1*c.d e.1.2 := by
  classical
  have hW := (c.separationProduct_pos e).ne'
  have hdi := (c.dPos e.1.1).ne'
  have hdj := (c.dPos e.1.2).ne'
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ M.kPos.ne')
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hW) hdi) hdj)).1
  intro p
  rw [factorization_mul_apply (mul_ne_zero (pow_ne_zero _ hW) hdi) hdj,
    factorization_mul_apply (pow_ne_zero _ hW) hdi,factorization_pow_apply,
    factorization_pow_apply,c.separationProduct_factor]
  by_cases hp : p∈c.splitSupport
  · have hV := c.norm_factors (p := p) M
    have hE := c.kp_round_error hq hc hp M
    dsimp only at hE
    have hm : p∈c.separationSupport e ↔ separates (c.primeCut p) e.1 = true := by
      simp [separationSupport,hp]
    rw [if_congr hm rfl rfl]
    cases hi : sideBit (c.primeCut p) e.1.1 <;>
      cases hj : sideBit (c.primeCut p) e.1.2 <;>
      simp [separates,hi,hj] at hE ⊢ <;> omega
  · have hV := c.norm_factors (p := p) M
    have hZero := c.kp_factorization_unselected hp M
    have hh : p∉c.separationSupport e := fun hm => hp (Finset.mem_filter.1 hm).1
    rw [if_neg hh]
    omega

/-- The lower edge contribution used in the weighted-cut proof. -/
theorem separation_lower (hq : 0<q) (hc : IsCoprime a q) (e : EdgeIndex)
    (M : c.MinorData e.1.1 e.1.2) (hN : 0<N) :
    Real.log (c.S.natAbs:ℝ)/2-3*Real.log (N:ℝ)/2 ≤
      separationWeight c.splitSupport c.primeCut
        (fun p => (c.exponent p:ℝ)*Real.log (p:ℝ)) e.1 := by
  have hS : 0<(c.S.natAbs:ℝ) := by exact_mod_cast c.S_natPos
  have hK : 0<(M.k:ℝ) := by exact_mod_cast M.kPos
  have hW : 0<(c.separationProduct e:ℝ) := by exact_mod_cast c.separationProduct_pos e
  have hNR : 0<(N:ℝ) := by exact_mod_cast hN
  have hdi : 0<(c.d e.1.1:ℝ) := by exact_mod_cast c.dPos e.1.1
  have hdj : 0<(c.d e.1.2:ℝ) := by exact_mod_cast c.dPos e.1.2
  have h1 := Real.log_le_log hS
    (show (c.S.natAbs:ℝ) ≤ (N:ℝ)*(M.k:ℝ)^2 by exact_mod_cast M.kBound)
  rw [Real.log_mul hNR.ne' (pow_ne_zero _ hK.ne'),Real.log_pow] at h1
  have htot : 0<(c.separationProduct e)^2*c.d e.1.1*c.d e.1.2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (c.separationProduct_pos e)) (c.dPos _)) (c.dPos _)
  have h2N := Nat.le_of_dvd htot (c.K_sq_divides_sep hq hc e M)
  have h2 := Real.log_le_log (pow_pos hK 2)
    (show (M.k:ℝ)^2 ≤ (c.separationProduct e:ℝ)^2*(c.d e.1.1:ℝ)*(c.d e.1.2:ℝ)
      by exact_mod_cast h2N)
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hW.ne') hdi.ne') hdj.ne',
    Real.log_mul (pow_ne_zero _ hW.ne') hdi.ne',Real.log_pow,Real.log_pow] at h2
  have h3 := Real.log_le_log hdi (show (c.d e.1.1:ℝ) ≤ (N:ℝ) by exact_mod_cast (c.dLt _).le)
  have h4 := Real.log_le_log hdj (show (c.d e.1.2:ℝ) ≤ (N:ℝ) by exact_mod_cast (c.dLt _).le)
  rw [← c.separationProduct_log]
  norm_num at h1 h2 ⊢
  linarith

theorem total_split_weight_le :
    ∑ p ∈ c.splitSupport, (c.exponent p:ℝ)*Real.log (p:ℝ) ≤ Real.log (c.S.natAbs:ℝ) := by
  classical
  have hprime (p : ℕ) (hp : p∈c.S.natAbs.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hprod : (∏ p ∈ c.S.natAbs.primeFactors, p^(c.exponent p)) = c.S.natAbs :=
    (Nat.prod_primeFactors_pow_factorization c.S_natPos.ne').symm
  have hsum := log_prime_product c.S.natAbs.primeFactors c.exponent hprime
  rw [hprod] at hsum
  rw [hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp _
  exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le))

include c in
/-- The common difference is polynomially bounded as soon as the five
same-sum representations exist. This completes the exact §§2–5 chain. -/
theorem q_polynomial (hq : 0<q) (hc : IsCoprime a q)
    (K : ℕ) (hK : 0<K)
    (hABC : ∀ a b c : ℕ, 0<a → 0<b → 0<c → ({a,b,c} : Set ℕ).Pairwise Nat.Coprime →
      a+b=c → c^4 ≤ K*(radical (a*b*c))^5) :
    q.natAbs ≤ K^30*N^16215 := by
  classical
  have hN : 0<N := (c.dPos 0).trans (c.dLt 0)
  have hKR : 0<(K:ℝ) := by exact_mod_cast hK
  have hNR : 0<(N:ℝ) := by exact_mod_cast hN
  let M := c.allMinors hq hc
  let w := fun p : ℕ => (c.exponent p:ℝ)*Real.log (p:ℝ)
  have hw : ∀ p∈c.splitSupport, 0≤w p := by
    intro p hp
    exact mul_nonneg (by positivity) (Real.log_nonneg
      (by exact_mod_cast ((Finset.mem_filter.1 hp).2.1).one_lt.le))
  have hW : (∑ p ∈ c.splitSupport, w p) ≤ Real.log (c.S.natAbs:ℝ) := c.total_split_weight_le
  have hpair (ij : Fin 5×Fin 5) (hij : ij∈edges) :
      Real.log (c.S.natAbs:ℝ)/2-3*Real.log (N:ℝ)/2 ≤
        separationWeight c.splitSupport c.primeCut w ij :=
    c.separation_lower hq hc ⟨ij,hij⟩ (M ⟨ij,hij⟩) hN
  have hquartet (o : Fin 5) (r : Fin 3) :
      pairingWeight c.splitSupport c.primeCut w o r ≤ Real.log (K:ℝ)+540*Real.log (N:ℝ) := by
    rw [← c.pairingProduct_log]
    have h := Real.log_le_log (show 0<(c.pairingProduct o r:ℝ) by exact_mod_cast c.pairingProduct_pos o r)
      (show (c.pairingProduct o r:ℝ)≤(K:ℝ)*(N:ℝ)^540 by
        exact_mod_cast c.pairing_polynomial M hq hc K hABC o r)
    rw [Real.log_mul hKR.ne' (pow_ne_zero _ hNR.ne'),Real.log_pow] at h
    norm_num at h
    exact h
  have hlog := weighted_cut_bound c.splitSupport c.primeCut w
    (Real.log (c.S.natAbs:ℝ)) (Real.log (N:ℝ))
    (Real.log (K:ℝ)+540*Real.log (N:ℝ)) hw hW hpair hquartet
  have hlog' : Real.log (c.S.natAbs:ℝ) ≤ Real.log ((K:ℝ)^30*(N:ℝ)^16215) := by
    rw [Real.log_mul (pow_ne_zero _ hKR.ne') (pow_ne_zero _ hNR.ne'),Real.log_pow,Real.log_pow]
    norm_num at hlog ⊢
    linarith
  have hExp := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log (by exact_mod_cast c.S_natPos),Real.exp_log (by positivity)] at hExp
  have hSq : c.S.natAbs≤K^30*N^16215 := by exact_mod_cast hExp
  apply le_trans _ hSq
  have hqD : q ≤ q*(c.d 0:ℤ) := by
    have hD : 1≤(c.d 0:ℤ) := by exact_mod_cast (c.dPos 0)
    have he := mul_le_mul_of_nonneg_left hD hq.le
    simpa only [mul_one] using he
  have hDS : q*(c.d 0:ℤ) ≤ c.S := by
    rw [← c.diff_eq]
    linarith [c.norm_eq 0,sq_nonneg (c.y 0)]
  have hf : (q.natAbs:ℤ) ≤ (c.S.natAbs:ℤ) := by
    rw [Int.natAbs_of_nonneg hq.le,Int.natAbs_of_nonneg c.SPos.le]
    exact hqD.trans hDS
  exact_mod_cast hf

end RudinABC.Circle
