import RudinABC.RootInterval

/-! # The divisor estimate and the two q-ranges (preprint §6) -/

namespace RudinABC

def omegaFactor (q : ℕ) : ℕ := 2^q.primeFactors.card

/-- For a fixed power L, the finitely many primes below 2^L are absorbed
by a constant. This is the paper's elementary divisor estimate, with
fractional exponents cleared. -/
theorem omegaFactor_pow_le (q L : ℕ) (hq : 0<q) :
    omegaFactor q^L ≤ (2^L)^(2^L)*q := by
  classical
  let s := q.primeFactors
  let H : ℕ := 2^L
  let small := s.filter (fun p => p<H)
  let large := s.filter (fun p => ¬p<H)
  have hsum : (∏ p ∈ small, H)*(∏ p ∈ large, H) = ∏ p ∈ s, H :=
    Finset.prod_filter_mul_prod_filter_not s (fun p => p<H) (fun _ => H)
  have hle : small.card≤H := by
    calc
      _ ≤ (Finset.range H).card := Finset.card_le_card fun p hp =>
        Finset.mem_range.2 (Finset.mem_filter.1 hp).2
      _ = _ := Finset.card_range _
  have hsmall : (∏ p ∈ small, H)≤H^H := by
    rw [Finset.prod_const]
    have hH : 0<H := by dsimp [H]; positivity
    exact pow_le_pow_right₀ hH hle
  have hlarge : (∏ p ∈ large,H)≤q := by
    calc
      _ ≤ ∏ p ∈ large,p := Finset.prod_le_prod' fun p hp => le_of_not_gt (Finset.mem_filter.1 hp).2
      _ ≤ q := Nat.le_of_dvd hq
        ((Finset.prod_dvd_prod_of_subset large s (fun p => p) (Finset.filter_subset _ _)).trans
          q.prod_primeFactors_dvd)
  calc
    omegaFactor q^L = (2^L)^s.card := by unfold omegaFactor; rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ = ∏ p ∈ s,H := by rw [Finset.prod_const]
    _ = _ := hsum.symm
    _ ≤ _ := Nat.mul_le_mul hsmall hlarge

theorem omegaFactor_le_sqrt (q : ℕ) (hq : 0<q) :
    (omegaFactor q:ℝ) ≤ 16*Real.sqrt (q:ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by positivity)
  have h := omegaFactor_pow_le q 2 hq
  norm_num at h
  have hr : (omegaFactor q:ℝ)^2 ≤ 256*(q:ℝ) := by exact_mod_cast h
  rwa [mul_pow,Real.sq_sqrt (by positivity : 0≤(q:ℝ)),show (16:ℝ)^2=256 by norm_num]

/-- Fixed constant for the large-q range when (q≤ A N^B). -/
def growthConstant (A B : ℕ) : ℕ :=
  (2^(2*(B+1)))^(2^(2*(B+1)))*A

theorem omegaFactor_le_sqrt_of_poly (A B q N : ℕ)
    (hA : 0<A) (hN : 0<N) (hq : 0<q) (hqN : q≤A*N^B) :
    (omegaFactor q:ℝ) ≤ (growthConstant A B:ℝ)*Real.sqrt (N:ℝ) := by
  let L := 2*(B+1)
  let C := growthConstant A B
  have hL : L≠0 := by dsimp [L]; omega
  have hC0 : 0<C := by dsimp [C,growthConstant]; positivity
  have hC : 1≤C := hC0
  have hN1 : 1≤N := by omega
  have hNpow : N^B≤N^(B+1) := pow_le_pow_right₀ hN1 (Nat.le_succ _)
  have hCpow : C≤C^L := le_self_pow₀ hC hL
  have hNat : omegaFactor q^L ≤ C^L*N^(B+1) := by
    calc
      _ ≤ (2^L)^(2^L)*q := omegaFactor_pow_le q L hq
      _ ≤ (2^L)^(2^L)*(A*N^B) := Nat.mul_le_mul_left _ hqN
      _ = C*N^B := by unfold C growthConstant L; ring
      _ ≤ _ := Nat.mul_le_mul hCpow hNpow
  apply le_of_pow_le_pow_left₀ hL (by positivity)
  rw [mul_pow,show (Real.sqrt (N:ℝ))^L=(N:ℝ)^(B+1) by
    unfold L; rw [pow_mul,Real.sq_sqrt (by positivity : 0≤(N:ℝ))]]
  exact_mod_cast hNat

/-- Positive-square count once the polynomial bound for q has been reached,
in both ranges from the final paragraph of the preprint. -/
theorem positive_count_of_polynomial (A B N : ℕ) (q a : ℤ)
    (hA : 0<A) (hN : 0<N) (hq : 0<q) (hc : IsCoprime a q)
    (hpoly : q.natAbs≤A*N^B) :
    ((positiveSquareIndices N q a).card:ℝ) ≤
      (64+4*(growthConstant A B:ℝ))*Real.sqrt (N:ℝ) := by
  let Q := q.natAbs
  have hQ : 0<Q := Int.natAbs_pos.2 hq.ne'
  have hQeq : (Q:ℤ)=q := Int.natAbs_of_nonneg hq.le
  have hQR : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hNR : 0<(N:ℝ) := by exact_mod_cast hN
  have hcrt := residueCount_le_two_pow Q hQ a (hQeq.symm ▸ hc)
  have hcrtR : (residueCount Q a:ℝ)≤2*(omegaFactor Q:ℝ) := by
    unfold omegaFactor
    exact_mod_cast hcrt
  let s := Real.sqrt ((N:ℝ)/(Q:ℝ))
  have hs : 0≤s := Real.sqrt_nonneg _
  have hm : ((positiveSquareIndices N q a).card:ℝ)≤2*(omegaFactor Q:ℝ)*(1+s) :=
    (positive_count_residue_interval N q a hq).trans
      (mul_le_mul_of_nonneg_right hcrtR (by positivity))
  apply hm.trans
  by_cases h : Q≤N
  · have hqS := omegaFactor_le_sqrt Q hQ
    have hsqcomp : Real.sqrt (Q:ℝ)≤Real.sqrt (N:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h)
    have hqSd : 0<Real.sqrt (Q:ℝ) := Real.sqrt_pos.2 hQR
    have hcan : Real.sqrt (Q:ℝ)*(1+s)=Real.sqrt (Q:ℝ)+Real.sqrt (N:ℝ) := by
      unfold s
      rw [Real.sqrt_div hNR.le]
      field_simp
    calc
      _ ≤ 2*(16*Real.sqrt (Q:ℝ))*(1+s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqS (by norm_num)) (by positivity)
      _ = 32*(Real.sqrt (Q:ℝ)+Real.sqrt (N:ℝ)) := by
        calc
          _ = 32*(Real.sqrt (Q:ℝ)*(1+s)) := by ring
          _ = _ := by rw [hcan]
      _ ≤ _ := by nlinarith [mul_nonneg (show 0≤(growthConstant A B:ℝ) by positivity) (Real.sqrt_nonneg (N:ℝ))]
  · have hqS := omegaFactor_le_sqrt_of_poly A B Q N hA hN hQ hpoly
    have hs1 : s≤1 := by
      unfold s
      have hr : (N:ℝ)/(Q:ℝ) ≤ 1 := (div_le_one₀ hQR).2 (by exact_mod_cast (lt_of_not_ge h).le)
      simpa using Real.sqrt_le_sqrt hr
    calc
      _ ≤ 2*((growthConstant A B:ℝ)*Real.sqrt (N:ℝ))*2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hqS (by norm_num)) (by linarith)
          (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg (N:ℝ)]

end RudinABC
