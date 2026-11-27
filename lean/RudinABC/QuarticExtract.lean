import RudinABC.ArithmeticCuts
import RudinABC.ValuationAlgebra
import RudinABC.QuarticBound

/-! # From the exact valuations to one quartic for each quartet -/

namespace RudinABC

abbrev EdgeIndex := {ij : Fin 5 × Fin 5 // ij ∈ edges}

def edgeIndex (i j : Fin 5) (h : i<j) : EdgeIndex :=
  ⟨(i,j), by simp [edges,h]⟩

theorem edgeIndex_lt (e : EdgeIndex) : e.1.1<e.1.2 :=
  (Finset.mem_filter.1 e.2).2

theorem pairing_lt1 : ∀ r : Fin 3, (pairing r).1.1 < (pairing r).1.2 := by decide
theorem pairing_lt2 : ∀ r : Fin 3, (pairing r).2.1 < (pairing r).2.2 := by decide

def quartetEdge1 (o : Fin 5) (r : Fin 3) : EdgeIndex :=
  edgeIndex (retained o (pairing r).1.1) (retained o (pairing r).1.2)
    (Fin.strictMono_succAbove o (pairing_lt1 r))

def quartetEdge2 (o : Fin 5) (r : Fin 3) : EdgeIndex :=
  edgeIndex (retained o (pairing r).2.1) (retained o (pairing r).2.2)
    (Fin.strictMono_succAbove o (pairing_lt2 r))

namespace Circle
variable {N : ℕ} {q a : ℤ} (c : Circle N q a)

abbrev Minors := ∀ e : EdgeIndex, c.MinorData e.1.1 e.1.2

noncomputable def allMinors (hq : 0<q) (hc : IsCoprime a q) : c.Minors :=
  fun e => Classical.choice (c.exists_minor_data hq hc (edgeIndex_lt e))

def pairA (M : c.Minors) (o : Fin 5) (r : Fin 3) : ℕ :=
  (M (quartetEdge1 o r)).jminus*(M (quartetEdge2 o r)).jminus

def pairX (M : c.Minors) (o : Fin 5) (r : Fin 3) : ℕ :=
  (M (quartetEdge1 o r)).kp*(M (quartetEdge2 o r)).kp

theorem pairA_pos (M : c.Minors) (o : Fin 5) (r : Fin 3) : 0<c.pairA M o r :=
  Nat.mul_pos (M _).minusPos (M _).minusPos

theorem pairX_pos (M : c.Minors) (o : Fin 5) (r : Fin 3) : 0<c.pairX M o r :=
  Nat.mul_pos (M _).kpPos (M _).kpPos

theorem pairA_bound (M : c.Minors) (o : Fin 5) (r : Fin 3) : c.pairA M o r ≤ N^4 := by
  calc
    _ ≤ N^2*N^2 := Nat.mul_le_mul (M _).minusBound (M _).minusBound
    _ = _ := by ring

/-- The original Plücker equation with each (D_{ij}) an actual
integer minor. No Gaussian valuation approximation is used here. -/
theorem quartet_plucker (M : c.Minors) (hq : q≠0) (o : Fin 5) :
    c.pairA M o 0*(c.pairX M o 0)^2+c.pairA M o 1*(c.pairX M o 1)^2 =
      c.pairA M o 2*(c.pairX M o 2)^2 := by
  let b (i : Fin 4) := (c.A (retained o i),c.B (retained o i))
  have h₁ (r : Fin 3) :
      minor (b (pairing r).1.1) (b (pairing r).1.2) =
        q*((M (quartetEdge1 o r)).jminus:ℤ)*((M (quartetEdge1 o r)).kp:ℤ)^2 := by
    have h := (M (quartetEdge1 o r)).DEq
    change c.D (retained o (pairing r).1.1) (retained o (pairing r).1.2) = _ at h
    rw [show minor (b (pairing r).1.1) (b (pairing r).1.2) =
       c.D (retained o (pairing r).1.1) (retained o (pairing r).1.2) by rfl,h]
    ring
  have h₂ (r : Fin 3) :
      minor (b (pairing r).2.1) (b (pairing r).2.2) =
        q*((M (quartetEdge2 o r)).jminus:ℤ)*((M (quartetEdge2 o r)).kp:ℤ)^2 := by
    have h := (M (quartetEdge2 o r)).DEq
    change c.D (retained o (pairing r).2.1) (retained o (pairing r).2.2) = _ at h
    rw [show minor (b (pairing r).2.1) (b (pairing r).2.2) =
       c.D (retained o (pairing r).2.1) (retained o (pairing r).2.2) by rfl,h]
    ring
  have H := plucker_cancel_common_factor (b 0) (b 1) (b 2) (b 3) q _ _ _ _ _ _ _ _ _ _ _ _ hq
    (h₁ 0) (h₂ 0) (h₁ 1) (h₂ 1) (h₁ 2) (h₂ 2)
  exact_mod_cast H

def budget (o : Fin 5) : ℕ :=
  c.d (retained o 0)*c.d (retained o 1)*c.d (retained o 2)*c.d (retained o 3)

theorem budget_pos (o : Fin 5) : 0<c.budget o :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (c.dPos _) (c.dPos _)) (c.dPos _)) (c.dPos _)

theorem budget_bound (o : Fin 5) : c.budget o ≤ N^4 := by
  calc
    _ ≤ N*N*N*N := Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul (c.dLt _).le (c.dLt _).le) (c.dLt _).le) (c.dLt _).le
    _ = _ := by ring

theorem budgetVal (o : Fin 5) (p : ℕ) :
    (c.budget o).factorization p = (c.d (retained o 0)).factorization p+
      (c.d (retained o 1)).factorization p+(c.d (retained o 2)).factorization p+
      (c.d (retained o 3)).factorization p := by
  have h0 := (c.dPos (retained o 0)).ne'
  have h1 := (c.dPos (retained o 1)).ne'
  have h2 := (c.dPos (retained o 2)).ne'
  have h3 := (c.dPos (retained o 3)).ne'
  unfold budget
  rw [factorization_mul_apply (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    factorization_mul_apply (mul_ne_zero h0 h1) h2,factorization_mul_apply h0 h1]

theorem budgetValMatching (o : Fin 5) (p : ℕ) (r : Fin 3) :
    (c.budget o).factorization p =
      (c.d (quartetEdge1 o r).1.1).factorization p+(c.d (quartetEdge1 o r).1.2).factorization p+
      ((c.d (quartetEdge2 o r).1.1).factorization p+(c.d (quartetEdge2 o r).1.2).factorization p) := by
  rw [c.budgetVal]
  fin_cases r <;> simp [quartetEdge1,quartetEdge2,edgeIndex,pairing] <;> omega

noncomputable def pairingSupport (o : Fin 5) (r : Fin 3) : Finset ℕ :=
  c.splitSupport.filter fun p => matchesPairing (c.primeCut p) o r = true

noncomputable def pairingProduct (o : Fin 5) (r : Fin 3) : ℕ :=
  ∏ p ∈ c.pairingSupport o r, p^(c.exponent p)

theorem pairingSupport_prime (o : Fin 5) (r : Fin 3) :
    ∀ p∈c.pairingSupport o r, p.Prime := by
  classical
  intro p hp
  exact (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.1

theorem pairingProduct_pos (o : Fin 5) (r : Fin 3) : 0<c.pairingProduct o r :=
  Finset.prod_pos (fun p hp => Nat.pow_pos (c.pairingSupport_prime o r p hp).pos)

theorem pairingProduct_factor (o : Fin 5) (r : Fin 3) (p : ℕ) :
    (c.pairingProduct o r).factorization p = if p∈c.pairingSupport o r then c.exponent p else 0 :=
  prime_product_factorization _ _ (c.pairingSupport_prime o r) p

theorem pairingProducts_coprime (o : Fin 5) {r t : Fin 3} (h : r≠t) :
    Nat.Coprime (c.pairingProduct o r) (c.pairingProduct o t) := by
  classical
  apply Nat.coprime_of_dvd
  intro p hp hr ht
  have hr' := (hp.dvd_iff_one_le_factorization (c.pairingProduct_pos o r).ne').1 hr
  have ht' := (hp.dvd_iff_one_le_factorization (c.pairingProduct_pos o t).ne').1 ht
  rw [c.pairingProduct_factor] at hr' ht'
  have hmr : p∈c.pairingSupport o r := by by_contra H; simp [H] at hr'
  have hmt : p∈c.pairingSupport o t := by by_contra H; simp [H] at ht'
  exact h (matchesPairing_unique (c.primeCut p) o r t
    (Finset.mem_filter.1 hmr).2 (Finset.mem_filter.1 hmt).2)

theorem pairingProduct_log (o : Fin 5) (r : Fin 3) :
    Real.log (c.pairingProduct o r:ℝ) =
      pairingWeight c.splitSupport c.primeCut
        (fun p => (c.exponent p:ℝ)*Real.log (p:ℝ)) o r := by
  unfold pairingProduct pairingWeight
  rw [log_prime_product _ _ (c.pairingSupport_prime o r),pairingSupport,Finset.sum_filter]

/-- Budget accumulation across the two disjoint edges of one quartet matching. -/
theorem pairing_rounded (M : c.Minors) (hq : 0<q) (hc : IsCoprime a q)
    (o : Fin 5) {p : ℕ} (hp : p∈c.splitSupport) (r : Fin 3) :
    let X := (c.pairX M o r).factorization p
    let I := c.exponent p*matchingEqualCount (c.primeCut p) o r
    let D := (c.budget o).factorization p
    2*X ≤ 2*I+D ∧ 2*I ≤ 2*X+D := by
  dsimp only
  have h₁ := c.kp_round_error hq hc hp (M (quartetEdge1 o r))
  have h₂ := c.kp_round_error hq hc hp (M (quartetEdge2 o r))
  dsimp only at h₁ h₂
  rw [pairX,factorization_mul_apply (M _).kpPos.ne' (M _).kpPos.ne',c.budgetValMatching o p r]
  let w (E : EdgeIndex) :=
    if sideBit (c.primeCut p) E.1.1=sideBit (c.primeCut p) E.1.2 then c.exponent p else 0
  have scale (P : Prop) [Decidable P] :
      c.exponent p*(if P then 1 else 0) = (if P then c.exponent p else 0) := by
    split_ifs <;> simp
  have hknown : c.exponent p*matchingEqualCount (c.primeCut p) o r =
      w (quartetEdge1 o r)+w (quartetEdge2 o r) := by
    dsimp only [matchingEqualCount,w,quartetEdge1,quartetEdge2,edgeIndex]
    rw [Nat.mul_add,scale,scale]
  rw [hknown]
  dsimp only [w]
  omega

/-- GCD of the three products of the original squared Gaussian gcd norms. -/
def quartetGcd (M : c.Minors) (o : Fin 5) : ℕ :=
  (c.pairX M o 0).gcd ((c.pairX M o 1).gcd (c.pairX M o 2))

theorem quartetGcd_pos (M : c.Minors) (o : Fin 5) : 0<c.quartetGcd M o :=
  Nat.gcd_pos_of_pos_left _ (c.pairX_pos M o 0)

theorem quartetGcd_dvd (M : c.Minors) (o : Fin 5) (r : Fin 3) :
    c.quartetGcd M o ∣ c.pairX M o r := by
  have h : c.quartetGcd M o ∣ (c.pairX M o 1).gcd (c.pairX M o 2) :=
    Nat.gcd_dvd_right _ _
  fin_cases r
  · exact Nat.gcd_dvd_left _ _
  · exact h.trans (Nat.gcd_dvd_left _ _)
  · exact h.trans (Nat.gcd_dvd_right _ _)

theorem quartetGcd_factorization (M : c.Minors) (o : Fin 5) (p : ℕ) :
    (c.quartetGcd M o).factorization p = min3 (fun r => (c.pairX M o r).factorization p) := by
  unfold quartetGcd min3
  rw [factorization_gcd_apply (c.pairX_pos M o 0).ne' (Nat.gcd_pos_of_pos_left _ (c.pairX_pos M o 1)).ne',
    factorization_gcd_apply (c.pairX_pos M o 1).ne' (c.pairX_pos M o 2).ne']

/-- The two valuation inequalities for the rational (t_ν) appearing
immediately before the preprint's quartic equation (8). -/
theorem divided_valuation_error (M : c.Minors) (hq : 0<q) (hc : IsCoprime a q)
    (o : Fin 5) (p : ℕ) (r : Fin 3) :
    let X := (c.pairX M o r/c.quartetGcd M o).factorization p
    let I := 2*(c.pairingProduct o r).factorization p
    let D := (c.budget o).factorization p
    X ≤ I+D ∧ I ≤ X+D := by
  classical
  dsimp only
  rw [factorization_div_apply (c.quartetGcd_dvd M o r),c.quartetGcd_factorization,c.pairingProduct_factor]
  by_cases hp : p∈c.splitSupport
  · let X := fun r => (c.pairX M o r).factorization p
    let I := fun r => c.exponent p*matchingEqualCount (c.primeCut p) o r
    have H := after_min_error X I ((c.budget o).factorization p)
      (fun r => c.pairing_rounded M hq hc o hp r) r
    have hI : I r-min3 I = 2*(if p∈c.pairingSupport o r then c.exponent p else 0) := by
      unfold I
      rw [min3_mul,← Nat.mul_sub_left_distrib,matchingEqualCount_after_min]
      have hm : p∈c.pairingSupport o r ↔ matchesPairing (c.primeCut p) o r = true := by
        simp [pairingSupport,hp]
      rw [if_congr hm rfl rfl]
      split_ifs <;> omega
    rw [hI] at H
    exact H
  · have hP : p∉c.pairingSupport o r := fun hp' => hp (Finset.mem_filter.1 hp').1
    have hX (k : Fin 3) : (c.pairX M o k).factorization p = c.exponent p+c.exponent p := by
      rw [pairX,factorization_mul_apply (M _).kpPos.ne' (M _).kpPos.ne',
        c.kp_factorization_unselected hp,c.kp_factorization_unselected hp]
    simp [hP,hX,min3]

/-- Assemble (c_r P_r^4) from the divided Plücker coefficients and the
bounded denominator, without making any choice of integer signs. -/
theorem exists_quartic (M : c.Minors) (hq : 0<q) (hc : IsCoprime a q) (o : Fin 5) :
    ∃ C : Fin 3 → ℕ, (∀ r, 0<C r ∧ C r≤N^20) ∧
      C 0*(c.pairingProduct o 0)^4+C 1*(c.pairingProduct o 1)^4 =
        C 2*(c.pairingProduct o 2)^4 := by
  let H := c.quartetGcd M o
  let D := c.budget o
  let X := c.pairX M o
  let A := c.pairA M o
  let P := c.pairingProduct o
  have hH : 0<H := c.quartetGcd_pos M o
  have hD : 0<D := c.budget_pos o
  have hdiv (r : Fin 3) : X r/H*H=X r :=
    Nat.div_mul_cancel (c.quartetGcd_dvd M o r)
  have hDivPos (r : Fin 3) : 0<X r/H := by
    by_contra! hz
    have hz0 : X r/H=0 := Nat.eq_zero_of_le_zero hz
    have hp := c.pairX_pos M o r
    have hprod := hdiv r
    rw [hz0,zero_mul] at hprod
    change 0 < X r at hp
    omega
  have ht (r : Fin 3) : ∃ t : ℕ, 0<t ∧ D*(X r/H)=P r^2*t ∧ t∣D^2 :=
    clear_rounding_denominator (hDivPos r) (c.pairingProduct_pos o r) hD
      (fun p => c.divided_valuation_error M hq hc o p r)
  choose T hT using ht
  let C := fun r => A r*(T r)^2
  have hcBd (r : Fin 3) : 0<C r ∧ C r≤N^20 := by
    refine ⟨Nat.mul_pos (c.pairA_pos M o r) (Nat.pow_pos (hT r).1),?_⟩
    have htd : T r ≤ D^2 := Nat.le_of_dvd (Nat.pow_pos hD) (hT r).2.2
    have htn : T r ≤ N^8 := by
      calc
        _ ≤ D^2 := htd
        _ ≤ (N^4)^2 := Nat.pow_le_pow_left (c.budget_bound o) 2
        _ = _ := by ring
    calc
      C r ≤ N^4*(N^8)^2 :=
        Nat.mul_le_mul (c.pairA_bound M o r) (Nat.pow_le_pow_left htn 2)
      _ = _ := by ring
  have hDX (r : Fin 3) : D*X r = H*(P r^2*T r) := by
    calc
      _ = D*((X r/H)*H) := by rw [hdiv r]
      _ = H*(D*(X r/H)) := by ring
      _ = _ := by rw [(hT r).2.1]
  have hterm (r : Fin 3) : D^2*(A r*(X r)^2)=H^2*(C r*(P r)^4) := by
    calc
      _ = A r*(D*X r)^2 := by ring
      _ = _ := by rw [hDX]; unfold C; ring
  refine ⟨C,hcBd,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hH.ne')
  rw [mul_add,← hterm 0,← hterm 1,← hterm 2,← mul_add]
  exact congrArg (fun n : ℕ => D^2*n) (c.quartet_plucker M hq.ne' o)

/-- Equation (9) uniformly across the five quartets and three pairings. -/
theorem pairing_polynomial (M : c.Minors) (hq : 0<q) (hc : IsCoprime a q)
    (K : ℕ) (hABC : ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c → ({a,b,c} : Set ℕ).Pairwise Nat.Coprime →
      a+b=c → c^4 ≤ K*(radical (a*b*c))^5) (o : Fin 5) (r : Fin 3) :
    c.pairingProduct o r ≤ K*N^540 := by
  obtain ⟨C,hC,hqE⟩ := c.exists_quartic M hq hc o
  have hb := quartic_bound_of_abc_constant K hABC N (C 0) (C 1) (C 2)
    (c.pairingProduct o 0) (c.pairingProduct o 1) (c.pairingProduct o 2)
    (hC 0).1 (hC 1).1 (hC 2).1 (c.pairingProduct_pos o 0)
    (c.pairingProduct_pos o 1) (c.pairingProduct_pos o 2)
    (hC 0).2 (hC 1).2 (hC 2).2
    (c.pairingProducts_coprime o (by decide : (0:Fin 3)≠1)) hqE
  apply le_trans _ hb
  fin_cases r
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

end Circle
end RudinABC
