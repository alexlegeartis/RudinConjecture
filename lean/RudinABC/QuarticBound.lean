import RudinABC.ABC
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Ring

/-! # Apply classical abc to the three terms in the quartic (preprint §4)
This file starts with the exact integer quartic equation. The extraction of
its coefficients from the rounded Gaussian valuations belongs to Factorization.
-/

namespace RudinABC

theorem abc_radical_eq_factor_radical (n : ℕ) : radical n = UniqueFactorizationMonoid.radical n := by
  rw [Nat.radical_eq_prod_primeFactors]
  rfl

private theorem pairwise_coprime_add {a b : ℕ} (h : Nat.Coprime a b) :
    ({a,b,a+b} : Set ℕ).Pairwise Nat.Coprime := by
  have hac : Nat.Coprime a (a+b) := Nat.coprime_self_add_right.2 h
  have hbc : Nat.Coprime b (a+b) := Nat.coprime_add_self_right.2 h.symm
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals
    first
    | exact (hxy rfl).elim
    | exact h
    | exact h.symm
    | exact hac
    | exact hac.symm
    | exact hbc
    | exact hbc.symm

/-- The preprint's gcd divides the coefficient product because at most one
of its paired factors can contain a given prime. The proof uses the stronger
two-coefficient divisibility and then includes the third. -/
private theorem quartic_gcd_dvd (c₁ c₂ c₃ P₁ P₂ : ℕ) (hP : Nat.Coprime P₁ P₂) :
    Nat.gcd (c₁*P₁^4) (c₂*P₂^4) ∣ c₁*c₂*c₃ := by
  let G := Nat.gcd (c₁*P₁^4) (c₂*P₂^4)
  have h₁ : G ∣ (c₁*c₂)*P₁^4 := by
    rw [show (c₁*c₂)*P₁^4 = (c₁*P₁^4)*c₂ by ring]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left ..) _
  have h₂ : G ∣ (c₁*c₂)*P₂^4 := by
    rw [show (c₁*c₂)*P₂^4 = (c₂*P₂^4)*c₁ by ring]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right ..) _
  have h := Nat.dvd_gcd h₁ h₂
  have hh : Nat.Coprime (P₁^4) (P₂^4) := (hP.pow_left 4).pow_right 4
  rw [Nat.gcd_mul_left, hh.gcd_eq_one, Nat.mul_one] at h
  exact dvd_mul_of_dvd_left h c₃

/-- Equation (8) of the paper yields equation (9) at exponent one-quarter.
The bound (K N^{540}) is what results from clearing the rational exponents,
not an effective bound on the abc constant (K). -/
theorem quartic_bound_of_abc_constant (K : ℕ)
    (hABC : ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c → ({a,b,c} : Set ℕ).Pairwise Nat.Coprime →
      a+b=c → c^4 ≤ K*(radical (a*b*c))^5)
    (N c₁ c₂ c₃ P₁ P₂ P₃ : ℕ)
    (hc₁ : 0<c₁) (hc₂ : 0<c₂) (hc₃ : 0<c₃)
    (hp₁ : 0<P₁) (hp₂ : 0<P₂) (hp₃ : 0<P₃)
    (hcs₁ : c₁ ≤ N^20) (hcs₂ : c₂ ≤ N^20) (hcs₃ : c₃ ≤ N^20)
    (hP : Nat.Coprime P₁ P₂)
    (hquartic : c₁*P₁^4+c₂*P₂^4 = c₃*P₃^4) :
    max P₁ (max P₂ P₃) ≤ K*N^540 := by
  let A := c₁*P₁^4
  let B := c₂*P₂^4
  let C := c₃*P₃^4
  let G := A.gcd B
  let a := A/G
  let b := B/G
  let c := C/G
  let M := max P₁ (max P₂ P₃)
  let cp := c₁*c₂*c₃
  let pp := P₁*P₂*P₃
  have hA : 0<A := by positivity
  have hB : 0<B := by positivity
  have hC : 0<C := by positivity
  have hG : 0<G := Nat.gcd_pos_of_pos_left _ hA
  have hM : 0<M := hp₁.trans_le (le_max_left _ _)
  have hGa : a*G=A := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hGb : b*G=B := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have heq : A+B=C := hquartic
  have hcDvd : G ∣ C := by
    rw [← heq]
    exact Nat.dvd_add (Nat.gcd_dvd_left A B) (Nat.gcd_dvd_right A B)
  have hGc : c*G=C := Nat.div_mul_cancel hcDvd
  have hsum : a+b=c := by
    apply Nat.eq_of_mul_eq_mul_right hG
    simpa only [Nat.add_mul,hGa,hGb,hGc] using hquartic
  have ha : 0<a := by
    by_contra! h
    have he : a=0 := Nat.eq_zero_of_le_zero h
    simp only [he,zero_mul] at hGa
    omega
  have hb : 0<b := by
    by_contra! h
    have he : b=0 := Nat.eq_zero_of_le_zero h
    simp only [he,zero_mul] at hGb
    omega
  have hc : 0<c := by omega
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hG
  have hABC' : c^4 ≤ K*(radical (a*b*c))^5 := by
    apply hABC _ _ _ ha hb hc
    · rw [← hsum]
      exact pairwise_coprime_add hcop
    · exact hsum
  have hcp : cp ≤ N^60 := by
    calc
      cp ≤ N^20*N^20*N^20 := Nat.mul_le_mul (Nat.mul_le_mul hcs₁ hcs₂) hcs₃
      _ = _ := by ring
  have hGbd : G ≤ N^60 :=
    (Nat.le_of_dvd (by positivity : 0<cp) (quartic_gcd_dvd c₁ c₂ c₃ P₁ P₂ hP)).trans hcp
  have hpp : pp ≤ M^3 := by
    have h₁ : P₁ ≤ M := le_max_left _ _
    have h₂ : P₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have h₃ : P₃ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    calc
      pp ≤ M*M*M := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
      _ = _ := by ring
  have hd : a*b*c ∣ A*B*C := mul_dvd_mul (mul_dvd_mul ⟨G,hGa.symm⟩ ⟨G,hGb.symm⟩) ⟨G,hGc.symm⟩
  have hr : radical (a*b*c) ∣ radical (A*B*C) := by
    rw [abc_radical_eq_factor_radical, abc_radical_eq_factor_radical]
    exact UniqueFactorizationMonoid.radical_dvd_radical hd (by positivity)
  have hr2 : radical (A*B*C) ∣ cp*pp := by
    have hprod : A*B*C = cp*pp^4 := by dsimp [A,B,C,cp,pp]; ring
    rw [hprod, abc_radical_eq_factor_radical]
    apply dvd_trans (UniqueFactorizationMonoid.radical_mul_dvd (a := cp) (b := pp^4))
    rw [UniqueFactorizationMonoid.radical_pow _ (by decide : (4:ℕ)≠0)]
    exact mul_dvd_mul UniqueFactorizationMonoid.radical_dvd_self UniqueFactorizationMonoid.radical_dvd_self
  have hrad : radical (a*b*c) ≤ N^60*M^3 := by
    exact (Nat.le_of_dvd (by positivity : 0<cp*pp) (hr.trans hr2)).trans (Nat.mul_le_mul hcp hpp)
  have h₁ : P₁^4 ≤ C := by
    have h := Nat.mul_le_mul_right (P₁^4) (show 1≤c₁ by omega)
    dsimp [C]
    rw [one_mul] at h
    omega
  have h₂ : P₂^4 ≤ C := by
    have h := Nat.mul_le_mul_right (P₂^4) (show 1≤c₂ by omega)
    dsimp [C]
    rw [one_mul] at h
    omega
  have h₃ : P₃^4 ≤ C := by
    have h := Nat.mul_le_mul_right (P₃^4) (show 1≤c₃ by omega)
    simpa [C] using h
  have hMC : M^4 ≤ C := by
    unfold M
    rcases le_total P₁ (max P₂ P₃) with hh|hh
    · rw [max_eq_right hh]
      rcases le_total P₂ P₃ with hh'|hh'
      · simpa [max_eq_right hh'] using h₃
      · simpa [max_eq_left hh'] using h₂
    · simpa [max_eq_left hh] using h₁
  have hfinal : M^16 ≤ K*N^540*M^15 := calc
    _ = (M^4)^4 := by ring
    _ ≤ C^4 := Nat.pow_le_pow_left hMC 4
    _ = c^4*G^4 := by rw [← hGc,mul_pow]
    _ ≤ (K*(radical (a*b*c))^5)*(N^60)^4 :=
      Nat.mul_le_mul hABC' (Nat.pow_le_pow_left hGbd 4)
    _ ≤ (K*(N^60*M^3)^5)*(N^60)^4 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrad 5))
    _ = _ := by ring
  have hlast : M*M^15 ≤ (K*N^540)*M^15 := by
    rwa [show M*M^15=M^16 by ring]
  exact Nat.le_of_mul_le_mul_right hlast (by positivity)

end RudinABC
