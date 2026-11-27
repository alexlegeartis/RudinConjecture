import RudinABC.Rounding
import Mathlib.Data.Nat.Factorization.Basic

/-! # The integer form of the preprint's rational denominator clearing -/

namespace RudinABC

theorem factorization_mul_apply {x y : ℕ} (hx : x≠0) (hy : y≠0) (p : ℕ) :
    (x*y).factorization p = x.factorization p+y.factorization p := by
  rw [Nat.factorization_mul hx hy,Finsupp.add_apply]

theorem factorization_pow_apply (x k p : ℕ) :
    (x^k).factorization p = k*x.factorization p := by
  simp [Nat.factorization_pow,Finsupp.smul_apply]

theorem factorization_gcd_apply {x y : ℕ} (hx : x≠0) (hy : y≠0) (p : ℕ) :
    (x.gcd y).factorization p = min (x.factorization p) (y.factorization p) := by
  rw [Nat.factorization_gcd hx hy,Finsupp.inf_apply]

theorem factorization_div_apply {x y : ℕ} (h : y∣x) (p : ℕ) :
    (x/y).factorization p = x.factorization p-y.factorization p := by
  rw [Nat.factorization_div h,Finsupp.tsub_apply]

/-- If the valuations of (X/P²) have absolute value bounded by the
valuations of (D), then (D X/P²) is an integer dividing (D²).
This is precisely the paper's `D₀ t_ν` and its size estimate. -/
theorem clear_rounding_denominator {X P D : ℕ} (hX : 0<X) (hP : 0<P) (hD : 0<D)
    (h : ∀ p, X.factorization p ≤ 2*P.factorization p+D.factorization p ∧
      2*P.factorization p ≤ X.factorization p+D.factorization p) :
    ∃ T : ℕ, 0<T ∧ D*X=P^2*T ∧ T∣D^2 := by
  have hPX : P^2∣D*X := by
    apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ hP.ne') (mul_ne_zero hD.ne' hX.ne')).1
    intro p
    rw [factorization_pow_apply,factorization_mul_apply hD.ne' hX.ne']
    have hp := (h p).2
    omega
  let T := D*X/(P^2)
  have hTprod : T*P^2 = D*X := Nat.div_mul_cancel hPX
  have hT : 0<T := by
    by_contra! hz
    have hzz : T=0 := Nat.eq_zero_of_le_zero hz
    have hpos := Nat.mul_pos hD hX
    rw [hzz,zero_mul] at hTprod
    omega
  refine ⟨T,hT,by rw [mul_comm (P^2) T,hTprod],?_⟩
  apply (Nat.factorization_le_iff_dvd hT.ne' (pow_ne_zero _ hD.ne')).1
  intro p
  have hh := congrArg (fun x : ℕ => x.factorization p) hTprod
  rw [factorization_mul_apply hT.ne' (pow_ne_zero _ hP.ne'),factorization_pow_apply,
      factorization_mul_apply hD.ne' hX.ne'] at hh
  rw [factorization_pow_apply]
  have hi := (h p).1
  omega

/-- Factoring a product over a set of distinct primes selects exactly the
valuation of that prime, if retained. -/
theorem prime_product_factorization (T : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p∈T, p.Prime) (r : ℕ) :
    (∏ p ∈ T, p^(e p)).factorization r = if r∈T then e r else 0 := by
  rw [Nat.factorization_prod_apply (fun p hp' => pow_ne_zero _ (hp p hp').ne_zero)]
  calc
    _ = ∑ p ∈ T, if p=r then e p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp'
      rw [(hp p hp').factorization_pow,Finsupp.single_apply]
    _ = _ := Finset.sum_ite_eq' T r e

/-- Per-place positive parts of a prime-factor product specialize the
abstract weights in the cut proof. -/
theorem log_prime_product (T : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p∈T, p.Prime) :
    Real.log (↑(∏ p ∈ T, p^(e p)) : ℝ) =
      ∑ p ∈ T, (e p : ℝ)*Real.log (p:ℝ) := by
  push_cast
  rw [Real.log_prod (fun p hp' => pow_ne_zero _ (by exact_mod_cast (hp p hp').ne_zero))]
  simp only [Real.log_pow]

theorem min3_mul (e : ℕ) (f : Fin 3 → ℕ) :
    min3 (fun r => e*f r) = e*min3 f := by
  simp [min3,min_mul_mul_left]

end RudinABC
