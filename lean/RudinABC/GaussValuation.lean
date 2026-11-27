import RudinABC.Gaussian
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Linarith

/-! # Rational and Gaussian valuations for the same norm
The first half of §4, equation (7), uses ordinary algebraic prime powers.
We use Mathlib's multiplicity for Gaussian primes and Nat.factorization
for rational primes. -/

namespace RudinABC
open Zsqrtd

/-- The positive integer norm (squared complex absolute value). -/
def normN (z : GaussianInt) : ℕ := z.norm.natAbs

@[simp] theorem normN_cast (z : GaussianInt) : (normN z : ℤ) = z.norm :=
  GaussianInt.abs_natCast_norm z

theorem normN_pos {z : GaussianInt} (hz : z ≠ 0) : 0 < normN z := by
  exact_mod_cast (show (0:ℤ) < (normN z:ℤ) by rw [normN_cast]; exact GaussianInt.norm_pos.2 hz)

theorem normN_ne_zero {z : GaussianInt} (hz : z ≠ 0) : normN z ≠ 0 :=
  (normN_pos hz).ne'

@[simp] theorem normN_mul (z w : GaussianInt) : normN (z*w) = normN z * normN w := by
  simp [normN,norm_mul,Int.natAbs_mul]

@[simp] theorem normN_star (z : GaussianInt) : normN (star z) = normN z := by
  simp [normN]

theorem normN_coords (z : GaussianInt) : normN z = z.re.natAbs^2+z.im.natAbs^2 := by
  simpa [normN,pow_two] using GaussianInt.natAbs_norm_eq z

@[simp] theorem normN_natCast (n : ℕ) : normN (n : GaussianInt) = n^2 := by
  simp [normN,norm_natCast,Int.natAbs_mul,pow_two]

theorem normN_dvd {z w : GaussianInt} (h : z ∣ w) : normN z ∣ normN w := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨normN v,normN_mul _ _⟩

theorem gauss_prime_of_normN_prime {z : GaussianInt} (hp : (normN z).Prime) :
    Prime z := by
  apply irreducible_iff_prime.1
  refine ⟨?_,?_⟩
  · intro h
    have h1 := (Zsqrtd.norm_eq_one_iff.mpr h : normN z=1)
    exact hp.ne_one h1
  · intro u v he
    have hh : normN z = normN u*normN v := by rw [he,normN_mul]
    rcases (Nat.dvd_prime hp).1 ⟨normN v,hh⟩ with hu | hu
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.1 hu)
    · have hv : normN v=1 := by
        have hu' : 0<normN u := by rw [hu]; exact hp.pos
        apply Nat.eq_of_mul_eq_mul_left hu'
        rw [mul_one, ← hh, hu]
      exact Or.inr (Zsqrtd.norm_eq_one_iff.1 hv)

/-- The two factors over an odd split prime really are different.
If one divided its conjugate it would divide their sum and difference;
taking norms forces p to divide both coordinates and hence p² to divide p. -/
theorem split_not_dvd_star {π : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hodd : p≠2) (hn : normN π=p) : ¬π ∣ star π := by
  intro hd
  have h1 := normN_dvd (dvd_add (dvd_refl π) hd)
  have h2 := normN_dvd (dvd_sub (dvd_refl π) hd)
  have hRe : normN (π+star π) = (2*π.re.natAbs)^2 := by
    rw [normN_coords]
    simp [← two_mul, Int.natAbs_mul]
  have hIm : normN (π-star π) = (2*π.im.natAbs)^2 := by
    rw [normN_coords]
    simp [sub_neg_eq_add,← two_mul,Int.natAbs_mul]
  rw [hn,hRe] at h1
  rw [hn,hIm] at h2
  have hp2 : ¬p ∣ 2 := by
    intro hc
    rcases (Nat.dvd_prime Nat.prime_two).1 hc with h|h
    · exact hp.ne_one h
    · exact hodd h
  have hpr : p ∣ π.re.natAbs := ((hp.dvd_mul).mp (hp.dvd_of_dvd_pow h1)).resolve_left hp2
  have hpi : p ∣ π.im.natAbs := ((hp.dvd_mul).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp2
  have hpdvd : p^2 ∣ p := by
    calc
      p^2 ∣ π.re.natAbs^2+π.im.natAbs^2 :=
        dvd_add (pow_dvd_pow_of_dvd hpr 2) (pow_dvd_pow_of_dvd hpi 2)
      _ = normN π := (normN_coords π).symm
      _ = p := hn
  have hpb := Nat.le_of_dvd hp.pos hpdvd
  nlinarith [hp.two_le]

/-- A compatible conjugation across the entire prime-power divisibility tower. -/
theorem gauss_multiplicity_star (π z : GaussianInt) :
    multiplicity π (star z) = multiplicity (star π) z := by
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  constructor
  · rintro ⟨r, hr⟩
    use star r
    simpa [star_mul,star_pow,mul_comm] using congrArg star hr
  · rintro ⟨r, hr⟩
    use star r
    simpa [star_mul,star_pow,mul_comm] using congrArg star hr

theorem gauss_multiplicity_gcd {π z w : GaussianInt}
    (hπ : Prime π) (hz : z≠0) (hw : w≠0) :
    multiplicity π (gaussGcd z w) = min (multiplicity π z) (multiplicity π w) := by
  have hg := FiniteMultiplicity.of_prime_left hπ (gaussGcd_ne_zero_of_right hw : gaussGcd z w≠0)
  have hfz := FiniteMultiplicity.of_prime_left hπ hz
  have hfw := FiniteMultiplicity.of_prime_left hπ hw
  apply _root_.le_antisymm
  · exact le_min
      (hfz.le_multiplicity_of_pow_dvd ((pow_multiplicity_dvd π (gaussGcd z w)).trans (gaussGcd_dvd_left z w)))
      (hfw.le_multiplicity_of_pow_dvd ((pow_multiplicity_dvd π (gaussGcd z w)).trans (gaussGcd_dvd_right z w)))
  · exact hg.le_multiplicity_of_pow_dvd (dvd_gaussGcd
      (pow_dvd_of_le_multiplicity (min_le_left _ _))
      (pow_dvd_of_le_multiplicity (min_le_right _ _)))

/-- Valuation of a rational integer in the Gaussian local factor. The
multiplier is one in the inert/split cases and two in the ramified one. -/
theorem gauss_multiplicity_natCast {π : GaussianInt} {p n : ℕ}
    (hπ : Prime π) (hp : p.Prime) (hbound : p ∣ normN π) (hn : n≠0) :
    multiplicity π (n:GaussianInt) =
      n.factorization p * multiplicity π (p:GaussianInt) := by
  let e := n.factorization p
  let t := ordCompl[p] n
  have hnt : n = p^e*t := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hnat : (n:GaussianInt)=(p:GaussianInt)^e*(t:GaussianInt) := by exact_mod_cast hnt
  have hp0 : (p:GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0 : (n:GaussianInt) ≠ 0 := by exact_mod_cast hn
  have hndvd : ¬π ∣ (t:GaussianInt) := by
    intro hd
    apply Nat.not_dvd_ordCompl hp hn
    have hval := hbound.trans (normN_dvd hd)
    rw [normN_natCast] at hval
    exact hp.dvd_of_dvd_pow hval
  have hmul : multiplicity π (t:GaussianInt)=0 := by
    by_contra! hz
    exact hndvd (dvd_of_multiplicity_pos (Nat.pos_of_ne_zero hz))
  calc
    _ = multiplicity π ((p:GaussianInt)^e*(t:GaussianInt)) := by rw [← hnat]
    _ = _ := by
      rw [multiplicity_mul hπ (FiniteMultiplicity.of_prime_left hπ (hnat ▸ hn0)),
        (FiniteMultiplicity.of_prime_left hπ hp0).multiplicity_pow hπ,hmul,Nat.add_zero]

/-- Frobenius-free norm formula: the rational-prime valuation of the norm
is the multiplicity of the two conjugate probes divided by their ramification index. -/
theorem gauss_multiplicity_norm {π z : GaussianInt} {p : ℕ}
    (hπ : Prime π) (hp : p.Prime) (hbound : p ∣ normN π) (hz : z≠0) :
    (normN z).factorization p * multiplicity π (p:GaussianInt) =
      multiplicity π z + multiplicity (star π) z := by
  have hcast : (normN z : GaussianInt)=z*star z := by
    calc
      _ = ((normN z:ℤ):GaussianInt) := by rw [Int.cast_natCast]
      _ = (z.norm:GaussianInt) := by rw [normN_cast]
      _ = _ := norm_eq_mul_conj z
  have h0 : star z≠0 := fun hs => hz (by simpa using congrArg star hs)
  rw [← gauss_multiplicity_natCast hπ hp hbound (normN_ne_zero hz),
    hcast,multiplicity_mul hπ (FiniteMultiplicity.of_prime_left hπ (mul_ne_zero hz h0)),
    gauss_multiplicity_star]

end RudinABC
