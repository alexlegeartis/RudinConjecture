import RudinABC.GaussValuation

/-! # Split, inert, and ramified Gaussian prime probes

Proof of the (K'_{ij}) valuation formula of equation (7), and
its equal-valuation counterpart at inert and ramified primes. -/

namespace RudinABC
open Zsqrtd

theorem gauss_prime_or_norm {p : ℕ} (hp : p.Prime) :
    Prime (p:GaussianInt) ∨ ∃ π : GaussianInt, normN π=p := by
  classical
  by_cases hh : Prime (p:GaussianInt)
  · exact Or.inl hh
  · let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨a,b,hab⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p
      (fun hi => hh (irreducible_iff_prime.1 hi))
    refine Or.inr ⟨⟨(a:ℤ),(b:ℤ)⟩,?_⟩
    simpa [normN_coords] using hab

theorem natCast_normN_eq {p : ℕ} {π : GaussianInt} (h : normN π=p) :
    (p:GaussianInt) = π*star π := by
  have hc : (p:ℤ)=π.norm := by rw [← normN_cast]; exact_mod_cast h.symm
  calc
    _ = ((p:ℤ):GaussianInt) := by rw [Int.cast_natCast]
    _ = _ := by rw [hc,norm_eq_mul_conj]

theorem split_probe_value {p : ℕ} {π : GaussianInt} (hp : p.Prime) (hpodd : p≠2)
    (hn : normN π=p) : multiplicity π (p:GaussianInt)=1 := by
  have hπ : Prime π := gauss_prime_of_normN_prime (hn.symm ▸ hp)
  have hp0 : (p:GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hh := natCast_normN_eq hn
  have hstar0 : multiplicity π (star π)=0 := by
    by_contra! hn0
    exact split_not_dvd_star hp hpodd hn (dvd_of_multiplicity_pos (Nat.pos_of_ne_zero hn0))
  rw [hh,multiplicity_mul hπ (FiniteMultiplicity.of_prime_left hπ (hh ▸ hp0)),
    multiplicity_self,hstar0,Nat.add_zero]

/-- At an odd split prime the two conjugate exponents add to the rational
norm exponent. This equality is used independently at every one of the five labels. -/
theorem split_norm_value {p : ℕ} {π z : GaussianInt} (hp : p.Prime) (hpodd : p≠2)
    (hn : normN π=p) (hz : z≠0) :
    (normN z).factorization p = multiplicity π z + multiplicity (star π) z := by
  have hπ : Prime π := gauss_prime_of_normN_prime (hn.symm ▸ hp)
  have hd : p ∣ normN π := by rw [hn]
  simpa only [split_probe_value hp hpodd hn,Nat.mul_one] using gauss_multiplicity_norm hπ hp hd hz

theorem split_gcd_norm_value {p : ℕ} {π z w : GaussianInt} (hp : p.Prime)
    (hpodd : p≠2) (hn : normN π=p) (hz : z≠0) (hw : w≠0)
    (hS : normN z=normN w) :
    (normN (gaussGcd z w)).factorization p =
      min (multiplicity π z) (multiplicity π w) +
        min ((normN z).factorization p - multiplicity π z)
            ((normN z).factorization p - multiplicity π w) := by
  have hπ : Prime π := gauss_prime_of_normN_prime (hn.symm ▸ hp)
  have hn' : normN (star π)=p := by simpa only [normN_star] using hn
  have hπ' : Prime (star π) := gauss_prime_of_normN_prime (hn'.symm ▸ hp)
  have hzg := split_norm_value hp hpodd hn hz
  have hwg := split_norm_value hp hpodd hn hw
  have hez : (normN z).factorization p - multiplicity π z = multiplicity (star π) z := by omega
  have hew : (normN z).factorization p - multiplicity π w = multiplicity (star π) w := by
    rw [hS]
    omega
  rw [hez,hew,split_norm_value hp hpodd hn (gaussGcd_ne_zero_of_right hw),
    gauss_multiplicity_gcd hπ hz hw,gauss_multiplicity_gcd hπ' hz hw]

/-- At an inert rational prime the probe and its conjugate are the same. -/
theorem inert_gcd_norm_value {p : ℕ} {z w : GaussianInt} (hp : p.Prime)
    (hπ : Prime (p:GaussianInt)) (hz : z≠0) (hw : w≠0)
    (hS : normN z=normN w) :
    (normN (gaussGcd z w)).factorization p = (normN z).factorization p := by
  have hpnorm : p ∣ normN (p:GaussianInt) := by rw [normN_natCast]; exact dvd_pow_self p (by decide)
  have hprobe (u : GaussianInt) (hu : u≠0) :
      (normN u).factorization p = 2*multiplicity (p:GaussianInt) u := by
    simpa [multiplicity_self,two_mul] using gauss_multiplicity_norm hπ hp hpnorm hu
  have heq : multiplicity (p:GaussianInt) z = multiplicity (p:GaussianInt) w := by
    have h₁ := hprobe z hz
    have h₂ := hprobe w hw
    rw [hS] at h₁
    omega
  calc
    _ = 2*multiplicity (p:GaussianInt) (gaussGcd z w) := hprobe _ (gaussGcd_ne_zero_of_right hw)
    _ = 2*multiplicity (p:GaussianInt) w := by rw [gauss_multiplicity_gcd hπ hz hw,heq,min_self]
    _ = (normN w).factorization p := (hprobe w hw).symm
    _ = _ := by rw [hS]

private def ramifiedProbe : GaussianInt := ⟨1,1⟩

private theorem ramifiedProbe_norm : normN ramifiedProbe=2 := by
  norm_num [ramifiedProbe,normN_coords]

private theorem ramifiedProbe_prime : Prime ramifiedProbe :=
  gauss_prime_of_normN_prime (ramifiedProbe_norm.symm ▸ Nat.prime_two)

private theorem ramifiedProbe_assoc : Associated ramifiedProbe (star ramifiedProbe) := by
  let u : GaussianIntˣ :=
    ⟨⟨0,-1⟩,⟨0,1⟩,by decide,by decide⟩
  exact ⟨u, by decide⟩

private theorem ramifiedProbe_value : multiplicity ramifiedProbe (2:GaussianInt)=2 := by
  have hp := natCast_normN_eq ramifiedProbe_norm
  change (2:GaussianInt) = _ at hp
  rw [hp,multiplicity_mul ramifiedProbe_prime (FiniteMultiplicity.of_prime_left ramifiedProbe_prime
      (hp ▸ (by decide : (2:GaussianInt) ≠ 0))),
    ← multiplicity_eq_of_associated_right (a := ramifiedProbe) ramifiedProbe_assoc,
    multiplicity_self]

private theorem ramified_norm_value {z : GaussianInt} (hz : z≠0) :
    (normN z).factorization 2 = multiplicity ramifiedProbe z := by
  have hbd : 2 ∣ normN ramifiedProbe := by rw [ramifiedProbe_norm]
  have hh := gauss_multiplicity_norm ramifiedProbe_prime Nat.prime_two hbd hz
  have he : multiplicity (star ramifiedProbe) z = multiplicity ramifiedProbe z :=
    (multiplicity_eq_of_associated_left (c := z) ramifiedProbe_assoc)
  rw [he] at hh
  change (normN z).factorization 2 * multiplicity ramifiedProbe (2:GaussianInt) = _ at hh
  rw [ramifiedProbe_value] at hh
  omega

theorem ramified_gcd_norm_value {z w : GaussianInt} (hz : z≠0) (hw : w≠0)
    (hS : normN z=normN w) :
    (normN (gaussGcd z w)).factorization 2 = (normN z).factorization 2 := by
  have heq : multiplicity ramifiedProbe w = multiplicity ramifiedProbe z := by
    rw [← ramified_norm_value hw,← ramified_norm_value hz,hS]
  rw [ramified_norm_value (gaussGcd_ne_zero_of_right hw),
    gauss_multiplicity_gcd ramifiedProbe_prime hz hw,heq,min_self,ramified_norm_value hz]

end RudinABC
