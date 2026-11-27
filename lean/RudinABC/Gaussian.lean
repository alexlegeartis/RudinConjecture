import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.EuclideanDomain
import RudinABC.Plucker

/-! # Gaussian gcd and its two imaginary parts (preprint §3)

These are ordinary equal-norm representations. No appeal to an unproved
splitting assertion is needed to conclude that the coprime quotients are
conjugate up to a unit.
-/

namespace RudinABC

open Zsqrtd

local instance : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt

/-- A canonical Euclidean gcd, interchangeable up to units with any gcd. -/
def gaussGcd (z w : GaussianInt) : GaussianInt := GCDMonoid.gcd z w

theorem gaussGcd_dvd_left (z w : GaussianInt) : gaussGcd z w ∣ z :=
  GCDMonoid.gcd_dvd_left z w

theorem gaussGcd_dvd_right (z w : GaussianInt) : gaussGcd z w ∣ w :=
  GCDMonoid.gcd_dvd_right z w

theorem dvd_gaussGcd {a z w : GaussianInt} (hz : a ∣ z) (hw : a ∣ w) :
    a ∣ gaussGcd z w := GCDMonoid.dvd_gcd hz hw

theorem gaussGcd_ne_zero_of_right {z w : GaussianInt} (hw : w ≠ 0) :
    gaussGcd z w ≠ 0 :=
  gcd_ne_zero_of_right hw

theorem gauss_norm_dvd {z w : GaussianInt} (h : z ∣ w) : z.norm ∣ w.norm := by
  obtain ⟨g,rfl⟩ := h
  exact ⟨g.norm, norm_mul z g⟩

theorem gauss_mul_conj_eq_of_norm_eq {u v : GaussianInt} (hn : u.norm = v.norm) :
    u * star u = v * star v := by
  rw [← norm_eq_mul_conj, ← norm_eq_mul_conj, hn]

/-- The two coprime equal-norm cofactors are conjugate up to a unit. -/
theorem gauss_associated_star_of_coprime_norm {u v : GaussianInt}
    (hc : IsCoprime u v) (hn : u.norm = v.norm) : Associated v (star u) := by
  have he := gauss_mul_conj_eq_of_norm_eq hn
  have hstar : IsCoprime (star u) (star v) := by
    obtain ⟨a, b, hab⟩ := hc
    exact ⟨star a, star b, by
      simpa only [star_add, star_mul, star_one, mul_comm] using congrArg star hab⟩
  apply associated_of_dvd_dvd
  · exact hc.symm.dvd_of_dvd_mul_left ⟨star v, he⟩
  · apply hstar.dvd_of_dvd_mul_right
    use u
    simpa only [mul_comm] using he.symm

/-- A same-norm Gaussian pair decomposes exactly into its gcd and the two
coprime equal-norm cofactors, with the second cofactor a conjugate times a unit. -/
theorem gauss_gcd_cofactors {z w : GaussianInt} (hw : w ≠ 0) (hn : z.norm = w.norm) :
    ∃ u v : GaussianInt,
      z = gaussGcd z w * u ∧ w = gaussGcd z w * v ∧
      u.norm = v.norm ∧ Associated v (star u) := by
  let g := gaussGcd z w
  let u := z/g
  let v := w/g
  have hg : g ≠ 0 := (gcd_ne_zero_of_right hw : GCDMonoid.gcd z w ≠ 0)
  have hz : z = g*u :=
    (EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_left z w)).symm
  have hw' : w = g*v :=
    (EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_right z w)).symm
  have hnorm : u.norm = v.norm := by
    apply mul_left_cancel₀ (GaussianInt.norm_eq_zero.not.2 hg)
    rwa [hz, hw', norm_mul, norm_mul] at hn
  exact ⟨u, v, hz, hw', hnorm,
    gauss_associated_star_of_coprime_norm (isCoprime_div_gcd_div_gcd hw) hnorm⟩

/-- Put (a_i+b_i i=z_i^2). The Gaussian gcd norm squared divides the
negative minor (D). -/
theorem gauss_norm_sq_dvd_neg_minor {z w g u v : GaussianInt}
    (hz : z = g*u) (hw : w = g*v) :
    g.norm^2 ∣ minor ((z^2).re,(z^2).im) ((w^2).re,(w^2).im) := by
  have him : (star (z^2) * w^2).im = minor ((z^2).re,(z^2).im) ((w^2).re,(w^2).im) := by
    simp only [im_mul, im_star, re_star, minor]
    ring
  rw [← him]
  have hfac : star (z^2) * w^2 =
      ((g.norm^2 : ℤ) : GaussianInt) * (star (u^2) * v^2) := by
    rw [hz, hw, star_pow, star_mul]
    push_cast
    rw [norm_eq_mul_conj]
    simp only [star_pow]
    ring
  rw [hfac]
  exact ⟨(star (u^2)*v^2).im, by simp only [im_mul, re_intCast, im_intCast, zero_mul, add_zero]⟩

/-- The common cofactor norm squared divides the positive minor (E). -/
theorem gauss_norm_sq_dvd_pos_minor {z w g u v : GaussianInt}
    (hz : z = g*u) (hw : w = g*v) (hAssoc : Associated v (star u)) :
    u.norm^2 ∣ (z^2).re * (w^2).im + (z^2).im * (w^2).re := by
  rw [← im_mul]
  obtain ⟨e, he⟩ := hAssoc.symm
  have hfac : z^2 * w^2 =
      ((u.norm^2 : ℤ) : GaussianInt) * (g^4 * (e : GaussianInt)^2) := by
    rw [hz, hw, ← he]
    push_cast
    rw [norm_eq_mul_conj]
    ring
  rw [hfac]
  exact ⟨(g^4 * (e : GaussianInt)^2).im, by simp only [im_mul, re_intCast, im_intCast, zero_mul, add_zero]⟩

end RudinABC
