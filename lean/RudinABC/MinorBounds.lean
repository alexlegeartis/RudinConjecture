import RudinABC.Circle
import RudinABC.Gaussian

/-! # Integer minor quotients and their bounds (preprint §3, eqs. (3)–(5)) -/

namespace RudinABC
open Zsqrtd

private theorem isCoprime_of_gcd_dvd_two {q S h : ℤ}
    (hgcd : ((q.gcd S : ℕ):ℤ) ∣ 2) (hh : h ∣ S)
    (hodd : ¬(2:ℤ) ∣ q ∨ ¬(2:ℤ) ∣ h) : IsCoprime q h := by
  apply Int.isCoprime_iff_gcd_eq_one.2
  have hd : q.gcd h ∣ q.gcd S :=
    Int.dvd_gcd (Int.gcd_dvd_left q h) ((Int.gcd_dvd_right q h).trans hh)
  have h2 : q.gcd h ∣ 2 := hd.trans (Int.natCast_dvd_natCast.1 hgcd)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h₁ | h₂
  · exact h₁
  · have hq2 : (2:ℤ) ∣ q := by simpa [h₂] using Int.gcd_dvd_left q h
    have hh2 : (2:ℤ) ∣ h := by simpa [h₂] using Int.gcd_dvd_right q h
    exact (hodd.elim (fun h => h hq2) (fun h => h hh2)).elim

private theorem even_gauss_norm_of_odd_coords {x y : ℤ}
    (hx : x % 2 = 1) (hy : y % 2 = 1) : (⟨1,1⟩ : GaussianInt) ∣ (⟨x,y⟩ : GaussianInt) := by
  use (⟨(x+y)/2,(y-x)/2⟩ : GaussianInt)
  ext
  · change x = 1*((x+y)/2) + (-1)*1*((y-x)/2)
    omega
  · change y = 1*((y-x)/2) + 1*((x+y)/2)
    omega

namespace Circle

variable {N : ℕ} {q a : ℤ} (c : Circle N q a)

def gaussian (i : Fin 5) : GaussianInt := ⟨c.x i,c.y i⟩
def A (i : Fin 5) : ℤ := q*(c.d i:ℤ)
def B (i : Fin 5) : ℤ := 2*c.x i*c.y i
def D (i j : Fin 5) : ℤ := minor (c.A i,c.B i) (c.A j,c.B j)
def E (i j : Fin 5) : ℤ := c.A i*c.B j+c.B i*c.A j

theorem A_pos (hq : 0<q) (i : Fin 5) : 0<c.A i :=
  mul_pos hq (by exact_mod_cast c.dPos i)

theorem B_pos (i : Fin 5) : 0<c.B i := by
  unfold B
  exact mul_pos (mul_pos (by norm_num) (c.xPos i)) (c.yPos i)

theorem B_le_S (i : Fin 5) : c.B i ≤ c.S := by
  unfold B
  have h := c.norm_eq i
  nlinarith [sq_nonneg (c.x i-c.y i)]

theorem gauss_norm (i : Fin 5) : (c.gaussian i).norm = c.S := by
  rw [norm_def]
  change c.x i*c.x i-(-1)*c.y i*c.y i = c.S
  linear_combination c.norm_eq i

theorem gauss_nonzero (i : Fin 5) : c.gaussian i ≠ 0 :=
  GaussianInt.norm_pos.1 (by rw [c.gauss_norm]; exact c.SPos)

theorem gauss_sq_re (i : Fin 5) : (c.gaussian i ^ 2).re = c.A i := by
  rw [pow_two, re_mul]
  change c.x i*c.x i+(-1)*c.y i*c.y i = q*(c.d i:ℤ)
  linear_combination c.diff_eq i

theorem gauss_sq_im (i : Fin 5) : (c.gaussian i ^ 2).im = c.B i := by
  rw [pow_two, im_mul]
  change c.x i*c.y i+c.y i*c.x i = 2*c.x i*c.y i
  ring

theorem norm_coords (i : Fin 5) : c.A i^2+c.B i^2 = c.S^2 := by
  rw [← c.gauss_sq_re, ← c.gauss_sq_im, ← c.gauss_norm i]
  have hv := norm_mul (c.gaussian i) (c.gaussian i)
  rw [← pow_two, norm_def] at hv
  calc
    _ = (c.gaussian i^2).re*(c.gaussian i^2).re -
        (-1)*(c.gaussian i^2).im*(c.gaussian i^2).im := by ring
    _ = _ := by simpa only [pow_two] using hv

theorem A_decreasing (hq : 0<q) {i j : Fin 5} (hij : i<j) : c.A j < c.A i :=
  mul_lt_mul_of_pos_left (by exact_mod_cast c.decreasing hij) hq

theorem B_increasing (hq : 0<q) {i j : Fin 5} (hij : i<j) : c.B i < c.B j := by
  have ha := c.A_decreasing hq hij
  by_contra! hb
  have h₁ : 0 < c.A i^2-c.A j^2 := by
    have hm := mul_pos (sub_pos.2 ha) (add_pos (c.A_pos hq i) (c.A_pos hq j))
    nlinarith only [hm]
  have h₂ : 0 ≤ c.B i^2-c.B j^2 := by
    have hm := mul_nonneg (sub_nonneg.2 hb) (add_nonneg (c.B_pos i).le (c.B_pos j).le)
    nlinarith only [hm]
  linarith [c.norm_coords i,c.norm_coords j]

theorem D_pos (hq : 0<q) {i j : Fin 5} (hij : i<j) : 0<c.D i j := by
  unfold D minor
  have hi := mul_lt_mul_of_pos_right (c.A_decreasing hq hij) (c.B_pos i)
  have hj := mul_lt_mul_of_pos_left (c.B_increasing hq hij) (c.A_pos hq i)
  linarith

theorem E_pos (hq : 0<q) (i j : Fin 5) : 0<c.E i j :=
  add_pos (mul_pos (c.A_pos hq i) (c.B_pos j)) (mul_pos (c.B_pos i) (c.A_pos hq j))

theorem D_le_qNS (hq : 0<q) (i j : Fin 5) : c.D i j ≤ q*(N:ℤ)*c.S := by
  unfold D minor
  calc
    _ ≤ c.A i*c.B j := sub_le_self _ (mul_nonneg (c.B_pos i).le (c.A_pos hq j).le)
    _ ≤ c.A i*c.S := mul_le_mul_of_nonneg_left (c.B_le_S j) (c.A_pos hq i).le
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ c.SPos.le
      unfold A
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (c.dLt i).le) hq.le

theorem minors_product (i j : Fin 5) :
    c.D i j*c.E i j = q^2*c.S^2*((c.d i:ℤ)^2-(c.d j:ℤ)^2) := by
  have hi : c.B i^2 = c.S^2-c.A i^2 := by linarith [c.norm_coords i]
  have hj : c.B j^2 = c.S^2-c.A j^2 := by linarith [c.norm_coords j]
  calc
    _ = c.A i^2*c.B j^2-c.B i^2*c.A j^2 := by unfold D E minor; ring
    _ = _ := by rw [hi,hj]; unfold A; ring

theorem q_dvd_D (i j : Fin 5) : q ∣ c.D i j := by
  use (c.d i:ℤ)*c.B j-c.B i*(c.d j:ℤ)
  unfold D minor A
  ring

theorem q_dvd_E (i j : Fin 5) : q ∣ c.E i j := by
  use (c.d i:ℤ)*c.B j+c.B i*(c.d j:ℤ)
  unfold E A
  ring

private theorem odd_a_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) : ¬(2:ℤ) ∣ a := by
  intro ha
  have h := hc.isUnit_of_dvd' ha hq2
  norm_num [Int.isUnit_iff_natAbs_eq] at h

private theorem root_odd_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q)
    {r : ℤ} {n : ℕ} (hr : r^2 = q*(n:ℤ)+a) : r%2=1 := by
  have ha := odd_a_of_even_q hc hq2
  by_contra! hr2
  have hr' : (2:ℤ) ∣ r := Int.dvd_iff_emod_eq_zero.2 (by omega)
  have hqN : (2:ℤ) ∣ q*(n:ℤ) := dvd_mul_of_dvd_left hq2 _
  have hrN : (2:ℤ) ∣ r^2 := dvd_trans hr' (dvd_pow_self _ (by decide))
  apply ha
  rw [hr] at hrN
  simpa using dvd_sub hrN hqN

theorem x_odd_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) (i : Fin 5) :
    c.x i%2=1 := root_odd_of_even_q hc hq2 (c.xSquare i)

theorem y_odd_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) (i : Fin 5) :
    c.y i%2=1 := root_odd_of_even_q hc hq2 (c.ySquare i)

private theorem odd_sq_mod_four {r : ℤ} (hr : r%2=1) : Int.ModEq 4 (r^2) 1 := by
  apply Int.modEq_iff_dvd.2
  have h : r = 2*(r/2)+1 := by omega
  use -((r/2)^2+r/2)
  nth_rewrite 1 [h]
  ring

theorem S_two_mod_four_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) :
    c.S%4=2 := by
  have hx := odd_sq_mod_four (c.x_odd_of_even_q hc hq2 0)
  have hy := odd_sq_mod_four (c.y_odd_of_even_q hc hq2 0)
  have hs := (hx.add hy).eq
  rw [c.norm_eq] at hs
  norm_num at hs
  exact hs

theorem four_q_dvd_D (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) (i j : Fin 5) :
    4*q ∣ c.D i j := by
  have hoddX (k : Fin 5) : Int.ModEq 2 (c.x k) 1 := c.x_odd_of_even_q hc hq2 k
  have hoddY (k : Fin 5) : Int.ModEq 2 (c.y k) 1 := c.y_odd_of_even_q hc hq2 k
  have hpar (k l : Fin 5) :
      Int.ModEq 2 ((c.d k:ℤ)*c.x l*c.y l) (c.t:ℤ) := by
    simpa only [mul_one] using (((c.dParity k).mul (hoddX l)).mul (hoddY l))
  obtain ⟨v,hv⟩ := Int.modEq_iff_dvd.1 ((hpar j i).trans (hpar i j).symm)
  use v
  calc
    _ = (2*q)*((c.d i:ℤ)*c.x j*c.y j-(c.d j:ℤ)*c.x i*c.y i) := by unfold D minor A B; ring
    _ = _ := by rw [hv]; ring

theorem gcd_norm_even_of_even_q (hc : IsCoprime a q) (hq2 : (2:ℤ) ∣ q) (i j : Fin 5) :
    (2:ℤ) ∣ (gaussGcd (c.gaussian i) (c.gaussian j)).norm := by
  have H (k : Fin 5) : (⟨1,1⟩ : GaussianInt) ∣ c.gaussian k :=
    even_gauss_norm_of_odd_coords (c.x_odd_of_even_q hc hq2 k) (c.y_odd_of_even_q hc hq2 k)
  have h := gauss_norm_dvd (dvd_gaussGcd (H i) (H j))
  exact h

/-- Combining the Gaussian minor divisors with (q), with exactly the extra
factor of four for (D) when (q) is even. -/
theorem q_mul_norm_sq_dvd_minors (hc : IsCoprime a q) (i j : Fin 5)
    {u v : GaussianInt}
    (hi : c.gaussian i = (gaussGcd (c.gaussian i) (c.gaussian j))*u)
    (hj : c.gaussian j = (gaussGcd (c.gaussian i) (c.gaussian j))*v)
    (hAssoc : Associated v (star u)) :
    let G := (gaussGcd (c.gaussian i) (c.gaussian j)).norm
    let K := u.norm
    q*G^2 ∣ c.D i j ∧ q*K^2 ∣ c.E i j := by
  let G := (gaussGcd (c.gaussian i) (c.gaussian j)).norm
  let K := u.norm
  change q*G^2 ∣ c.D i j ∧ q*K^2 ∣ c.E i j
  have hGK : G*K = c.S := by
    unfold G K
    rw [← norm_mul, ← hi, c.gauss_norm]
  have hGdvd : G ∣ c.S := ⟨K,hGK.symm⟩
  have hKdvd : K ∣ c.S := ⟨G,by rw [mul_comm,hGK]⟩
  have hD : G^2 ∣ c.D i j := by
    simpa only [c.gauss_sq_re,c.gauss_sq_im,D] using gauss_norm_sq_dvd_neg_minor hi hj
  have hE : K^2 ∣ c.E i j := by
    simpa only [c.gauss_sq_re,c.gauss_sq_im,E] using gauss_norm_sq_dvd_pos_minor hi hj hAssoc
  have hgcd := c.gcd_dvd_two hc
  by_cases hq2 : (2:ℤ) ∣ q
  · obtain ⟨G₀,hG₀⟩ := c.gcd_norm_even_of_even_q hc hq2 i j
    have hhG : G = 2*G₀ := hG₀
    have hSo : ¬(4:ℤ) ∣ c.S := by
      rw [Int.dvd_iff_emod_eq_zero,c.S_two_mod_four_of_even_q hc hq2]
      norm_num
    have hG₀S : G₀ ∣ c.S := ⟨2*K,by rw [← hGK,hhG]; ring⟩
    have hG₀o : ¬(2:ℤ) ∣ G₀ := by
      rintro ⟨g,hg⟩
      apply hSo
      use g*K
      rw [← hGK,hhG,hg]
      ring
    have hKo : ¬(2:ℤ) ∣ K := by
      rintro ⟨k,hk⟩
      apply hSo
      use G₀*k
      rw [← hGK,hhG,hk]
      ring
    have hGc := (isCoprime_of_gcd_dvd_two hgcd hG₀S (Or.inr hG₀o)).pow_right (n:=2)
    have hKc := (isCoprime_of_gcd_dvd_two hgcd hKdvd (Or.inr hKo)).pow_right (n:=2)
    obtain ⟨m,hm⟩ := c.four_q_dvd_D hc hq2 i j
    have hGdvd' : G₀^2 ∣ q*m := by
      rw [hhG, mul_pow, show (2:ℤ)^2=4 by norm_num, hm, mul_assoc] at hD
      exact (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).1 hD
    obtain ⟨k,hk⟩ := hGc.mul_dvd (dvd_mul_right q m) hGdvd'
    refine ⟨⟨k,?_⟩, hKc.mul_dvd (c.q_dvd_E i j) hE⟩
    calc
      c.D i j = 4*(q*m) := by rw [hm]; ring
      _ = 4*(q*G₀^2*k) := by rw [hk]
      _ = _ := by rw [hhG]; ring
  · exact ⟨(isCoprime_of_gcd_dvd_two hgcd hGdvd (Or.inl hq2)).pow_right.mul_dvd
        (c.q_dvd_D i j) hD,
      (isCoprime_of_gcd_dvd_two hgcd hKdvd (Or.inl hq2)).pow_right.mul_dvd
        (c.q_dvd_E i j) hE⟩

/-- The exact positive natural arithmetic attached to an ordered pair. -/
structure MinorData (i j : Fin 5) where
  kp : ℕ
  k : ℕ
  jminus : ℕ
  jplus : ℕ
  kpIsNorm : kp = (gaussGcd (c.gaussian i) (c.gaussian j)).norm.natAbs
  kpPos : 0 < kp
  kPos : 0 < k
  minusPos : 0 < jminus
  plusPos : 0 < jplus
  normProduct : kp*k = c.S.natAbs
  DEq : c.D i j = q*(kp:ℤ)^2*(jminus:ℤ)
  EEq : c.E i j = q*(k:ℤ)^2*(jplus:ℤ)
  productExact : jminus*jplus = c.d i^2 - c.d j^2
  minusBound : jminus ≤ N^2
  plusBound : jplus ≤ N^2
  kpBound : kp^2 ≤ N*c.S.natAbs
  kBound : c.S.natAbs ≤ N*k^2

/-- The Gaussian norm factorization and parity yield all the integer
and size bounds in equations (3)–(5). -/
theorem exists_minor_data (hq : 0<q) (hc : IsCoprime a q)
    {i j : Fin 5} (hij : i<j) : Nonempty (c.MinorData i j) := by
  obtain ⟨u,v,hi,hj,_,hAssoc⟩ := gauss_gcd_cofactors (c.gauss_nonzero j)
    ((c.gauss_norm i).trans (c.gauss_norm j).symm)
  let G := (gaussGcd (c.gaussian i) (c.gaussian j)).norm
  let K := u.norm
  have hGK : G*K = c.S := by
    unfold G K
    rw [← norm_mul, ← hi, c.gauss_norm]
  have hG : 0<G := GaussianInt.norm_pos.2 (gaussGcd_ne_zero_of_right (c.gauss_nonzero j))
  have hK : 0<K := by
    by_contra! h
    have hh := mul_nonpos_of_nonneg_of_nonpos hG.le h
    rw [hGK] at hh
    exact (not_lt_of_ge hh) c.SPos
  obtain ⟨⟨Jm,hm⟩,⟨Jp,hp⟩⟩ := c.q_mul_norm_sq_dvd_minors hc i j hi hj hAssoc
  change c.D i j = q*G^2*Jm at hm
  change c.E i j = q*K^2*Jp at hp
  have hJm : 0<Jm := by
    have hh : 0<q*G^2*Jm := hm ▸ c.D_pos hq hij
    have hpos : 0<q*G^2 := mul_pos hq (pow_pos hG 2)
    exact ((mul_pos_iff.mp hh).resolve_right (fun h => (not_lt_of_ge hpos.le) h.1)).2
  have hJp : 0<Jp := by
    have hh : 0<q*K^2*Jp := hp ▸ c.E_pos hq i j
    have hpos : 0<q*K^2 := mul_pos hq (pow_pos hK 2)
    exact ((mul_pos_iff.mp hh).resolve_right (fun h => (not_lt_of_ge hpos.le) h.1)).2
  have hfactor : Jm*Jp = (c.d i:ℤ)^2-(c.d j:ℤ)^2 := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hq.ne') (pow_ne_zero 2 c.SPos.ne'))
    calc
      _ = c.D i j*c.E i j := by rw [hm,hp,← hGK]; ring
      _ = _ := c.minors_product i j
  have hJprod : Jm*Jp ≤ (N:ℤ)^2 := by
    have hd : (c.d i:ℤ) ≤ N := by exact_mod_cast (c.dLt i).le
    have hb := pow_le_pow_left₀ (by positivity : 0≤(c.d i:ℤ)) hd 2
    linarith [sq_nonneg (c.d j:ℤ)]
  have hJmBd : Jm ≤ (N:ℤ)^2 := by
    have h1 : 1≤Jp := by omega
    have hb := mul_le_mul_of_nonneg_left h1 hJm.le
    linarith
  have hJpBd : Jp ≤ (N:ℤ)^2 := by
    have h1 : 1≤Jm := by omega
    have hb := mul_le_mul_of_nonneg_right h1 hJp.le
    linarith
  have hGbd : G^2 ≤ (N:ℤ)*c.S := by
    apply le_of_mul_le_mul_left _ hq
    calc
      q*G^2 = (q*G^2)*1 := by ring
      _ ≤ q*G^2*Jm := mul_le_mul_of_nonneg_left (by omega) (by positivity)
      _ = c.D i j := hm.symm
      _ ≤ _ := by simpa [mul_assoc] using c.D_le_qNS hq i j
  have hKbd : c.S ≤ (N:ℤ)*K^2 := by
    apply le_of_mul_le_mul_left _ c.SPos
    calc
      _ = G^2*K^2 := by rw [← hGK]; ring
      _ ≤ ((N:ℤ)*c.S)*K^2 := mul_le_mul_of_nonneg_right hGbd (sq_nonneg K)
      _ = _ := by ring
  have hcS : (c.S.natAbs:ℤ)=c.S := Int.natAbs_of_nonneg c.SPos.le
  have hcG : (G.natAbs:ℤ)=G := Int.natAbs_of_nonneg hG.le
  have hcK : (K.natAbs:ℤ)=K := Int.natAbs_of_nonneg hK.le
  have hcJm : (Jm.natAbs:ℤ)=Jm := Int.natAbs_of_nonneg hJm.le
  have hcJp : (Jp.natAbs:ℤ)=Jp := Int.natAbs_of_nonneg hJp.le
  have hdcomp : c.d j^2 ≤ c.d i^2 := Nat.pow_le_pow_left (c.decreasing hij).le 2
  refine ⟨⟨G.natAbs,K.natAbs,Jm.natAbs,Jp.natAbs,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact_mod_cast hcG ▸ hG
  · exact_mod_cast hcK ▸ hK
  · exact_mod_cast hcJm ▸ hJm
  · exact_mod_cast hcJp ▸ hJp
  · exact_mod_cast (show (G.natAbs:ℤ)*(K.natAbs:ℤ)=(c.S.natAbs:ℤ) by simpa [hcS,hcG,hcK] using hGK)
  · simpa only [hcG,hcJm] using hm
  · simpa only [hcK,hcJp] using hp
  · have he : ((Jm.natAbs*Jp.natAbs:ℕ):ℤ) = ((c.d i^2-c.d j^2:ℕ):ℤ) := by
      rw [Nat.cast_mul,Nat.cast_sub hdcomp,Nat.cast_pow,Nat.cast_pow,hcJm,hcJp]
      exact hfactor
    exact_mod_cast he
  · exact_mod_cast (show (Jm.natAbs:ℤ) ≤ (N:ℤ)^2 by simpa only [hcJm] using hJmBd)
  · exact_mod_cast (show (Jp.natAbs:ℤ) ≤ (N:ℤ)^2 by simpa only [hcJp] using hJpBd)
  · exact_mod_cast (show (G.natAbs:ℤ)^2 ≤ (N:ℤ)*(c.S.natAbs:ℤ) by simpa only [hcG,hcS] using hGbd)
  · exact_mod_cast (show (c.S.natAbs:ℤ) ≤ (N:ℤ)*(K.natAbs:ℤ)^2 by simpa only [hcK,hcS] using hKbd)

end Circle
end RudinABC
