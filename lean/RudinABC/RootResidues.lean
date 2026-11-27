import RudinABC.Statements
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The prime-power root count and the Chinese remainder theorem (preprint §6) -/

namespace RudinABC

private theorem int_two_not_dvd_of_odd_nat_prime {p : ℕ} (hp : p.Prime)
    (hp2 : p≠2) : ¬(p:ℤ) ∣ 2 := by
  intro h
  have h' : p∣2 := Int.natCast_dvd_natCast.1 h
  rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1|h2
  · exact hp.ne_one h1
  · exact hp2 h2

/-- At an odd prime power, a unit root must be one of the two signs
of any fixed root. -/
theorem odd_prime_power_sign {p k : ℕ} (hp : p.Prime) (hp2 : p≠2)
    (x r : ℤ) (hr : ¬(p:ℤ)∣r) (h : (p:ℤ)^k ∣ x^2-r^2) :
    (p:ℤ)^k ∣ x-r ∨ (p:ℤ)^k ∣ x+r := by
  have hπ := Nat.prime_iff_prime_int.1 hp
  have hprod : (p:ℤ)^k ∣ (x-r)*(x+r) := by
    rwa [show (x-r)*(x+r)=x^2-r^2 by ring]
  by_cases hd : (p:ℤ)∣x-r
  · have hnd : ¬(p:ℤ)∣x+r := by
      intro hh
      have h2r : (p:ℤ)∣2*r := by
        simpa [show 2*r=(x+r)-(x-r) by ring] using dvd_sub hh hd
      exact (hπ.dvd_or_dvd h2r).elim (int_two_not_dvd_of_odd_nat_prime hp hp2) hr
    exact Or.inl (hπ.pow_dvd_of_dvd_mul_right k hnd hprod)
  · exact Or.inr (hπ.pow_dvd_of_dvd_mul_left k hd hprod)

/-- At modulus (2^{k+1}), the two products split so that one of
the signed differences is divisible by (2^k). -/
theorem two_power_sign {k : ℕ} (x r : ℤ) (hr : ¬(2:ℤ)∣r)
    (h : (2:ℤ)^(k+1)∣x^2-r^2) :
    (2:ℤ)^k∣x-r ∨ (2:ℤ)^k∣x+r := by
  have hr1 : r%2=1 := by
    have hh : ¬r%2=0 := fun h => hr (Int.dvd_iff_emod_eq_zero.mpr h)
    omega
  have hdiff : (2:ℤ)∣x^2-r^2 :=
    (dvd_pow_self _ (Nat.succ_ne_zero k)).trans h
  have hx1 : x%2=1 := by
    by_contra! hx
    have he : (2:ℤ)∣x := Int.dvd_iff_emod_eq_zero.2 (by omega)
    have hxsq := he.trans (dvd_pow_self x (by decide : (2:ℕ)≠0))
    have hrsq : (2:ℤ)∣r^2 := by
      have hh := dvd_sub hxsq hdiff
      rwa [show x^2-(x^2-r^2)=r^2 by ring] at hh
    exact hr (Int.prime_two.dvd_of_dvd_pow hrsq)
  have hmin : (2:ℤ)∣x-r := Int.dvd_iff_emod_eq_zero.2 (by omega)
  have hplu : (2:ℤ)∣x+r := Int.dvd_iff_emod_eq_zero.2 (by omega)
  have hprod : (2:ℤ)^(k+1)∣(x-r)*(x+r) := by
    rwa [show (x-r)*(x+r)=x^2-r^2 by ring]
  by_cases h4 : ((4:ℤ) ∣ x-r)
  · have h4' : ¬(4:ℤ)∣x+r := by
      intro h4p
      have ha : (2:ℤ)*2∣2*r := by
        change (4:ℤ)∣2*r
        rw [show 2*r=(x+r)-(x-r) by ring]
        exact dvd_sub h4p h4
      exact hr ((mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0)).1 ha)
    obtain ⟨v,hv⟩ := hplu
    have hv2 : ¬(2:ℤ)∣v := by
      rintro ⟨u,hu⟩
      exact h4' ⟨u,by rw [hv,hu]; ring⟩
    have hcr : (2:ℤ)^k∣(x-r)*v := by
      rw [hv,pow_succ',← mul_assoc,mul_comm (x-r) 2,mul_assoc] at hprod
      exact (mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0)).1 hprod
    exact Or.inl (Int.prime_two.pow_dvd_of_dvd_mul_right k hv2 hcr)
  · obtain ⟨v,hv⟩ := hmin
    have hv2 : ¬(2:ℤ)∣v := by
      rintro ⟨u,hu⟩
      exact h4 ⟨u,by rw [hv,hu]; ring⟩
    have hcr : (2:ℤ)^k∣v*(x+r) := by
      rw [hv,pow_succ',mul_assoc] at hprod
      exact (mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0)).1 hprod
    exact Or.inr (Int.prime_two.pow_dvd_of_dvd_mul_left k hv2 hcr)

noncomputable def residueSet (m : ℕ) [NeZero m] (a : ℤ) : Finset (ZMod m) := by
  classical
  exact Finset.univ.filter fun x => x^2=(a:ZMod m)

theorem mem_residueSet (m : ℕ) [NeZero m] (a : ℤ) (x : ZMod m) :
    x ∈ residueSet m a ↔ x^2=(a:ZMod m) := by
  classical
  simp [residueSet]

noncomputable def residueCount (m : ℕ) (a : ℤ) : ℕ :=
  if h : m=0 then 0 else (@residueSet m ⟨h⟩ a).card

theorem residueCount_eq (m : ℕ) [NeZero m] (a : ℤ) :
    residueCount m a = (residueSet m a).card := by
  simp [residueCount,NeZero.ne m]

private theorem cast_val_int {m : ℕ} [NeZero m] (z : ZMod m) :
    ((z.val:ℤ):ZMod m)=z := by rw [Int.cast_natCast,ZMod.natCast_zmod_val]

private theorem root_integer_diff {m : ℕ} [NeZero m] {x r : ZMod m} {a : ℤ}
    (hx : x∈residueSet m a) (hr : r∈residueSet m a) :
    (m:ℤ)∣(x.val:ℤ)^2-(r.val:ℤ)^2 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  rw [Int.cast_sub,Int.cast_pow,Int.cast_pow,cast_val_int,cast_val_int,
    (mem_residueSet _ _ _).1 hx,(mem_residueSet _ _ _).1 hr,sub_self]

private theorem reference_not_divisible {p k : ℕ} [NeZero (p^k)] {r : ZMod (p^k)} {a : ℤ}
    (hk : k≠0) (ha : ¬(p:ℤ)∣a) (hr : r∈residueSet (p^k) a) :
    ¬(p:ℤ)∣(r.val:ℤ) := by
  intro hd
  apply ha
  have heq : (((r.val:ℤ)^2 : ℤ):ZMod (p^k)) = (a:ZMod (p^k)) := by
    rw [Int.cast_pow,cast_val_int]
    exact (mem_residueSet _ _ _).1 hr
  have hdiff := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 heq
  rw [Nat.cast_pow] at hdiff
  have hp : (p:ℤ)∣a-(r.val:ℤ)^2 := (dvd_pow_self _ hk).trans hdiff
  have hsq : (p:ℤ)∣(r.val:ℤ)^2 := hd.trans (dvd_pow_self _ (by decide : (2:ℕ)≠0))
  simpa using dvd_add hp hsq

/-- The odd-prime-power residue count, including its empty-root case. -/
theorem residueCount_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hp2 : p≠2)
    (hk : k≠0) (a : ℤ) (ha : ¬(p:ℤ)∣a) :
    residueCount (p^k) a ≤ 2 := by
  classical
  let _ : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [residueCount_eq]
  by_cases h : (residueSet (p^k) a).Nonempty
  · obtain ⟨r,hr⟩ := h
    have hr' := reference_not_divisible hk ha hr
    have hsub : residueSet (p^k) a ⊆ {r,-r} := by
      intro x hx
      have hd := root_integer_diff hx hr
      rw [Nat.cast_pow] at hd
      rw [Finset.mem_insert,Finset.mem_singleton]
      rcases odd_prime_power_sign hp hp2 _ _ hr' hd with h | h
      · left
        have hg := (ZMod.intCast_zmod_eq_zero_iff_dvd
          ((x.val:ℤ)-(r.val:ℤ)) (p^k)).2 (by simpa only [Nat.cast_pow] using h)
        rwa [Int.cast_sub,cast_val_int,cast_val_int,sub_eq_zero] at hg
      · right
        have hg := (ZMod.intCast_zmod_eq_zero_iff_dvd
          ((x.val:ℤ)+(r.val:ℤ)) (p^k)).2 (by simpa only [Nat.cast_pow] using h)
        rw [Int.cast_add,cast_val_int,cast_val_int] at hg
        exact eq_neg_of_add_eq_zero_left hg
    exact (Finset.card_le_card hsub).trans (by calc
      _ ≤ ({(-r)} : Finset (ZMod (p^k))).card+1 := Finset.card_insert_le _ _
      _ = _ := by simp)
  · rw [Finset.not_nonempty_iff_eq_empty.1 h]
    simp

private theorem two_lifts (k : ℕ) (x r : ℤ)
    (h : (2:ℤ)^k∣x-r) :
    (x:ZMod (2^(k+1)))=(r:ZMod (2^(k+1))) ∨
    (x:ZMod (2^(k+1)))=(r:ZMod (2^(k+1)))+(2:ZMod (2^(k+1)))^k := by
  obtain ⟨v,hv⟩ := h
  have hmod : (2:ZMod (2^(k+1)))^(k+1)=0 := by
    exact_mod_cast ZMod.natCast_self (2^(k+1))
  have hvdiv : v=2*(v/2)+v%2 := by omega
  have hem : v%2=0 ∨ v%2=1 := by omega
  let R := ZMod (2^(k+1))
  let f := Int.castRingHom R
  have hvc : (x:R)-(r:R)=(2:R)^k*(v:R) := by
    change f x - f r = (2:R)^k*f v
    rw [← map_sub,hv,map_mul,map_pow]
    norm_num [f]
  have hsc : (v:R)=(2:R)*((v/2:ℤ):R)+((v%2:ℤ):R) := by
    change f v = (2:R)*f (v/2)+f (v%2)
    conv_lhs => rw [hvdiv]
    rw [map_add,map_mul]
    norm_num [f]
  have hrzero : (2:R)^k * (2:R) = 0 := by rwa [← pow_succ]
  have hh : (x:R)-(r:R)=(2:R)^k*((v%2:ℤ):R) := by
    rw [hvc,hsc,mul_add,← mul_assoc,hrzero,zero_mul,zero_add]
  rcases hem with he|he
  · left
    rw [he,Int.cast_zero,mul_zero,sub_eq_zero] at hh
    exact hh
  · right
    rw [he,Int.cast_one,mul_one,sub_eq_iff_eq_add] at hh
    simpa [add_comm] using hh

theorem residueCount_two_pow {k : ℕ} (hk : k≠0) (a : ℤ) (ha : ¬(2:ℤ)∣a) :
    residueCount (2^k) a ≤ 4 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  classical
  let _ : NeZero (2^(k+1)) := ⟨by positivity⟩
  rw [residueCount_eq]
  by_cases h : (residueSet (2^(k+1)) a).Nonempty
  · obtain ⟨r,hr⟩ := h
    let d : ZMod (2^(k+1)) := (2:ZMod (2^(k+1)))^k
    have hr' := reference_not_divisible (Nat.succ_ne_zero k) ha hr
    have hsub : residueSet (2^(k+1)) a ⊆ {r,r+d,-r,-r+d} := by
      intro x hx
      have hd := root_integer_diff hx hr
      rw [Nat.cast_pow] at hd
      rcases two_power_sign _ _ hr' hd with h|h
      · have H := two_lifts k (x.val:ℤ) (r.val:ℤ) h
        simp only [cast_val_int] at H
        rcases H with h|h
        · simp [h]
        · simp [h,d]
      · have H := two_lifts k (x.val:ℤ) (-(r.val:ℤ)) (by simpa only [sub_neg_eq_add] using h)
        simp only [Int.cast_neg,cast_val_int] at H
        rcases H with h|h
        · simp [h]
        · simp [h,d]
    apply (Finset.card_le_card hsub).trans
    calc
      _ ≤ (Finset.card {r+d,-r,-r+d})+1 := Finset.card_insert_le _ _
      _ ≤ (Finset.card {-r,-r+d})+1+1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ ≤ (Finset.card {-r+d})+1+1+1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
      _ = _ := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.1 h]
    simp

/-- For coprime moduli, CRT sends a root injectively to a pair of roots. -/
theorem residueCount_mul_le {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (hcop : m.Coprime n) (a : ℤ) :
    residueCount (m*n) a ≤ residueCount m a*residueCount n a := by
  classical
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  let _ : NeZero (m*n) := ⟨(mul_pos hm hn).ne'⟩
  rw [residueCount_eq,residueCount_eq,residueCount_eq,← Finset.card_product]
  let E := ZMod.chineseRemainder hcop
  apply Finset.card_le_card_of_injOn E _ E.injective.injOn
  intro x hx
  have hh := (mem_residueSet _ _ _).1 hx
  have h : (E x)^2 = (a : ZMod m × ZMod n) := by
    rw [← map_pow,hh,map_intCast]
  exact Finset.mem_product.2
    ⟨(mem_residueSet _ _ _).2 (congrArg Prod.fst h),
     (mem_residueSet _ _ _).2 (congrArg Prod.snd h)⟩

private def localRootBound (p : ℕ) : ℕ := 2*(if p=2 then 2 else 1)

private theorem residueCount_one_le (a : ℤ) : residueCount 1 a ≤ 1 := by
  rw [residueCount_eq]
  exact (Finset.card_le_univ _).trans_eq (ZMod.card 1)

private theorem residueCount_prod_primes_le (s : Finset ℕ) (e : ℕ → ℕ) (a : ℤ)
    (hp : ∀ p∈s, p.Prime) (he : ∀ p∈s, e p≠0) (ha : ∀ p∈s, ¬(p:ℤ)∣a) :
    residueCount (∏ p ∈ s, p^(e p)) a ≤ ∏ p ∈ s, localRootBound p := by
  classical
  induction s using Finset.induction with
  | empty => simpa using residueCount_one_le a
  | insert p s hs ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have he' := he p (Finset.mem_insert_self _ _)
    have ha' := ha p (Finset.mem_insert_self _ _)
    have hpr (r : ℕ) (hr : r∈s) : r.Prime := hp r (Finset.mem_insert_of_mem hr)
    have hcop : (p^(e p)).Coprime (∏ r ∈ s, r^(e r)) := by
      apply Nat.Coprime.prod_right
      intro r hr
      exact Nat.coprime_pow_primes _ _ hp' (hpr r hr) (fun h => hs (h ▸ hr))
    have hl : residueCount (p^e p) a ≤ localRootBound p := by
      by_cases h2 : p=2
      · subst p
        simpa [localRootBound] using residueCount_two_pow he' a ha'
      · simpa [localRootBound,h2] using residueCount_odd_prime_pow hp' h2 he' a ha'
    have hs' := ih hpr (fun r hr => he r (Finset.mem_insert_of_mem hr))
      (fun r hr => ha r (Finset.mem_insert_of_mem hr))
    rw [Finset.prod_insert hs,Finset.prod_insert hs]
    exact (residueCount_mul_le (Nat.pow_pos hp'.pos)
      (Finset.prod_pos fun r hr => Nat.pow_pos (hpr r hr).pos) hcop a).trans
      (Nat.mul_le_mul hl hs')

/-- Global root-count factor: two choices per odd prime and at most four
at the only even prime. -/
theorem residueCount_le_two_pow (q : ℕ) (hq : 0<q) (a : ℤ)
    (hc : IsCoprime a (q:ℤ)) :
    residueCount q a ≤ 2*2^q.primeFactors.card := by
  classical
  have hprod : (∏ p ∈ q.primeFactors, p^q.factorization p)=q :=
    (Nat.prod_primeFactors_pow_factorization hq.ne').symm
  have hp (p : ℕ) (hp : p∈q.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he (p : ℕ) (hp : p∈q.primeFactors) : q.factorization p≠0 :=
    Finsupp.mem_support_iff.1 hp
  have ha (p : ℕ) (h : p∈q.primeFactors) : ¬(p:ℤ)∣a := by
    intro hd
    exact (Nat.prime_iff_prime_int.1 (hp p h)).not_isUnit
      (hc.isUnit_of_dvd' hd (Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors h)))
  have hb := residueCount_prod_primes_le q.primeFactors q.factorization a hp he ha
  rw [hprod] at hb
  apply hb.trans
  unfold localRootBound
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  have hs : (∏ p ∈ q.primeFactors, if p=2 then (2:ℕ) else 1) ≤ 2 := by
    rw [Finset.prod_ite_eq' q.primeFactors 2 (fun _ => (2:ℕ))]
    split_ifs <;> decide
  calc
    _ ≤ 2^q.primeFactors.card*2 := Nat.mul_le_mul_left _ hs
    _ = _ := Nat.mul_comm _ _

end RudinABC
