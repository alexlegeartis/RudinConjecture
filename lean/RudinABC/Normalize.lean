import RudinABC.Statements
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Exact normalization of all signed integer progressions (preprint §2) -/

namespace RudinABC

/-- Reversal on the length-`N` window; valid also when `N=0`. -/
theorem reverse_QZ (N : ℕ) (q a : ℤ) :
    QZ N (-q) (a + q*((N:ℤ)-1)) = QZ N q a := by
  classical
  unfold QZ
  let r := fun n : ℕ => N-1-n
  have hlt (n : ℕ) (hn : n < N) : r n < N := by dsimp [r]; omega
  have hrt (n : ℕ) (hn : n < N) : ((r n : ℕ) : ℤ) = (N:ℤ)-1-(n:ℤ) := by
    dsimp [r]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  have hii (n : ℕ) (hn : n < N) : r (r n) = n := by dsimp [r]; omega
  refine Finset.card_bij' (fun n _ => r n) (fun n _ => r n) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_squareIndices] at hn ⊢
    refine ⟨hlt n hn.1, ?_⟩
    rw [hrt n hn.1, show q*((N:ℤ)-1-(n:ℤ))+a = (-q)*(n:ℤ)+(a+q*((N:ℤ)-1)) by ring]
    exact hn.2
  · intro n hn
    rw [mem_squareIndices] at hn ⊢
    refine ⟨hlt n hn.1, ?_⟩
    rw [hrt n hn.1, show (-q)*((N:ℤ)-1-(n:ℤ))+(a+q*((N:ℤ)-1)) = q*(n:ℤ)+a by ring]
    exact hn.2
  · intro n hn
    exact hii n ((mem_squareIndices _ _ _ _).1 hn).1
  · intro n hn
    exact hii n ((mem_squareIndices _ _ _ _).1 hn).1

/-- When `b² g u` is a square and `g` is squarefree, its root is a multiple
of `b g` and `u = g v²`. Conversely this condition gives a square. -/
theorem isSquare_sq_mul_squarefree_iff {b g : ℕ} (hb : 0 < b)
    (hg : Squarefree g) (u : ℤ) :
    IsSquare ((b : ℤ)^2*(g : ℤ)*u) ↔ ∃ v : ℤ, u = (g : ℤ)*v^2 := by
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne_zero
  constructor
  · rintro ⟨x,hx⟩
    have hbd : (b:ℤ)^2 ∣ x^2 := by refine ⟨(g:ℤ)*u, ?_⟩; simpa only [pow_two, mul_assoc] using hx.symm
    obtain ⟨y,hy⟩ := (Int.pow_dvd_pow_iff (by decide : (2:ℕ) ≠ 0)).mp hbd
    have hu : (g:ℤ)*u = y^2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hb0)
      calc
        _ = x*x := by simpa only [mul_assoc] using hx
        _ = _ := by rw [hy]; ring
    have hgd : g ∣ y.natAbs^2 := by
      have hh : (g:ℤ) ∣ y^2 := ⟨u, hu.symm⟩
      simpa only [Int.natAbs_pow] using Int.natCast_dvd.1 hh
    obtain ⟨v,hv⟩ := Int.natCast_dvd.2 ((hg.dvd_pow_iff_dvd (by decide : (2:ℕ) ≠ 0)).mp hgd)
    refine ⟨v, mul_left_cancel₀ hg0 ?_⟩
    rw [hu, hv]
    ring
  · rintro ⟨v,hv⟩
    exact ⟨(b:ℤ)*(g:ℤ)*v, by rw [hv]; ring⟩

/-- Removes the gcd by restricting to the exact residue class of square
indices and then dividing all terms by `(b g)²`. The number of terms can
decrease, but the number of squares is unchanged. -/
theorem normalize_positive (N : ℕ) (q a : ℤ) (hq : 0 < q)
    (hne : (squareIndices N q a).Nonempty) :
    ∃ L : ℕ, ∃ Q A₀ : ℤ, L ≤ N ∧ 0 < Q ∧ IsCoprime A₀ Q ∧ QZ N q a = QZ L Q A₀ := by
  classical
  have hG : 0 < Int.gcd a q := by
    apply Nat.pos_of_ne_zero
    intro he
    exact hq.ne (Int.gcd_eq_zero_iff.mp he).2.symm
  obtain ⟨A,Q,hcop,ha,hqeq⟩ := Int.exists_gcd_one hG
  have hcop' := Int.isCoprime_iff_gcd_eq_one.2 hcop
  obtain ⟨g,b,hg,hb,hGb,hgSq⟩ := Nat.sq_mul_squarefree_of_pos hG
  have hGc : (Int.gcd a q : ℤ) = (b:ℤ)^2*(g:ℤ) := by exact_mod_cast hGb.symm
  have hQ : 0 < Q := by
    rw [hqeq] at hq
    have hp : 0 < (Int.gcd a q : ℤ) := by exact_mod_cast hG
    exact ((mul_pos_iff.mp hq).resolve_right (fun h => (not_lt_of_ge hp.le) h.2)).1
  obtain ⟨n₁,hn₁⟩ := hne
  rw [mem_squareIndices] at hn₁
  have hsq (n : ℕ) :
      IsSquare (q*(n:ℤ)+a) ↔ ∃ v : ℤ, A+Q*(n:ℤ) = (g:ℤ)*v^2 := by
    have ha' : a = A*((b:ℤ)^2*(g:ℤ)) := ha.trans (congrArg (fun h : ℤ => A*h) hGc)
    have hq' : q = Q*((b:ℤ)^2*(g:ℤ)) := hqeq.trans (congrArg (fun h : ℤ => Q*h) hGc)
    rw [show q*(n:ℤ)+a = (b:ℤ)^2*(g:ℤ)*(A+Q*(n:ℤ)) by rw [ha',hq']; ring]
    exact isSquare_sq_mul_squarefree_iff hb hgSq _
  obtain ⟨v₁,hv₁⟩ := (hsq n₁).1 hn₁.2
  let n₀ := n₁ % g
  let A₀ : ℤ := v₁^2 - Q*((n₁/g:ℕ):ℤ)
  have hn₀ : n₀ < N := (Nat.mod_le _ _).trans_lt hn₁.1
  have hm₀ : n₀ < g := Nat.mod_lt _ hg
  have hdec (n : ℕ) : n % g + g*(n/g) = n := Nat.mod_add_div n g
  have hbase : A+Q*(n₀:ℤ) = (g:ℤ)*A₀ := by
    have hh : ((n₀:ℕ):ℤ) + (g:ℤ)*((n₁/g:ℕ):ℤ) = (n₁:ℤ) := by exact_mod_cast (hdec n₁)
    unfold A₀
    calc
      _ = A+Q*(n₁:ℤ)-Q*(g:ℤ)*((n₁/g:ℕ):ℤ) := by rw [← hh]; ring
      _ = _ := by rw [hv₁]; ring
  obtain ⟨r,s,hrs⟩ := hcop'
  have h₀cop : IsCoprime A₀ Q := by
    refine ⟨r*(g:ℤ), s-r*(n₀:ℤ), ?_⟩
    calc
      _ = r*((g:ℤ)*A₀) + (s-r*(n₀:ℤ))*Q := by ring
      _ = 1 := by rw [← hbase]; linear_combination hrs
  have hgQ : IsCoprime (g:ℤ) Q := by
    refine ⟨r*A₀, s-r*(n₀:ℤ), ?_⟩
    calc
      _ = r*((g:ℤ)*A₀) + (s-r*(n₀:ℤ))*Q := by ring
      _ = 1 := by rw [← hbase]; linear_combination hrs
  let L := (N-1-n₀)/g+1
  have hL : L ≤ N := by
    have h := Nat.div_le_self (N-1-n₀) g
    dsimp [L]
    omega
  have hlen (k : ℕ) : k < L ↔ n₀+g*k < N := by
    dsimp [L]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hg]
    rw [Nat.mul_comm k g]
    omega
  have hpoly (k : ℕ) :
      A+Q*((n₀+g*k:ℕ):ℤ) = (g:ℤ)*(Q*(k:ℤ)+A₀) := by
    push_cast
    calc
      _ = (A+Q*(n₀:ℤ)) + Q*(g:ℤ)*(k:ℤ) := by ring
      _ = _ := by rw [hbase]; ring
  have hg0 : (g:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have hsq_map (k : ℕ) : IsSquare (q*((n₀+g*k:ℕ):ℤ)+a) ↔ IsSquare (Q*(k:ℤ)+A₀) := by
    rw [hsq,hpoly]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v, by simpa [pow_two] using (mul_left_cancel₀ hg0 hv)⟩
    · rintro ⟨v,hv⟩
      exact ⟨v, by rw [hv,pow_two]⟩
  refine ⟨L,Q,A₀,hL,hQ,h₀cop,?_⟩
  unfold QZ
  symm
  refine Finset.card_bij (fun k _ => n₀+g*k) ?_ ?_ ?_
  · intro k hk
    rw [mem_squareIndices] at hk ⊢
    exact ⟨(hlen k).1 hk.1,(hsq_map k).2 hk.2⟩
  · intro k₁ _ k₂ _ he
    exact Nat.eq_of_mul_eq_mul_left hg (Nat.add_left_cancel he)
  · intro n hn
    have hnorig := (mem_squareIndices _ _ _ _).1 hn
    obtain ⟨v,hv⟩ := (hsq n).1 hnorig.2
    have hdn : (g:ℤ) ∣ Q*((n:ℤ)-(n₀:ℤ)) := by
      refine ⟨v^2-A₀, ?_⟩
      calc
        _ = (A+Q*(n:ℤ)) - (A+Q*(n₀:ℤ)) := by ring
        _ = _ := by rw [hv,hbase]; ring
    have hemod := (Int.modEq_iff_dvd.2 (hgQ.dvd_of_dvd_mul_left hdn)).eq
    have hmod : n % g = n₀ := by
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hm₀), ← Int.natCast_mod] at hemod
      exact_mod_cast hemod.symm
    have hr : n₀+g*(n/g) = n := by rw [← hmod, hdec]
    have hnlen : n₀+g*(n/g) < N := by simpa only [hr] using hnorig.1
    refine ⟨n/g, (mem_squareIndices _ _ _ _).2 ⟨(hlen _).2 hnlen, ?_⟩, hr⟩
    apply (hsq_map _).1
    simpa only [hr] using hnorig.2

end RudinABC
