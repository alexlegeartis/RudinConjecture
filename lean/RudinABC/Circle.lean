import RudinABC.Normalize
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Prod

/-! # Colliding index sums yield five representations (preprint §2, eq. (2)) -/

namespace RudinABC

/-- Square-term indices with the zero term removed. -/
noncomputable def positiveSquareIndices (N : ℕ) (q a : ℤ) : Finset ℕ :=
  (squareIndices N q a).filter fun n => 0 < q*(n:ℤ)+a

theorem mem_positiveSquareIndices (N n : ℕ) (q a : ℤ) :
    n ∈ positiveSquareIndices N q a ↔
      (n < N ∧ IsSquare (q*(n:ℤ)+a)) ∧ 0 < q*(n:ℤ)+a := by
  simp [positiveSquareIndices, mem_squareIndices]

theorem QZ_le_positive_add_one (N : ℕ) (q a : ℤ) (hq : q ≠ 0) :
    QZ N q a ≤ (positiveSquareIndices N q a).card + 1 := by
  classical
  have hsub : positiveSquareIndices N q a ⊆ squareIndices N q a := Finset.filter_subset _ _
  let T := squareIndices N q a \ positiveSquareIndices N q a
  have ht : ∀ n ∈ T, q*(n:ℤ)+a = 0 := by
    intro n hn
    obtain ⟨hsq, hnP⟩ := Finset.mem_sdiff.mp hn
    have hm := (mem_squareIndices _ _ _ _).mp hsq
    have hnp : ¬ 0 < q*(n:ℤ)+a := fun hc =>
      hnP ((mem_positiveSquareIndices _ _ _ _).2 ⟨hm,hc⟩)
    obtain ⟨r,hr⟩ := hm.2
    exact le_antisymm (le_of_not_gt hnp) (hr.symm ▸ mul_self_nonneg r)
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    have hmul : q*(i:ℤ) = q*(j:ℤ) := by linarith [ht _ hi, ht _ hj]
    exact_mod_cast mul_left_cancel₀ hq hmul
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  unfold QZ
  change T.card + _ = _ at hsum
  omega

/-- Index and root data for precisely five unequal pairs with the same sum.
The lower indices are ordered increasingly, so the differences decrease. -/
structure Circle (N : ℕ) (q a : ℤ) where
  t : ℕ
  lo : Fin 5 → ℕ
  hi : Fin 5 → ℕ
  x : Fin 5 → ℤ
  y : Fin 5 → ℤ
  d : Fin 5 → ℕ
  indexSum : ∀ i, lo i + hi i = t
  indexOrder : ∀ i, lo i < hi i
  indexMax : ∀ i, hi i < N
  xPos : ∀ i, 0 < x i
  yPos : ∀ i, 0 < y i
  xSquare : ∀ i, x i ^ 2 = q*(hi i:ℤ)+a
  ySquare : ∀ i, y i ^ 2 = q*(lo i:ℤ)+a
  dDef : ∀ i, d i = hi i - lo i
  decreasing : StrictAnti d

namespace Circle

variable {N : ℕ} {q a : ℤ}

def S (c : Circle N q a) : ℤ := 2*a + q*(c.t:ℤ)

theorem dPos (c : Circle N q a) (i : Fin 5) : 0 < c.d i := by
  rw [c.dDef]
  exact Nat.sub_pos_of_lt (c.indexOrder i)

theorem dLt (c : Circle N q a) (i : Fin 5) : c.d i < N := by
  rw [c.dDef]
  exact (Nat.sub_le _ _).trans_lt (c.indexMax i)

theorem norm_eq (c : Circle N q a) (i : Fin 5) : c.x i^2+c.y i^2 = c.S := by
  have h : (c.lo i:ℤ)+(c.hi i:ℤ) = c.t := by exact_mod_cast c.indexSum i
  rw [c.xSquare, c.ySquare, S, ← h]
  ring

theorem SPos (c : Circle N q a) : 0 < c.S := by
  rw [← c.norm_eq 0]
  exact add_pos_of_pos_of_nonneg (pow_pos (c.xPos 0) _) (sq_nonneg _)

theorem diff_eq (c : Circle N q a) (i : Fin 5) :
    c.x i^2-c.y i^2 = q*(c.d i:ℤ) := by
  rw [c.xSquare, c.ySquare, c.dDef, Nat.cast_sub (c.indexOrder i).le]
  ring

theorem yLtX (c : Circle N q a) (hq : 0 < q) (i : Fin 5) : c.y i < c.x i := by
  have hpos : 0 < q*(c.d i:ℤ) := mul_pos hq (by exact_mod_cast c.dPos i)
  have hh := c.diff_eq i
  by_contra! he
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (add_nonneg (c.xPos i).le (c.yPos i).le)]

theorem dParity (c : Circle N q a) (i : Fin 5) : Int.ModEq 2 (c.d i:ℤ) (c.t:ℤ) := by
  apply Int.modEq_iff_dvd.2
  refine ⟨(c.lo i:ℤ), ?_⟩
  have ht : (c.lo i:ℤ)+(c.hi i:ℤ) = c.t := by exact_mod_cast c.indexSum i
  rw [c.dDef, Nat.cast_sub (c.indexOrder i).le, ← ht]
  ring

/-- On the primitive progression the common norm and q share only a
possible factor 2. -/
theorem gcd_dvd_two (c : Circle N q a) (h : IsCoprime a q) :
    ((Int.gcd q c.S : ℕ):ℤ) ∣ 2 := by
  obtain ⟨r,s,hrs⟩ := h
  have hb : 2 = r*c.S + (2*s-r*(c.t:ℤ))*q := by unfold S; linear_combination -2*hrs
  rw [hb]
  exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_right ..) _)
    (dvd_mul_of_dvd_right (Int.gcd_dvd_left ..) _)

end Circle

private theorem exists_pos_root {z : ℤ} (hp : 0 < z) (hs : IsSquare z) :
    ∃ x : ℤ, 0 < x ∧ x^2=z := by
  obtain ⟨r,hr⟩ := hs
  use |r|
  have hr0 : r ≠ 0 := by intro he; simp [he] at hr; omega
  exact ⟨abs_pos.2 hr0, by simpa [sq_abs,pow_two] using hr.symm⟩

/-- If there are more than (5\sqrt{N}) positive squares (encoded without
square roots as (25N<m²)), some index sum has at least five pairs. -/
theorem exists_circle (N : ℕ) (q a : ℤ)
    (hbig : 25*N < (positiveSquareIndices N q a).card^2) :
    Nonempty (Circle N q a) := by
  classical
  let F := positiveSquareIndices N q a
  let P := F.product F |>.filter fun ij => ij.1 < ij.2
  have hF : F.card ≤ N := (Finset.card_le_card (Finset.filter_subset _ _)).trans (QZ_le_length _ _ _)
  have hP : P.card = F.card.choose 2 := Finset.card_product_filter_lt
  have hple : 4*(2*N) < P.card := by
    rw [hP,Nat.choose_two_right]
    apply Nat.lt_iff_add_one_le.mpr
    rw [Nat.le_div_iff_mul_le (by decide)]
    rw [Nat.mul_sub_left_distrib, mul_one]
    change 25*N < F.card^2 at hbig
    rw [pow_two] at hbig
    have hN : 1 ≤ N := by
      by_contra! hh
      have hf : F.card = 0 := by omega
      simp [hf] at hbig
    apply Nat.le_sub_of_add_le
    omega
  have hmaps (ij : ℕ × ℕ) (hij : ij ∈ P) : ij.1+ij.2 ∈ Finset.range (2*N) := by
    have hm := Finset.mem_product.1 (Finset.mem_filter.1 hij).1
    have h1 := ((mem_positiveSquareIndices _ _ _ _).1 hm.1).1.1
    have h2 := ((mem_positiveSquareIndices _ _ _ _).1 hm.2).1.1
    exact Finset.mem_range.2 (by omega)
  have hple' : (Finset.range (2*N)).card * 4 < P.card := by
    simpa only [Finset.card_range, Nat.mul_comm (2*N) 4] using hple
  obtain ⟨t, _, ht⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hple'
  let B := P.filter fun ij => ij.1+ij.2=t
  have hBinj : (B : Set (ℕ × ℕ)).InjOn Prod.fst := by
    intro u hu v hv he
    have hu' := (Finset.mem_filter.1 hu).2
    have hv' := (Finset.mem_filter.1 hv).2
    exact Prod.ext he (by omega)
  let L := B.image Prod.fst
  have hbL : B.card = L.card := (Finset.card_image_of_injOn hBinj).symm
  have h5L : 5 ≤ L.card := by change 4 < B.card at ht; omega
  obtain ⟨U,hU,hUc⟩ := Finset.exists_subset_card_eq h5L
  let lo := U.orderEmbOfFin hUc
  have H (i : Fin 5) : ∃ j : ℕ, (lo i,j) ∈ B := by
    have hm : lo i ∈ L := hU (Finset.orderEmbOfFin_mem U hUc i)
    obtain ⟨⟨u,v⟩, hB, he⟩ := Finset.mem_image.1 hm
    change u = lo i at he
    exact ⟨v, he ▸ hB⟩
  choose hi hB using H
  have Hsum (i : Fin 5) : lo i + hi i = t := (Finset.mem_filter.1 (hB i)).2
  have Hlt (i : Fin 5) : lo i < hi i := (Finset.mem_filter.1 (Finset.mem_filter.1 (hB i)).1).2
  have Hpos (i : Fin 5) := Finset.mem_product.1
    (Finset.mem_filter.1 (Finset.mem_filter.1 (hB i)).1).1
  have Hlo (i : Fin 5) := (mem_positiveSquareIndices _ _ _ _).1 (Hpos i).1
  have Hhi (i : Fin 5) := (mem_positiveSquareIndices _ _ _ _).1 (Hpos i).2
  choose x hx using fun i => exists_pos_root (Hhi i).2 (Hhi i).1.2
  choose y hy using fun i => exists_pos_root (Hlo i).2 (Hlo i).1.2
  refine ⟨⟨t,lo,hi,x,y,fun i => hi i-lo i,Hsum,Hlt,fun i => (Hhi i).1.1,
    fun i => (hx i).1,fun i => (hy i).1,fun i => (hx i).2,
    fun i => (hy i).2,fun _ => rfl,?_⟩⟩
  intro i j hij
  have hlt : lo i < lo j := lo.strictMono hij
  have hi' := Hlt i
  have hj' := Hlt j
  have hi'' := Hsum i
  have hj'' := Hsum j
  change hi j-lo j < hi i-lo i
  omega

end RudinABC
