import RudinABC.Circle
import RudinABC.RootResidues

/-! # Count roots in a short interval within allowed residue classes -/

namespace RudinABC

private theorem intSquare_as_nat {z : ℤ} (h : IsSquare z) : ∃ r : ℕ, (r:ℤ)^2=z := by
  obtain ⟨x,hx⟩ := h
  refine ⟨x.natAbs,?_⟩
  rw [Int.natCast_natAbs,sq_abs,pow_two,hx]

/-- For a progression with positive difference, square roots are injective
and lie in an interval of length at most `sqrt(q*N)`. The CRT factor is
still a variable here, so this is the exact general counting mechanism. -/
theorem positive_count_residue_interval (N : ℕ) (q a : ℤ) (hq : 0<q) :
    ((positiveSquareIndices N q a).card:ℝ) ≤
      (residueCount q.natAbs a:ℝ)*(1+Real.sqrt ((N:ℝ)/(q.natAbs:ℝ))) := by
  classical
  let I := positiveSquareIndices N q a
  let t := q.natAbs
  have ht : 0<t := Int.natAbs_pos.2 hq.ne'
  have htR : 0<(t:ℝ) := by exact_mod_cast ht
  have hqeq : (t:ℤ)=q := Int.natAbs_of_nonneg hq.le
  let _ : NeZero t := ⟨ht.ne'⟩
  have H (i : {i : ℕ // i∈I}) : ∃ r : ℕ, (r:ℤ)^2=q*(i.1:ℤ)+a :=
    intSquare_as_nat ((mem_positiveSquareIndices _ _ _ _).1 i.2).1.2
  let rt := fun i => Classical.choose (H i)
  have rt_sq (i : {i : ℕ // i∈I}) : (rt i:ℤ)^2=q*(i.1:ℤ)+a :=
    Classical.choose_spec (H i)
  have h_inj : Function.Injective rt := by
    intro i j he
    have hi := rt_sq i
    rw [he,rt_sq j] at hi
    have hh : q*(i.1:ℤ)=q*(j.1:ℤ) := by linarith
    apply Subtype.ext
    exact_mod_cast mul_left_cancel₀ hq.ne' hh
  let S := I.attach.image rt
  have hcard : S.card=I.card := by simp [S,Finset.card_image_of_injective _ h_inj]
  by_cases hS : S.Nonempty
  · let L := S.min' hS
    let R := S.max' hS
    let D := R-L
    have hLS : L∈S := Finset.min'_mem _ _
    have hRS : R∈S := Finset.max'_mem _ _
    have hLR : L≤R := Finset.min'_le _ _ hRS
    have hl (r : ℕ) (hr : r∈S) : L≤r := Finset.min'_le _ _ hr
    have hu (r : ℕ) (hr : r∈S) : r≤R := Finset.le_max' _ _ hr
    obtain ⟨i,_,hi⟩ := Finset.mem_image.1 hLS
    obtain ⟨j,_,hj⟩ := Finset.mem_image.1 hRS
    have hLsq : (L:ℤ)^2=q*(i.1:ℤ)+a := by rw [← hi,rt_sq]
    have hRsq : (R:ℤ)^2=q*(j.1:ℤ)+a := by rw [← hj,rt_sq]
    have hNnat := ((mem_positiveSquareIndices _ _ _ _).1 j.2).1.1
    have hDb : D^2≤t*N := by
      have hN : (j.1:ℤ) - (i.1:ℤ) ≤ N := by
        have h' : (j.1:ℤ) < N := by exact_mod_cast hNnat
        omega
      have he : (R:ℤ)^2-(L:ℤ)^2 = q*((j.1:ℤ)-(i.1:ℤ)) := by rw [hRsq,hLsq]; ring
      have he₂ := mul_le_mul_of_nonneg_left hN hq.le
      rw [← he] at he₂
      have hLRi : (L:ℤ)≤R := by exact_mod_cast hLR
      have hD₂ : ((D:ℕ):ℤ)^2 ≤ (R:ℤ)^2-(L:ℤ)^2 := by
        rw [show D=R-L by rfl,Nat.cast_sub hLR]
        nlinarith [mul_nonneg (sub_nonneg.2 hLRi) (show 0≤(L:ℤ) by positivity)]
      have hT : ((D:ℕ):ℤ)^2 ≤ (t:ℤ)*(N:ℤ) := by rw [hqeq]; exact hD₂.trans he₂
      exact_mod_cast hT
    let mapRoot (r : ℕ) : ZMod t × ℕ := ((r:ZMod t),(r-L)/t)
    have card_bd : S.card≤(residueSet t a).card*(D/t+1) := by
      have hg : S.card ≤ ((residueSet t a).product (Finset.range (D/t+1))).card := by
        apply Finset.card_le_card_of_injOn mapRoot
        · intro r hr
          obtain ⟨u,_,hrU⟩ := Finset.mem_image.1 hr
          have hsu : (r:ℤ)^2=q*(u.1:ℤ)+a := by rw [← hrU,rt_sq]
          have hsz := congrArg (fun z : ℤ => (z:ZMod t)) hsu
          simp only [Int.cast_pow,Int.cast_add,Int.cast_mul,Int.cast_natCast] at hsz
          have hq0 : (q:ZMod t)=0 := by rw [← hqeq,Int.cast_natCast,ZMod.natCast_self]
          rw [hq0,zero_mul,zero_add] at hsz
          have hD' : r-L≤D := Nat.sub_le_sub_right (hu r hr) _
          exact Finset.mem_product.2 ⟨(mem_residueSet _ _ _).2 hsz,
            Finset.mem_range.2 (Nat.lt_succ_iff.2 (Nat.div_le_div_right hD'))⟩
        · intro r hr s hs he
          have hfst : (r:ZMod t)=(s:ZMod t) := congrArg Prod.fst he
          have hsnd : (r-L)/t=(s-L)/t := congrArg Prod.snd he
          have hcast := congrArg (fun z : ZMod t => z-(L:ZMod t)) hfst
          rw [← Nat.cast_sub (hl r hr),← Nat.cast_sub (hl s hs)] at hcast
          have hmod := (ZMod.natCast_eq_natCast_iff' (r-L) (s-L) t).1 hcast
          have hrR := Nat.mod_add_div (r-L) t
          have hsR := Nat.mod_add_div (s-L) t
          rw [hmod,hsnd,hsR] at hrR
          have hrl := hl r hr
          have hsl := hl s hs
          omega
      simpa [Finset.card_product] using hg
    have hquot : ((D/t:ℕ):ℝ) ≤ Real.sqrt ((N:ℝ)/(t:ℝ)) := by
      have hdiv : ((D/t:ℕ):ℝ) ≤ (D:ℝ)/(t:ℝ) := by
        apply (le_div_iff₀ htR).2
        exact_mod_cast Nat.div_mul_le_self D t
      apply hdiv.trans
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      rw [div_pow]
      apply (div_le_iff₀ (by positivity : 0<(t:ℝ)^2)).2
      have hdReal : (D:ℝ)^2 ≤ (t:ℝ)*(N:ℝ) := by exact_mod_cast hDb
      calc
        _ ≤ (t:ℝ)*(N:ℝ) := hdReal
        _ = (N:ℝ)/(t:ℝ)*(t:ℝ)^2 := by field_simp
    have hC : (I.card:ℝ) ≤ ((residueSet t a).card:ℝ)*(((D/t:ℕ):ℝ)+1) := by
      rw [← hcard]
      exact_mod_cast card_bd
    rw [← residueCount_eq] at hC
    change (I.card:ℝ) ≤ (residueCount t a:ℝ)*(1+Real.sqrt ((N:ℝ)/(t:ℝ)))
    apply hC.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.1 hS
    rw [hz,Finset.card_empty] at hcard
    change (I.card:ℝ) ≤ _
    rw [← hcard, Nat.cast_zero]
    positivity

end RudinABC
