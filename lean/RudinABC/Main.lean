import RudinABC.CutSpecialization
import RudinABC.DivisorBound

/-! # Rudin's original conjecture from the classical abc conjecture

This is the argument of the preprint, fixed at epsilon (1/4).
It proves the uniform bound for all integer differences other than zero.
-/

namespace RudinABC

open Filter Asymptotics

/-- Preprint Theorem 1 at `ε=1/4`: the uniform all-integer bound. -/
theorem uniformIntegerRudin_of_abcAtQuarter (h : abcAtQuarter) : UniformIntegerRudin := by
  obtain ⟨K,hK,hABC⟩ := h
  let A := K^30
  obtain ⟨B,hB⟩ : ∃ B : ℕ, B = 16215 := ⟨_,rfl⟩
  obtain ⟨G,hG⟩ : ∃ G : ℕ, growthConstant A B = G := ⟨_,rfl⟩
  let C : ℝ := 70+4*(G:ℝ)
  have hA : 0<A := Nat.pow_pos hK
  have hC : 0<C := by dsimp [C]; positivity
  have primitive (N : ℕ) (q a : ℤ) (hq : 0<q) (hc : IsCoprime a q) :
      (QZ N q a:ℝ) ≤ C*Real.sqrt (N:ℝ) := by
    by_cases hN : N=0
    · subst N
      simp [QZ,squareIndices]
    · have hNpos : 0<N := Nat.pos_of_ne_zero hN
      have hSR : 1≤Real.sqrt (N:ℝ) :=
        (Real.le_sqrt (by norm_num) (by positivity)).2 (by
          norm_num
          exact_mod_cast hNpos)
      let m := (positiveSquareIndices N q a).card
      have hQ := QZ_le_positive_add_one N q a hq.ne'
      have hQR : (QZ N q a:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hQ
      by_cases hbig : 25*N<m^2
      · obtain ⟨circle⟩ := exists_circle N q a hbig
        have hpoly : q.natAbs≤A*N^B := by
          rw [hB]
          exact circle.q_polynomial hq hc K hK hABC
        have hcount := positive_count_of_polynomial A B N q a hA hNpos hq hc hpoly
        rw [hG] at hcount
        change (m:ℝ) ≤ _ at hcount
        unfold C
        nlinarith
      · have hsmall : (m:ℝ)≤5*Real.sqrt (N:ℝ) := by
          have hn : m^2≤25*N := le_of_not_gt hbig
          apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by positivity)
          rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(N:ℝ)),show (5:ℝ)^2=25 by norm_num]
          exact_mod_cast hn
        have hh : (QZ N q a:ℝ)≤6*Real.sqrt (N:ℝ) := by linarith
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        dsimp [C]
        linarith [Nat.cast_nonneg (α := ℝ) G]
  have positive (N : ℕ) (q a : ℤ) (hq : 0<q) :
      (QZ N q a:ℝ)≤C*Real.sqrt (N:ℝ) := by
    by_cases hn : (squareIndices N q a).Nonempty
    · obtain ⟨L,Q,A₀,hL,hQ,hcop,hcount⟩ := normalize_positive N q a hq hn
      rw [hcount]
      apply (primitive L Q A₀ hQ hcop).trans
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hL)) hC.le
    · have he := Finset.not_nonempty_iff_eq_empty.1 hn
      unfold QZ
      rw [he,Finset.card_empty,Nat.cast_zero]
      exact mul_nonneg hC.le (Real.sqrt_nonneg _)
  refine ⟨C,hC,?_⟩
  intro N q a hq
  rcases lt_or_gt_of_ne hq with hqneg|hqpos
  · rw [← reverse_QZ N q a]
    exact positive _ _ _ (neg_pos.2 hqneg)
  · exact positive _ _ _ hqpos

/-- Uniform all-integer Rudin directly under the classical DeepMind-shaped
finite-exceptions hypothesis. -/
theorem uniformIntegerRudin_of_classicalABC (h : ClassicalABC) : UniformIntegerRudin :=
  uniformIntegerRudin_of_abcAtQuarter (abcAtQuarter_of_classical h)

/-- The exact DeepMind ordinary Rudin Big-O expression for its `Qmax`. -/
theorem rudin_of_classicalABC (h : ClassicalABC) :
    (fun N : ℕ => (Upstream.Qmax N:ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N :=
  Upstream.bigO_of_uniform_integer (uniformIntegerRudin_of_classicalABC h)

end RudinABC
