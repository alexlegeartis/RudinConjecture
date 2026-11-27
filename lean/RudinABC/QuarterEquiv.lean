import RudinABC.ABC

/-! # Equation (1) and its exact fourth-power encoding -/

namespace RudinABC

/-- The paper's real-constant hypothesis at the fixed value ε=1/4. -/
def abcRealQuarter : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ a b c : ℕ,
    0<a → 0<b → 0<c → ({a,b,c} : Set ℕ).Pairwise Nat.Coprime → a+b=c →
    (c:ℝ) ≤ C*(radical (a*b*c):ℝ)^(1+(1/4:ℝ))

private theorem rpow_to_four (x t : ℝ) (hx : 0≤x) :
    (x^t)^4 = x^(t*4) := by
  rw [Real.rpow_mul hx]
  exact (Real.rpow_natCast _ 4).symm

theorem abcAtQuarter_iff_realQuarter : abcAtQuarter ↔ abcRealQuarter := by
  constructor
  · rintro ⟨K,hK,h⟩
    let C := (K:ℝ)^(1/4:ℝ)
    have hkr : 0<(K:ℝ) := by exact_mod_cast hK
    have hcp : 0<C := Real.rpow_pos_of_pos hkr _
    refine ⟨C,hcp,?_⟩
    intro a b c ha hb hc hcop he
    let R : ℝ := radical (a*b*c)
    have hrp : 0<R := by dsimp [R]; exact_mod_cast radical_pos (a*b*c)
    have hlo : (c:ℝ)^4 ≤ (K:ℝ)*R^5 := by
      dsimp [R]
      exact_mod_cast h a b c ha hb hc hcop he
    have hR : (R^(1+(1/4:ℝ)))^4=R^5 := by
      rw [rpow_to_four _ _ hrp.le,show (1+(1/4:ℝ))*4=((5:ℕ):ℝ) by norm_num]
      exact Real.rpow_natCast _ 5
    have hC : C^4=(K:ℝ) := by
      unfold C
      rw [rpow_to_four _ _ hkr.le,show (1/4:ℝ)*4=1 by norm_num,Real.rpow_one]
    apply le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) (by positivity)
    rw [mul_pow,hC]
    exact hlo.trans_eq (congrArg (fun r : ℝ => (K:ℝ)*r) hR.symm)
  · rintro ⟨C,hCp,h⟩
    obtain ⟨K,hK⟩ := exists_nat_ge (C^4)
    have hKp : 0<K := by
      have hr := (pow_pos hCp 4).trans_le hK
      exact_mod_cast hr
    refine ⟨K,hKp,?_⟩
    intro a b c ha hb hc hcop he
    let R : ℝ := radical (a*b*c)
    have hrp : 0<R := by dsimp [R]; exact_mod_cast radical_pos (a*b*c)
    have hR : (R^(1+(1/4:ℝ)))^4=R^5 := by
      rw [rpow_to_four _ _ hrp.le,show (1+(1/4:ℝ))*4=((5:ℕ):ℝ) by norm_num]
      exact Real.rpow_natCast _ 5
    have hc4 := pow_le_pow_left₀ (by positivity : 0≤(c:ℝ)) (h a b c ha hb hc hcop he) 4
    change (c:ℝ)^4 ≤ (C*R^(1+(1/4:ℝ)))^4 at hc4
    rw [mul_pow,hR] at hc4
    have hs : (c:ℝ)^4 ≤ (K:ℝ)*R^5 :=
      hc4.trans (mul_le_mul_of_nonneg_right hK (pow_nonneg hrp.le _))
    dsimp [R] at hs
    exact_mod_cast hs

end RudinABC
