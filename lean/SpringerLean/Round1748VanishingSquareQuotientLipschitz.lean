import SpringerLean.Round1735ActualPFluxDifferentiability

namespace SpringerLean

/-- Squaring a numerator that vanishes linearly removes the
Lipschitz singularity of division, with Lean's zero-divisor value. -/
theorem norm_square_div_sub_square_div_le_of_norm_le
    (x y a b : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hx : ‖x‖ ≤ C*‖a‖) (hy : ‖y‖ ≤ C*‖b‖)
    (hba : ‖b‖ ≤ ‖a‖) :
    ‖x^2/a-y^2/b‖ ≤ 2*C*‖x-y‖ + C^2*‖a-b‖ := by
  by_cases hb : b = 0
  · subst b
    have hy0 : y = 0 := by
      apply norm_eq_zero.mp
      simpa using le_antisymm (by simpa using hy) (norm_nonneg y)
    subst y
    by_cases ha : a = 0
    · simp only [ha, div_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, sub_zero, norm_zero, zero_mul, mul_zero, add_zero]
      positivity
    · have har : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hq : ‖x‖^2/‖a‖ ≤ C*‖x‖ :=
        (div_le_iff₀ har).mpr (by nlinarith [norm_nonneg x])
      simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div,
        sub_zero, norm_div, norm_pow]
      nlinarith [norm_nonneg x, norm_nonneg a, sq_nonneg C]
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hapos : 0 < ‖a‖ := hbpos.trans_le hba
    have ha : a ≠ 0 := norm_ne_zero_iff.mp hapos.ne'
    have hcoef₁ : (‖x‖+‖y‖)/‖a‖ ≤ 2*C := by
      apply (div_le_iff₀ hapos).mpr
      nlinarith
    have hcoef₂ : ‖y‖^2/(‖a‖*‖b‖) ≤ C^2 := by
      apply (div_le_iff₀ (mul_pos hapos hbpos)).mpr
      have hy2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
      have hmult := mul_le_mul_of_nonneg_right hba (mul_nonneg (sq_nonneg C) hbpos.le)
      nlinarith [hy2, hmult]
    have hid : x^2/a-y^2/b = (x-y)*(x+y)/a + y^2*(b-a)/(a*b) := by
      field_simp
      ring
    calc
      _ = ‖(x-y)*(x+y)/a + y^2*(b-a)/(a*b)‖ := by rw [hid]
      _ ≤ ‖(x-y)*(x+y)/a‖ + ‖y^2*(b-a)/(a*b)‖ := norm_add_le _ _
      _ = ‖x-y‖*‖x+y‖/‖a‖ + ‖y‖^2*‖a-b‖/(‖a‖*‖b‖) := by
        rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul,
          norm_pow, norm_sub_rev b a]
      _ ≤ ‖x-y‖*(‖x‖+‖y‖)/‖a‖ + ‖y‖^2*‖a-b‖/(‖a‖*‖b‖) := by
        gcongr
        exact norm_add_le _ _
      _ = ((‖x‖+‖y‖)/‖a‖)*‖x-y‖ +
          (‖y‖^2/(‖a‖*‖b‖))*‖a-b‖ := by ring
      _ ≤ (2*C)*‖x-y‖+C^2*‖a-b‖ := by gcongr

theorem norm_square_div_sub_square_div_le
    (x y a b : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hx : ‖x‖ ≤ C*‖a‖) (hy : ‖y‖ ≤ C*‖b‖) :
    ‖x^2/a-y^2/b‖ ≤ 2*C*‖x-y‖ + C^2*‖a-b‖ := by
  rcases le_total ‖b‖ ‖a‖ with h | h
  · exact norm_square_div_sub_square_div_le_of_norm_le x y a b C hC hx hy h
  · have hs := norm_square_div_sub_square_div_le_of_norm_le y x b a C hC hy hx h
    simpa only [norm_sub_rev] using hs

/-- A uniform linear vanishing bound and two ordinary Lipschitz
bounds suffice for a Lipschitz quotient through its full zero set. -/
theorem lipschitzOnWith_vanishing_square_quotient
    {E : Type*} [PseudoMetricSpace E] (u v : E → ℂ)
    (s : Set E) (Ku Kv C : NNReal)
    (hu : LipschitzOnWith Ku u s) (hv : LipschitzOnWith Kv v s)
    (hvanish : ∀ z ∈ s, ‖u z‖ ≤ (C : ℝ)*‖v z‖) :
    LipschitzOnWith (2*C*Ku+C^2*Kv) (fun z => (u z)^2/v z) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have h := norm_square_div_sub_square_div_le
    (u z) (u w) (v z) (v w) C C.coe_nonneg
    (hvanish z hz) (hvanish w hw)
  have hu' := hu.dist_le_mul z hz w hw
  have hv' := hv.dist_le_mul z hz w hw
  simp only [dist_eq_norm] at hu' hv' ⊢
  calc
    _ ≤ _ := h
    _ ≤ 2*(C : ℝ)*((Ku : ℝ)*dist z w) +
        (C : ℝ)^2*((Kv : ℝ)*dist z w) := by gcongr
    _ = _ := by push_cast; ring

end SpringerLean

#print axioms SpringerLean.lipschitzOnWith_vanishing_square_quotient
