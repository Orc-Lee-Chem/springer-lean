import SpringerLean.Round1583EnergyAllKEndpointQuadratic

namespace SpringerLean

/-- A convex upper bound on the mixed coefficient, a concave lower bound
on the coercive coefficient, and an affine upper bound on the pure-gradient
coefficient transfer the endpoint quadratic bound to an interior point. -/
theorem signedEnergyQuadratic_le_of_segment_coefficients
    {A₀ A₁ B₀ B₁ D₀ D₁ A B D C s lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hs : 0 ≤ s)
    (hA : (1-lam)*A₀+lam*A₁ ≤ A)
    (hB : B ≤ (1-lam)*B₀+lam*B₁)
    (hD : D ≤ (1-lam)*D₀+lam*D₁)
    (h₀ : signedEnergyQuadratic A₀ B₀ D₀ s ≤ C)
    (h₁ : signedEnergyQuadratic A₁ B₁ D₁ s ≤ C) :
    signedEnergyQuadratic A B D s ≤ C := by
  have hbase := signedEnergyQuadratic_affine_endpoint hlam₀ hlam₁ h₀ h₁
  exact signedEnergyQuadratic_le_of_coefficient_envelope hA hD hB hs hbase

/-- The absolute value of an affine combination lies below the
corresponding affine combination of absolute values. -/
theorem abs_affine_le {x₀ x₁ x lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (hx : x = (1-lam)*x₀+lam*x₁) :
    |x| ≤ (1-lam)*|x₀|+lam*|x₁| := by
  rw [hx]
  calc
    |(1-lam)*x₀+lam*x₁| ≤ |(1-lam)*x₀|+|lam*x₁| := abs_add_le _ _
    _ = (1-lam)*|x₀|+lam*|x₁| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-lam),
        abs_of_nonneg hlam₀]

/-- The positive part obeys the same affine upper bound. -/
theorem max_zero_affine_le {x₀ x₁ x lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (hx : x = (1-lam)*x₀+lam*x₁) :
    max 0 x ≤ (1-lam)*max 0 x₀+lam*max 0 x₁ := by
  apply max_le
  · positivity
  · rw [hx]
    have h₀ := le_max_right (0:ℝ) x₀
    have h₁ := le_max_right (0:ℝ) x₁
    have hl := mul_le_mul_of_nonneg_left h₀ (by linarith : 0 ≤ 1-lam)
    have hr := mul_le_mul_of_nonneg_left h₁ hlam₀
    linarith

/-- The homogeneous quadratic consequence of a bound on the slope ratio.
The endpoint certificates supply `1 ≤ A` throughout each segment. -/
theorem signedEnergyQuadratic_homogeneous
    {A B D C p v : ℝ} (hA : 1 ≤ A) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hquad : ∀ s : ℝ, 0 ≤ s → signedEnergyQuadratic A B D s ≤ C) :
    D*p^2+B*v*p+(1-A)*v^2 ≤ C*p^2 := by
  rcases eq_or_lt_of_le hp with hp0 | hp_pos
  · subst p
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, add_zero]
    have hv2 : 0 ≤ v^2 := sq_nonneg v
    have hcoef : 1-A ≤ 0 := by linarith
    simpa using mul_nonpos_of_nonpos_of_nonneg hcoef hv2
  · have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hs : 0 ≤ v/p := div_nonneg hv (le_of_lt hp_pos)
    have h := hquad (v/p) hs
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg p)
    dsimp [signedEnergyQuadratic] at hm
    field_simp at hm
    nlinarith

end SpringerLean

#print axioms SpringerLean.signedEnergyQuadratic_le_of_segment_coefficients
#print axioms SpringerLean.abs_affine_le
#print axioms SpringerLean.max_zero_affine_le
#print axioms SpringerLean.signedEnergyQuadratic_homogeneous
