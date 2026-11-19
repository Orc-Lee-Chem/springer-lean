import SpringerLean.Round1655RadialPhaseDerivativeBound

namespace SpringerLean

/-- Every scalar directional derivative in the radial unit direction
is bounded by the operator norm of the real differential. -/
theorem scalar_radial_fderiv_abs_le
    (f : ℂ → ℝ) {z : ℂ} (hz : z ≠ 0) :
    |(fderiv ℝ f z) (z/‖z‖)| ≤ ‖fderiv ℝ f z‖ := by
  have hQ : ‖z/(‖z‖:ℂ)‖ = 1 := by
    simp [norm_ne_zero_iff.mpr hz]
  have hbound := (fderiv ℝ f z).le_opNorm (z/‖z‖)
  rw [hQ, mul_one] at hbound
  simpa only [Real.norm_eq_abs] using hbound

end SpringerLean

#print axioms SpringerLean.scalar_radial_fderiv_abs_le
