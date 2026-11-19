import SpringerLean.Round1654InverseConjugateDriftBound

namespace SpringerLean

/-- The radial phase derivative is bounded by the Euclidean phase
gradient in the exact normalization used by the energy certificate. -/
theorem phase_radial_derivative_abs_le
    (U : ℂ → ℝ) {z : ℂ} (hz : z ≠ 0) :
    |(fderiv ℝ U z) (z/‖z‖)| ≤
      Real.sqrt
        (((fderiv ℝ U z) (1:ℂ))^2+
         ((fderiv ℝ U z) Complex.I)^2) := by
  let Q : ℂ := z/‖z‖
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  have hQ : ‖Q‖ = 1 := by
    simp [Q, norm_div, norm_ne_zero_iff.mpr hz]
  have hdot := complex_dot_abs_le_gradient_sqrt Q ux uy
  rw [hQ, one_mul] at hdot
  have hcart := fderiv_radial_cartesian U z hz
  have hre : Q.re = z.re/‖z‖ := by
    simp [Q, Complex.div_ofReal_re]
  have him : Q.im = z.im/‖z‖ := by
    simp [Q, Complex.div_ofReal_im]
  rw [hre, him] at hdot
  simpa only [ux, uy] using hcart.symm ▸ hdot

end SpringerLean

#print axioms SpringerLean.phase_radial_derivative_abs_le
