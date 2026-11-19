import SpringerLean.Round1612RadialFluxQuotient

namespace SpringerLean

/-- The paper's radial flux formula, provided the scalar multiplier has
the designated affine slope at the point.  This is the formula used for
the actual profile away from its finitely many knots. -/
theorem radialFlux_divergence_with_time
    (phi U y t : ℂ → ℝ) (z : ℂ) (k slope : ℝ)
    (hphi : DifferentiableAt ℝ phi z)
    (hU : DifferentiableAt ℝ U z)
    (hy : DifferentiableAt ℝ y z)
    (hz : z ≠ 0) (hy0 : y z ≠ 0)
    (hphi_rad :
      (fderiv ℝ phi z) (z/‖z‖) =
        slope * (fderiv ℝ t z) (z/‖z‖))
    (htime_rad :
      (fderiv ℝ t z) (z/‖z‖) =
        -(k+t z*(fderiv ℝ y z) (z/‖z‖))/y z) :
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      ((y z/‖z‖)*phi z - (phi z+t z*slope)*yr - k*slope)*u^2 +
        2*phi z*u*Ur := by
  have hq := radialFlux_divergence_quotient phi U y z hphi hU hy hz hy0
  dsimp only at hq ⊢
  rw [hphi_rad, htime_rad] at hq
  rw [hq]
  have hn : (‖z‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp
  ring

end SpringerLean

#print axioms SpringerLean.radialFlux_divergence_with_time
