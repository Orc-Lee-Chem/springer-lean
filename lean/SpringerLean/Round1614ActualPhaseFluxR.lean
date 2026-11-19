import SpringerLean.Round1613RadialFluxTimeFormula

namespace SpringerLean

/-- The actual radial flux identity at any point where the multiplier
has its prescribed local slope with respect to multiplier time. -/
theorem actualHarmonic_phaseFluxR_divergence
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (phi : ℂ → ℝ) (slope : ℝ)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hphi : DifferentiableAt ℝ phi z)
    (hphi_rad :
      (fderiv ℝ phi z) (z/‖z‖) =
        slope *
          (fderiv ℝ (actualHarmonicMultiplierTime F k) z) (z/‖z‖)) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      ((y z/‖z‖)*phi z - (phi z+t z*slope)*yr - (k:ℝ)*slope)*u^2 +
        2*phi z*u*Ur := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  have hy : DifferentiableAt ℝ y z :=
    actualHarmonic_norm_differentiableAt F hc hz hH
  have hy0 : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  have htime := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH (z/‖z‖)
  rw [source_radius_fderiv_radial hz0] at htime
  have htime' :
      (fderiv ℝ t z) (z/‖z‖) =
        -((k:ℝ)+t z*(fderiv ℝ y z) (z/‖z‖))/y z := by
    simpa only [mul_one] using htime
  exact radialFlux_divergence_with_time
    phi U y t z (k:ℝ) slope hphi hU hy hz0 hy0 hphi_rad htime'

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxR_divergence
