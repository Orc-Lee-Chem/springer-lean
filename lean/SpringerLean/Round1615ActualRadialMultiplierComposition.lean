import SpringerLean.Round1614ActualPhaseFluxR

namespace SpringerLean

/-- The actual radial flux formula for any smooth outer multiplier
`f(t)`. At affine cells, `deriv f` is the printed one-sided slope. -/
theorem actualHarmonic_phaseFluxR_of_outer_multiplier
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (f : ℝ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hf : DifferentiableAt ℝ f (actualHarmonicMultiplierTime F k z)) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let phi : ℂ → ℝ := fun w => f (t w)
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      ((y z/‖z‖)*phi z -
        (phi z+t z*deriv f (t z))*yr -
        (k:ℝ)*deriv f (t z))*u^2 +
        2*phi z*u*Ur := by
  let t := actualHarmonicMultiplierTime F k
  let phi : ℂ → ℝ := fun w => f (t w)
  have ht : DifferentiableAt ℝ t z :=
    actualHarmonicMultiplierTime_differentiableAt F hc k hz hz0 hH
  have hphi : DifferentiableAt ℝ phi z := hf.comp z ht
  have hcomp := (hf.hasDerivAt.comp_hasFDerivAt z ht.hasFDerivAt).fderiv
  have hphi_rad :
      (fderiv ℝ phi z) (z/‖z‖) =
        (deriv f (t z))*(fderiv ℝ t z) (z/‖z‖) := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L (z/‖z‖)) hcomp
    change (fderiv ℝ (f ∘ t) z) (z/‖z‖) = _
    simpa only [smul_apply, smul_eq_mul] using h
  exact actualHarmonic_phaseFluxR_divergence
    F hc k beta phi (deriv f (t z)) hz hz0 hH hphi hphi_rad

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxR_of_outer_multiplier
