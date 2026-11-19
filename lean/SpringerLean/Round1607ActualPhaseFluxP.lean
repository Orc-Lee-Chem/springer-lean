import SpringerLean.Round1606ActualPhaseGradientRegularity

namespace SpringerLean

/-- The first actual flux divergence, before the drift PDE is
substituted. `chi` is any differentiable real multiplier at the point. -/
theorem actualHarmonic_phaseFluxP_divergence
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (chi : ℂ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hchi : DifferentiableAt ℝ chi z) :
    let U := actualHarmonicPhaseField F k beta
    (fderiv ℝ
      (fun w => chi w*U w*(fderiv ℝ U w (1:ℂ))) z) (1:ℂ) +
    (fderiv ℝ
      (fun w => chi w*U w*(fderiv ℝ U w Complex.I)) z) Complex.I =
      chi z *
        ((fderiv ℝ U z (1:ℂ))^2 +
         (fderiv ℝ U z Complex.I)^2) +
      chi z * U z * actualHarmonicPhaseLaplacian F k beta z +
      U z *
        ((fderiv ℝ chi z (1:ℂ))*(fderiv ℝ U z (1:ℂ)) +
         (fderiv ℝ chi z Complex.I)*(fderiv ℝ U z Complex.I)) := by
  let U := actualHarmonicPhaseField F k beta
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  obtain ⟨hUx,hUy⟩ :=
    actualHarmonicPhase_gradient_coordinates_differentiableAt
      F hc k beta hz
  have hprod := phaseFluxP_divergence_product_rule
    chi U z hchi hU hUx hUy
  simpa only [actualHarmonicPhaseLaplacian] using hprod

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxP_divergence
