import SpringerLean.Round1735ActualPFluxDifferentiability

open scoped ComplexConjugate

namespace SpringerLean

/-- The radial flux is differentiable on the regular source region
where the physical f multiplier is differentiable. -/
theorem actualEnergyFluxRField_differentiableAt_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (hH : actualHarmonic F z ≠ 0)
    (hphi : DifferentiableAt ℝ
      (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z) :
    DifferentiableAt ℝ (actualEnergyFluxRField F k beta) z := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let phi : ℂ → ℝ := fun w =>
    energyMultiplierF (actualHarmonicMultiplierTime F k w)
  let B : ℂ → ℝ := fun w => phi w * (U w)^2 / y w
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  have hy := actualHarmonic_norm_differentiableAt F hc hz hH
  have hy0 : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  have hB : DifferentiableAt ℝ B z := by
    change DifferentiableAt ℝ
      (fun w => (phi w * (U w)^2) * (y w)⁻¹) z
    exact (hphi.mul (hU.pow 2)).mul (hy.inv hy0)
  have hr := source_radius_differentiableAt hz0
  have hr0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hzr : DifferentiableAt ℝ (fun w : ℂ => w.re) z :=
    Complex.reCLM.differentiableAt
  have hzi : DifferentiableAt ℝ (fun w : ℂ => w.im) z :=
    Complex.imCLM.differentiableAt
  have hx : DifferentiableAt ℝ
      (fun w => (B w * w.re) / ‖w‖) z := by
    change DifferentiableAt ℝ
      (fun w => (B w * w.re) * (‖w‖)⁻¹) z
    exact (hB.mul hzr).mul (hr.inv hr0)
  have hi : DifferentiableAt ℝ
      (fun w => (B w * w.im) / ‖w‖) z := by
    change DifferentiableAt ℝ
      (fun w => (B w * w.im) * (‖w‖)⁻¹) z
    exact (hB.mul hzi).mul (hr.inv hr0)
  exact complex_mk_differentiableAt_of_coordinates _ _ z hx hi

/-- The inverse-filling drift flux is differentiable on the regular
source region where the physical sigma multiplier is. -/
theorem actualEnergyFluxSField_differentiableAt_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0)
    (hsigma : DifferentiableAt ℝ
      (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z) :
    DifferentiableAt ℝ (actualEnergyFluxSField F k beta) z := by
  let U := actualHarmonicPhaseField F k beta
  let sigma : ℂ → ℝ := fun w =>
    energyMultiplierSigma (actualHarmonicMultiplierTime F k w)
  let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  have hQ : DifferentiableAt ℝ Q z :=
    actualHarmonic_inverseConjugate_differentiableAt F hc hz hH
  have hQx : DifferentiableAt ℝ (fun w => (Q w).re) z :=
    Complex.reCLM.differentiableAt.comp z hQ
  have hQy : DifferentiableAt ℝ (fun w => (Q w).im) z :=
    Complex.imCLM.differentiableAt.comp z hQ
  have hB : DifferentiableAt ℝ
      (fun w => sigma w * (U w)^2) z :=
    hsigma.mul (hU.pow 2)
  have hx : DifferentiableAt ℝ
      (fun w => sigma w * (U w)^2 * (Q w).re) z := hB.mul hQx
  have hi : DifferentiableAt ℝ
      (fun w => sigma w * (U w)^2 * (Q w).im) z := hB.mul hQy
  exact complex_mk_differentiableAt_of_coordinates _ _ z hx hi

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxRField_differentiableAt_regular
#print axioms SpringerLean.actualEnergyFluxSField_differentiableAt_regular
