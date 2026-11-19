import SpringerLean.Round1638ActualEnergyProfile

namespace SpringerLean

/-- The actual P-flux formula with the explicit certified chi spline on
an open affine cell. -/
theorem actualHarmonic_phaseFluxP_explicit_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let chi : ℂ → ℝ := fun w => energyMultiplierChi
      (actualHarmonicMultiplierTime F k w)
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
  have hdiff := actualEnergyMultiplier_compositions_differentiableAt_cell
    F hc k i hz hz0 hH hleft hright
  exact actualHarmonic_phaseFluxP_divergence
    F hc k beta
    (fun w => energyMultiplierChi
      (actualHarmonicMultiplierTime F k w))
    hz hdiff.1

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxP_explicit_cell
