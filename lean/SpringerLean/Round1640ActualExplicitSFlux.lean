import SpringerLean.Round1639ActualExplicitPFlux

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual S-flux formula with the explicit certified sigma spline
on an open affine cell and away from zeros of the filling. -/
theorem actualHarmonic_phaseFluxS_explicit_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let sigma : ℂ → ℝ := fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)
    let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*(Q w).re) z) (1:ℂ) +
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*(Q w).im) z) Complex.I =
      2*sigma z*U z *
        ((Q z).re*(fderiv ℝ U z (1:ℂ)) +
         (Q z).im*(fderiv ℝ U z Complex.I)) +
      (U z)^2 *
        ((Q z).re*(fderiv ℝ sigma z (1:ℂ)) +
         (Q z).im*(fderiv ℝ sigma z Complex.I) -
         2*sigma z *
           (deriv (exteriorForwardGerm F) (conj z) /
             (actualHarmonic F z)^2).re) := by
  have hdiff := actualEnergyMultiplier_compositions_differentiableAt_cell
    F hc k i hz hz0 hH hleft hright
  exact actualHarmonic_phaseFluxS_divergence
    F hc k beta
    (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w))
    hz hH hdiff.2.2

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxS_explicit_cell
