import SpringerLean.Round1642ActualDividedDriftPDE

open scoped ComplexConjugate

namespace SpringerLean

/-- Actual P/S flux drift cancellation, before any absolute values:
the surviving term contains chi-sigma, with the displayed sign. -/
theorem actualHarmonicPhase_fluxPS_drift_cancellation
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    (chi sigma : ℝ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let Q := (conj (actualHarmonic F z))⁻¹
    let u := U z/‖actualHarmonic F z‖
    let drift := U z *
      (Q.re*(fderiv ℝ U z) (1:ℂ) +
       Q.im*(fderiv ℝ U z) Complex.I)
    chi*(U z*actualHarmonicPhaseLaplacian F k beta z) -
      2*((k:ℝ)-1)*(2*sigma*drift) =
      4*((k:ℝ)-1)*(chi-sigma)*drift -
        4*(k:ℝ)*((k:ℝ)-1)*chi*u^2 := by
  have hpde := actualHarmonicPhase_drift_PDE_divided
    F hc k hk beta hz hH
  dsimp only at hpde ⊢
  rw [hpde]
  ring

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_fluxPS_drift_cancellation
