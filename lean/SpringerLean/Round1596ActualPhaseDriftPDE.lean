import SpringerLean.Round1595ActualPhaseLaplacian

namespace SpringerLean

/-- The actual no-division drift PDE for the harmonic filling of every
centered exterior univalent function. It holds also at zeros of H. -/
theorem actualHarmonicPhase_drift_PDE
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq (actualHarmonic F z) *
        actualHarmonicPhaseLaplacian F k beta z +
      4*(k:ℝ)*((k:ℝ)-1)*actualHarmonicPhaseField F k beta z =
    4*((k:ℝ)-1) *
      ((actualHarmonic F z).re *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1:ℂ) +
       (actualHarmonic F z).im *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I) := by
  exact actualHarmonicPhase_drift_of_laplacian_formula
    F hc k hk beta hz
    (actualHarmonicPhaseLaplacian_eq F hc k hk beta hz)

/-- The same PDE with the Euclidean squared norm used in the paper. -/
theorem actualHarmonicPhase_drift_PDE_norm
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖actualHarmonic F z‖^2 *
        actualHarmonicPhaseLaplacian F k beta z +
      4*(k:ℝ)*((k:ℝ)-1)*actualHarmonicPhaseField F k beta z =
    4*((k:ℝ)-1) *
      ((actualHarmonic F z).re *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1:ℂ) +
       (actualHarmonic F z).im *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I) := by
  simpa only [Complex.sq_norm] using
    (actualHarmonicPhase_drift_PDE F hc k hk beta hz)

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_drift_PDE
#print axioms SpringerLean.actualHarmonicPhase_drift_PDE_norm
