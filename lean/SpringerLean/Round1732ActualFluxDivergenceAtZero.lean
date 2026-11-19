import SpringerLean.Round1731ActualFluxZeroDerivative

namespace SpringerLean

/-- At a filling zero, the signed physical flux has zero Cartesian
divergence.  This uses the derivative of the combined field, so no
individual quotient field needs to be differentiated there. -/
theorem actualCartesianDiv_actualEnergyFluxField_zero_at_filling_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1)
    (hzero : actualHarmonic F z₀ = 0) :
    actualCartesianDiv (actualEnergyFluxField F k beta) z₀ = 0 := by
  have hJ := actualEnergyFluxField_hasFDerivAt_zero_at_filling_zero
    F hc k hk beta hbeta hz₀ hzero
  have hre : HasFDerivAt
      (fun z => (actualEnergyFluxField F k beta z).re)
      (0 : ℂ →L[ℝ] ℝ) z₀ := by
    simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp z₀ hJ
  have him : HasFDerivAt
      (fun z => (actualEnergyFluxField F k beta z).im)
      (0 : ℂ →L[ℝ] ℝ) z₀ := by
    simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp z₀ hJ
  simp [actualCartesianDiv, hre.fderiv, him.fderiv]

/-- The source center is one of the filling zeros, so the same
zero-derivative and zero-divergence statements apply there. -/
theorem actualEnergyFluxField_zero_and_div_zero_at_source_center
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    HasFDerivAt (actualEnergyFluxField F k beta)
      (0 : ℂ →L[ℝ] ℂ) 0 ∧
    actualCartesianDiv (actualEnergyFluxField F k beta) 0 = 0 := by
  have hzero : actualHarmonic F 0 = 0 := by
    simpa [actualHarmonic, exteriorForwardGerm_zero]
  exact ⟨actualEnergyFluxField_hasFDerivAt_zero_at_filling_zero
      F hc k hk beta hbeta (by simp) hzero,
    actualCartesianDiv_actualEnergyFluxField_zero_at_filling_zero
      F hc k hk beta hbeta (by simp) hzero⟩

end SpringerLean

#print axioms SpringerLean.actualCartesianDiv_actualEnergyFluxField_zero_at_filling_zero
#print axioms SpringerLean.actualEnergyFluxField_zero_and_div_zero_at_source_center
