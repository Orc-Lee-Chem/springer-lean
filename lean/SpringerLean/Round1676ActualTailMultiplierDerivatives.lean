import SpringerLean.Round1637ActualSplineDirectionalDerivatives

namespace SpringerLean

/-- Beyond the last knot, every actual multiplier composition has zero
real directional derivative wherever the physical time is defined. -/
theorem actualEnergyMultiplier_tail_directional_derivatives
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (htail : 1 < actualHarmonicMultiplierTime F k z)
    (u : ℂ) :
    (fderiv ℝ (fun w => energyMultiplierChi
      (actualHarmonicMultiplierTime F k w)) z) u = 0 ∧
    (fderiv ℝ (fun w => energyMultiplierF
      (actualHarmonicMultiplierTime F k w)) z) u = 0 ∧
    (fderiv ℝ (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)) z) u = 0 := by
  let t := actualHarmonicMultiplierTime F k
  have ht := actualHarmonicMultiplierTime_differentiableAt
    F hc k hz hz0 hH
  have hs := energyMultiplierSpline_derivs_on_tail (t z) htail
  refine ⟨?_, ?_, ?_⟩
  · rw [fderiv_outer_real_apply energyMultiplierChi t z u hs.1.1 ht,
      hs.1.2]
    ring
  · rw [fderiv_outer_real_apply energyMultiplierF t z u hs.2.1.1 ht,
      hs.2.1.2]
    ring
  · rw [fderiv_outer_real_apply energyMultiplierSigma t z u hs.2.2.1 ht,
      hs.2.2.2]
    ring

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_tail_directional_derivatives
