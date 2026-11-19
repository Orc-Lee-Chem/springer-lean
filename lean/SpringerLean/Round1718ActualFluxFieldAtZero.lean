import SpringerLean.Round1717ActualEnergyFluxFields
import SpringerLean.Round1712PhaseFieldAtFillingZero

namespace SpringerLean

/-- The three actual physical flux fields and their signed combination
take the prescribed zero value at every filling zero in the source
disk. This is the value half of the zero-extension argument. -/
theorem actualEnergyFluxFields_zero_at_filling_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z = 0) :
    actualEnergyFluxPField F k beta z = 0 ∧
    actualEnergyFluxRField F k beta z = 0 ∧
    actualEnergyFluxSField F k beta z = 0 ∧
    actualEnergyFluxField F k beta z = 0 := by
  obtain ⟨hU, hUd⟩ :=
    actualHarmonicPhaseField_zero_and_fderiv_zero F hc k hk beta hz hH
  have hP : actualEnergyFluxPField F k beta z = 0 := by
    apply Complex.ext <;>
      simp [actualEnergyFluxPField, hU, hUd]
  have hR : actualEnergyFluxRField F k beta z = 0 := by
    apply Complex.ext <;>
      simp [actualEnergyFluxRField, hU]
  have hS : actualEnergyFluxSField F k beta z = 0 := by
    apply Complex.ext <;>
      simp [actualEnergyFluxSField, hU]
  refine ⟨hP, hR, hS, ?_⟩
  simp [actualEnergyFluxField, hP, hR, hS]

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxFields_zero_at_filling_zero
