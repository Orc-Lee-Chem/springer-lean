import SpringerLean.Round11Energy

namespace SpringerLean

/-- At a zero of the actual harmonic filling, a phase field of order
at least two and its full real gradient both vanish. -/
theorem actualHarmonicPhaseField_zero_and_fderiv_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z = 0) :
    actualHarmonicPhaseField F k beta z = 0 ∧
      fderiv ℝ (actualHarmonicPhaseField F k beta) z = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hkm1 : k - 1 ≠ 0 := by omega
  constructor
  · simp [actualHarmonicPhaseField, hH, zero_pow hk0]
  · have h := (actualHarmonicPhaseField_hasFDerivAt
      F hc k beta hz).fderiv
    rw [h]
    ext w
    simp [hH, zero_pow hkm1]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseField_zero_and_fderiv_zero
