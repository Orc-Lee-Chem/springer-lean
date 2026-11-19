import SpringerLean.Round1715EnergyMultiplierLinearBoundary
import SpringerLean.Round11Energy

namespace SpringerLean

/-- The actual phase field is bounded by the kth power of the actual
harmonic filling, with the phase normalized to unit modulus. -/
theorem actualHarmonicPhaseField_abs_le_power
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ)
    (hbeta : ‖beta‖ = 1) :
    |actualHarmonicPhaseField F k beta z| ≤
      ‖actualHarmonic F z‖^k := by
  calc
    |actualHarmonicPhaseField F k beta z| =
        |(beta * (actualHarmonic F z)^k).im| := rfl
    _ ≤ ‖beta * (actualHarmonic F z)^k‖ :=
      Complex.abs_im_le_norm _
    _ = ‖actualHarmonic F z‖^k := by
      rw [norm_mul, hbeta, one_mul, norm_pow]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseField_abs_le_power
