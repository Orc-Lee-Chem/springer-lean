import SpringerLean.Round1637ActualSplineDirectionalDerivatives

namespace SpringerLean

/-- The explicit multiplier time is nonnegative at every point of the
actual open source disk, including zeros under Lean's division convention. -/
theorem actualHarmonicMultiplierTime_nonneg
    (F : ℂ → ℂ) (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    0 ≤ actualHarmonicMultiplierTime F k z := by
  unfold actualHarmonicMultiplierTime
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact norm_nonneg _

/-- The original 43-case profile certificate is available at the
actual multiplier time of every source-disk point. -/
theorem actualHarmonic_energyMultiplier_profile_exists
    (F : ℂ → ℂ) (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ cp fp sp : ℝ,
      EnergyMultiplierProfileAt
        (actualHarmonicMultiplierTime F k z)
        (energyMultiplierSplineValue
          (actualHarmonicMultiplierTime F k z)) cp fp sp :=
  energyMultiplierSpline_profile_exists _
    (actualHarmonicMultiplierTime_nonneg F k hz)

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_nonneg
#print axioms SpringerLean.actualHarmonic_energyMultiplier_profile_exists
