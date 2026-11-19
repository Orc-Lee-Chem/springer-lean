import SpringerLean.Round1927OddStarSeedExpansion

namespace SpringerLean

theorem oddStarSeed_denominator_ne_zero
    (t : ℝ) (ht : |t| < 1) (z : ℂ) (hz : z ∈ exteriorDisk) :
    z - (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have heq : z = (t : ℂ) * Complex.I := sub_eq_zero.mp h
  have hnorm : ‖z‖ = |t| := by
    rw [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    rfl
  change 1 < ‖z‖ at hz
  rw [hnorm] at hz
  linarith

/-- The odd-star seed is holomorphic throughout the open exterior disk. -/
theorem oddStarSeed_analyticOnNhd_exteriorDisk
    (t : ℝ) (ht : |t| < 1) :
    AnalyticOnNhd ℂ (oddStarSeed t) exteriorDisk := by
  change AnalyticOnNhd ℂ
    (fun z : ℂ =>
      (z - (t : ℂ) * Complex.I +
        (Real.sqrt (1 - t ^ 2) : ℂ)) ^ 2 /
        (z - (t : ℂ) * Complex.I)) exteriorDisk
  apply AnalyticOnNhd.div
  · fun_prop
  · fun_prop
  · exact oddStarSeed_denominator_ne_zero t ht

end SpringerLean

#print axioms SpringerLean.oddStarSeed_denominator_ne_zero
#print axioms SpringerLean.oddStarSeed_analyticOnNhd_exteriorDisk
