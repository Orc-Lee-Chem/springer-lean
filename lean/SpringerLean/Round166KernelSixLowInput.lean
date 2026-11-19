import SpringerLean.Round165KernelLowCongruence

set_option maxHeartbeats 3000000

namespace SpringerLean

open PowerSeries

/-- Enlarging the quotient correction from five to six modes leaves the
old five-by-five coefficient block unchanged. -/
theorem schoberKernelT6_low_eq_T5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberLowEq 6
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁)
      (schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) := by
  intro i j hi hj
  interval_cases i <;> interval_cases j <;>
    simp only [schoberBiCoeff, schoberKernelT6, schoberKernelT5,
      map_add, PowerSeries.coeff_X_pow_mul'] <;>
    simp [schoberKernelT6Row, schoberKernelT5Row,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul] <;>
    simp only [← map_pow, PowerSeries.coeff_C,
      PowerSeries.coeff_X_pow] <;>
    simp

end SpringerLean
