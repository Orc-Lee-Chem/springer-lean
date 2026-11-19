import SpringerLean.Round154KernelSixThird

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

/-- The new `(6,3)` entry of the sixth finite log kernel. -/
theorem schoberKernelQ6_coeff_six_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 6 3
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₈ + b₁ * b₆ + 2 * b₂ * b₅ + 2 * b₃ * b₄ +
        b₁ ^ 2 * b₄ + 2 * b₁ * b₂ * b₃ + (3 : ℂ)⁻¹ * b₂ ^ 3 := by
  let R₁ := schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆
  let R₂ := schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇
  let R₃ := schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈
  have hR₃ : PowerSeries.coeff 6 R₃ = b₈ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X]
  have hprod : PowerSeries.coeff 6 (R₁ * R₂) =
      b₁ * b₆ + 2 * b₂ * b₅ + 2 * b₃ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [R₁, R₂, schoberKernelT6Row,
      Finset.sum_range_succ, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X]
    ring
  have hcube : PowerSeries.coeff 6 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₄ + 6 * b₁ * b₂ * b₃ + b₂ ^ 3 := by
    rw [show R₁ ^ 3 = R₁ ^ 2 * R₁ by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [R₁, schoberKernelT6Row,
      Finset.sum_range_succ, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, pow_two,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    ring
  rw [schoberBiCoeff, schoberKernelQ6_outer_three]
  change PowerSeries.coeff 6
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [hR₃, hprod, hcube]
  ring

end SpringerLean
