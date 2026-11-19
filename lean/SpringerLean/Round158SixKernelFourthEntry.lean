import SpringerLean.Round157KernelSixFourth

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

/-- The new `(6,4)` entry of the sixth finite log kernel. -/
theorem schoberKernelQ6_coeff_six_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 6 4
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₉ + b₁ * b₇ + 2 * b₂ * b₆ + 3 * b₃ * b₅ +
      (3 : ℂ) / 2 * b₄ ^ 2 + b₁ ^ 2 * b₅ +
      4 * b₁ * b₂ * b₄ + 2 * b₁ * b₃ ^ 2 +
      3 * b₂ ^ 2 * b₃ + b₁ ^ 3 * b₃ +
      (3 : ℂ) / 2 * b₁ ^ 2 * b₂ ^ 2 := by
  let R₁ := schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆
  let R₂ := schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇
  let R₃ := schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈
  let R₄ := schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉
  have h₄ : PowerSeries.coeff 6 R₄ = b₉ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT6Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT6Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT6Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₄ : PowerSeries.coeff 4 R₁ = b₄ := by
    simp [R₁, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₅ : PowerSeries.coeff 5 R₁ = b₅ := by
    simp [R₁, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₂₃ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₂₄ : PowerSeries.coeff 4 R₂ = b₅ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₂₅ : PowerSeries.coeff 5 R₂ = b₆ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₃₂ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₃₃ : PowerSeries.coeff 3 R₃ = b₅ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₃₄ : PowerSeries.coeff 4 R₃ = b₆ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₃₅ : PowerSeries.coeff 5 R₃ = b₇ := by
    simp [R₃, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 6 (R₁ * R₃) =
      b₁ * b₇ + b₂ * b₆ + 2 * b₃ * b₅ + b₄ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
      h₃₁, h₃₂, h₃₃, h₃₄, h₃₅]
    ring
  have hsq₂ : PowerSeries.coeff 6 (R₂ ^ 2) =
      2 * b₂ * b₆ + 2 * b₃ * b₅ + b₄ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₁2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq₁3 : PowerSeries.coeff 3 (R₁ ^ 2) = 2 * b₁ * b₂ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂]
    ring
  have hsq₁4 : PowerSeries.coeff 4 (R₁ ^ 2) =
      2 * b₁ * b₃ + b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃]
    ring
  have hsq₁5 : PowerSeries.coeff 5 (R₁ ^ 2) =
      2 * b₁ * b₄ + 2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃, h₁₄]
    ring
  have hhigh : PowerSeries.coeff 6 (R₁ ^ 2 * R₂) =
      b₁ ^ 2 * b₅ + 4 * b₁ * b₂ * b₄ +
      2 * b₁ * b₃ ^ 2 + 3 * b₂ ^ 2 * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, h₂₂, h₂₃, h₂₄,
      hsq₁1, hsq₁2, hsq₁3, hsq₁4, hsq₁5]
    ring
  have hfour : PowerSeries.coeff 6 (R₁ ^ 4) =
      4 * b₁ ^ 3 * b₃ + 6 * b₁ ^ 2 * b₂ ^ 2 := by
    rw [show R₁ ^ 4 = R₁ ^ 2 * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hsq₁2, hsq₁3, hsq₁4]
    ring
  rw [schoberBiCoeff, schoberKernelQ6_outer_four]
  change PowerSeries.coeff 6
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq₂, hhigh, hfour]
  ring

end SpringerLean
