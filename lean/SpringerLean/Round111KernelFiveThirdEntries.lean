import SpringerLean.Round110KernelFiveThird

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The first inner read of the third outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_one_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 1 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = b₃ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  have h₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have hmul : PowerSeries.coeff 1 (R₁ * R₂) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀, h₂₀]
  have hcube : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  rw [schoberBiCoeff, schoberKernelQ5_outer_three]
  change PowerSeries.coeff 1
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [h₃, hmul, hcube]

/-- The second inner read of the third outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_two_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 2 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₄ + b₁ * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  have h₃ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 2 (R₁ * R₂) = b₁ * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₂₁]
  have hcube : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    rw [show R₁ ^ 3 = R₁ * (R₁ * R₁) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, PowerSeries.coeff_one_mul]
  rw [schoberBiCoeff, schoberKernelQ5_outer_three]
  change PowerSeries.coeff 2
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [h₃, hmul, hcube]

/-- The central entry is the first cubic correction in the fifth-order
logarithmic kernel. -/
theorem schoberKernelQ5_coeff_three_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 3 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₅ + b₁ * b₃ + b₂ ^ 2 + (3 : ℂ)⁻¹ * b₁ ^ 3 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  have h₃ : PowerSeries.coeff 3 R₃ = b₅ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 3 (R₁ * R₂) =
      b₁ * b₃ + b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, h₂₁, h₂₂]
    ring
  have hsq0 : PowerSeries.constantCoeff (R₁ * R₁) = 0 := by
    simp [h₁₀]
  have hsq1 : PowerSeries.coeff 1 (R₁ * R₁) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀]
  have hsq2 : PowerSeries.coeff 2 (R₁ * R₁) = b₁ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hcube : PowerSeries.coeff 3 (R₁ ^ 3) = b₁ ^ 3 := by
    rw [show R₁ ^ 3 = R₁ * (R₁ * R₁) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, hsq1, hsq2]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_three]
  change PowerSeries.coeff 3
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [h₃, hmul, hcube]
  ring

/-- Fourth inner read of the third outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_four_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 4 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₆ + b₁ * b₄ + 2 * b₂ * b₃ + b₁ ^ 2 * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  have h₃ : PowerSeries.coeff 4 R₃ = b₆ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₃ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 4 (R₁ * R₂) =
      b₁ * b₄ + 2 * b₂ * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃]
    ring
  have hsq1 : PowerSeries.coeff 1 (R₁ * R₁) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀]
  have hsq2 : PowerSeries.coeff 2 (R₁ * R₁) = b₁ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq3 : PowerSeries.coeff 3 (R₁ * R₁) = 2 * b₁ * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂]
    ring
  have hcube : PowerSeries.coeff 4 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₂ := by
    rw [show R₁ ^ 3 = R₁ * (R₁ * R₁) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, hsq1, hsq2, hsq3]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_three]
  change PowerSeries.coeff 4
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [h₃, hmul, hcube]
  ring

/-- Fifth inner read of the third outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_five_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 5 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₇ + b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 +
        b₁ ^ 2 * b₃ + b₁ * b₂ ^ 2 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  have h₃ : PowerSeries.coeff 5 R₃ = b₇ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₄ : PowerSeries.coeff 4 R₁ = b₄ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₃ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₄ : PowerSeries.coeff 4 R₂ = b₅ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 5 (R₁ * R₂) =
      b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, h₁₃, h₁₄, h₂₁, h₂₂, h₂₃, h₂₄]
    ring
  have hsq1 : PowerSeries.coeff 1 (R₁ * R₁) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀]
  have hsq2 : PowerSeries.coeff 2 (R₁ * R₁) = b₁ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq3 : PowerSeries.coeff 3 (R₁ * R₁) = 2 * b₁ * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂]
    ring
  have hsq4 : PowerSeries.coeff 4 (R₁ * R₁) =
      2 * b₁ * b₃ + b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃]
    ring
  have hcube : PowerSeries.coeff 5 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₃ + 3 * b₁ * b₂ ^ 2 := by
    rw [show R₁ ^ 3 = R₁ * (R₁ * R₁) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃, hsq1, hsq2, hsq3, hsq4]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_three]
  change PowerSeries.coeff 5
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [h₃, hmul, hcube]
  ring

end SpringerLean
