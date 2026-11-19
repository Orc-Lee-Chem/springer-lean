import SpringerLean.Round161SixCoefficientPowers

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

theorem schoberKernelQ6_coeff_six_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 6 5
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₁₀ + b₁ * b₈ + 2 * b₂ * b₇ + 3 * b₃ * b₆ +
        4 * b₄ * b₅ + b₁ ^ 2 * b₆ + 4 * b₁ * b₂ * b₅ +
        6 * b₁ * b₃ * b₄ + 4 * b₂ ^ 2 * b₄ +
        5 * b₂ * b₃ ^ 2 + b₁ ^ 3 * b₄ +
        6 * b₁ ^ 2 * b₂ * b₃ + 3 * b₁ * b₂ ^ 3 +
        b₁ ^ 4 * b₂ := by
  let R₁ := schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆
  let R₂ := schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇
  let R₃ := schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈
  let R₄ := schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉
  let R₅ := schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀
  have h₅ : PowerSeries.coeff 6 R₅ = b₁₀ := by
    simp [R₅, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT6Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT6Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT6Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT6Row]
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
  have h₄₁ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₄₂ : PowerSeries.coeff 2 R₄ = b₅ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₄₃ : PowerSeries.coeff 3 R₄ = b₆ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₄₄ : PowerSeries.coeff 4 R₄ = b₇ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have h₄₅ : PowerSeries.coeff 5 R₄ = b₈ := by
    simp [R₄, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have hmul14 : PowerSeries.coeff 6 (R₁ * R₄) =
      b₁ * b₈ + b₂ * b₇ + b₃ * b₆ + 2 * b₄ * b₅ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₄₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
      h₄₁, h₄₂, h₄₃, h₄₄, h₄₅]
    ring
  have hmul23 : PowerSeries.coeff 6 (R₂ * R₃) =
      b₂ * b₇ + 2 * b₃ * b₆ + 2 * b₄ * b₅ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₃₀, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅,
      h₃₁, h₃₂, h₃₃, h₃₄, h₃₅]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₂1 : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have hsq₁2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq₁3 : PowerSeries.coeff 3 (R₁ ^ 2) =
      2 * b₁ * b₂ := by
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
  have hsq₂2 : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁]
    ring
  have hsq₂3 : PowerSeries.coeff 3 (R₂ ^ 2) =
      2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂]
    ring
  have hsq₂4 : PowerSeries.coeff 4 (R₂ ^ 2) =
      2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃]
    ring
  have hsq₂5 : PowerSeries.coeff 5 (R₂ ^ 2) =
      2 * b₂ * b₅ + 2 * b₃ * b₄ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃, h₂₄]
    ring
  have hhigh113 : PowerSeries.coeff 6 (R₁ ^ 2 * R₃) =
      b₁ ^ 2 * b₆ + 2 * b₁ * b₂ * b₅ +
        4 * b₁ * b₃ * b₄ + b₂ ^ 2 * b₄ +
        2 * b₂ * b₃ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₃₁, h₃₂, h₃₃, h₃₄,
      hsq₁1, hsq₁2, hsq₁3, hsq₁4, hsq₁5]
    ring
  have hhigh122 : PowerSeries.coeff 6 (R₁ * R₂ ^ 2) =
      2 * b₁ * b₂ * b₅ + 2 * b₁ * b₃ * b₄ +
        3 * b₂ ^ 2 * b₄ + 3 * b₂ * b₃ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, h₁₃, h₁₄,
      hsq₂1, hsq₂2, hsq₂3, hsq₂4, hsq₂5]
    ring
  have hcube₁1 : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hcube₁2 : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1]
  have hcube₁3 : PowerSeries.coeff 3 (R₁ ^ 3) = b₁ ^ 3 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, hsq₁1, hsq₁2]
    ring
  have hcube₁4 : PowerSeries.coeff 4 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₂ := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, hsq₁1, hsq₁2, hsq₁3]
    ring
  have hcube₁5 : PowerSeries.coeff 5 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₃ + 3 * b₁ * b₂ ^ 2 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃,
      hsq₁1, hsq₁2, hsq₁3, hsq₁4]
    ring
  have hhigh1112 : PowerSeries.coeff 6 (R₁ ^ 3 * R₂) =
      b₁ ^ 3 * b₄ + 6 * b₁ ^ 2 * b₂ * b₃ +
        3 * b₁ * b₂ ^ 3 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, h₂₂, h₂₃,
      hcube₁1, hcube₁2, hcube₁3, hcube₁4, hcube₁5]
    ring
  have hhigh5 : PowerSeries.coeff 6 (R₁ ^ 5) =
      5 * b₁ ^ 4 * b₂ := by
    rw [powerSeries_coeff_six_pow_five_of_const_zero R₁ h₁₀,
      h₁₁, h₁₂]
  rw [schoberBiCoeff, schoberKernelQ6_outer_five]
  change PowerSeries.coeff 6
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]
  ring

end SpringerLean
