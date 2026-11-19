import SpringerLean.Round108KernelFive

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

private noncomputable def schoberKernelR5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.C (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) +
  PowerSeries.X * PowerSeries.C
    (schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) +
  PowerSeries.X ^ 2 * PowerSeries.C
    (schoberKernelT5Row b₃ b₄ b₅ b₆ b₇) +
  PowerSeries.X ^ 3 * PowerSeries.C
    (schoberKernelT5Row b₄ b₅ b₆ b₇ b₈) +
  PowerSeries.X ^ 4 * PowerSeries.C
    (schoberKernelT5Row b₅ b₆ b₇ b₈ b₉)

private theorem schoberKernelT5_eq_X_mul_R5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ =
      PowerSeries.X * schoberKernelR5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ := by
  unfold schoberKernelT5 schoberKernelR5
  ring

private theorem schoberKernelR5_coeff_zero
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.constantCoeff
      (schoberKernelR5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ := by
  simp [schoberKernelR5]

private theorem schoberKernelR5_coeff_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelR5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
  simp [schoberKernelR5, PowerSeries.coeff_X]

/-- The complete second outer row of the fifth-order finite logarithmic
kernel. This fixes the quadratic correction before inner coefficient reads. -/
theorem schoberKernelQ5_outer_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ +
        PowerSeries.C ((2 : ℂ)⁻¹) *
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) ^ 2 := by
  let T := schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  let R := schoberKernelR5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have hT : T = PowerSeries.X * R :=
    schoberKernelT5_eq_X_mul_R5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ :=
    schoberKernelR5_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ :=
    schoberKernelR5_coeff_one b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have hT2 : PowerSeries.coeff 2 T =
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 1).trans hR1
  have hTpow2 : PowerSeries.coeff 2 (T ^ 2) =
      (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow3 : PowerSeries.coeff 2 (T ^ 3) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  have hTpow4 : PowerSeries.coeff 2 (T ^ 4) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  have hTpow5 : PowerSeries.coeff 2 (T ^ 5) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 2
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5) = _
  simp [hT2, hTpow2, hTpow3, hTpow4, hTpow5]

theorem schoberKernelQ5_coeff_one_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 1 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  have hR₂ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have hsq : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, hR₁₀]
  rw [schoberBiCoeff, schoberKernelQ5_outer_two]
  change PowerSeries.coeff 1 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]

theorem schoberKernelQ5_coeff_two_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 2 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₃ + (2 : ℂ)⁻¹ * b₁ ^ 2 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  have hR₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_two]
  change PowerSeries.coeff 2 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]

theorem schoberKernelQ5_coeff_three_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 3 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = b₄ + b₁ * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  have hR₂ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 3 (R₁ ^ 2) = 2 * b₁ * b₂ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁, hR₁₂]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_two]
  change PowerSeries.coeff 3 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]
  ring

theorem schoberKernelQ5_coeff_four_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 4 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₅ + b₁ * b₃ + (2 : ℂ)⁻¹ * b₂ ^ 2 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  have hR₂ : PowerSeries.coeff 4 R₂ = b₅ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 4 (R₁ ^ 2) =
      2 * b₁ * b₃ + b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁, hR₁₂, hR₁₃]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_two]
  change PowerSeries.coeff 4 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]
  ring

theorem schoberKernelQ5_coeff_five_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 5 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₆ + b₁ * b₄ + b₂ * b₃ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  have hR₂ : PowerSeries.coeff 5 R₂ = b₆ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hR₁₄ : PowerSeries.coeff 4 R₁ = b₄ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 5 (R₁ ^ 2) =
      2 * b₁ * b₄ + 2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁, hR₁₂, hR₁₃, hR₁₄]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_two]
  change PowerSeries.coeff 5 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]
  ring

end SpringerLean
