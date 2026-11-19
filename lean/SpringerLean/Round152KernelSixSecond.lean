import SpringerLean.Round151KernelSix

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

private noncomputable def schoberKernelR6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.C (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆) +
  PowerSeries.X * PowerSeries.C
    (schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇) +
  PowerSeries.X ^ 2 * PowerSeries.C
    (schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈) +
  PowerSeries.X ^ 3 * PowerSeries.C
    (schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉) +
  PowerSeries.X ^ 4 * PowerSeries.C
    (schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀) +
  PowerSeries.X ^ 5 * PowerSeries.C
    (schoberKernelT6Row b₆ b₇ b₈ b₉ b₁₀ b₁₁)

private theorem schoberKernelT6_eq_X_mul_R6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ =
      PowerSeries.X * schoberKernelR6
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ := by
  unfold schoberKernelT6 schoberKernelR6
  ring

private theorem schoberKernelR6_coeff_zero
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries.constantCoeff
      (schoberKernelR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ := by
  simp [schoberKernelR6]

private theorem schoberKernelR6_coeff_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
  simp [schoberKernelR6, PowerSeries.coeff_X]

theorem schoberKernelQ6_outer_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries.coeff 2
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ +
        PowerSeries.C ((2 : ℂ)⁻¹) *
          (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆) ^ 2 := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  let R := schoberKernelR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : T = PowerSeries.X * R :=
    schoberKernelT6_eq_X_mul_R6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ :=
    schoberKernelR6_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ :=
    schoberKernelR6_coeff_one b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT2 : PowerSeries.coeff 2 T =
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 1).trans hR1
  have hTpow2 : PowerSeries.coeff 2 (T ^ 2) =
      (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆) ^ 2 := by
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
  have hTpow6 : PowerSeries.coeff 2 (T ^ 6) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 2
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
        PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) = _
  simp [hT2, hTpow2, hTpow3, hTpow4, hTpow5, hTpow6]

/-- New sixth-column entry in the second outer row. -/
theorem schoberKernelQ6_coeff_six_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 6 2
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₇ + b₁ * b₅ + b₂ * b₄ + (2 : ℂ)⁻¹ * b₃ ^ 2 := by
  let R₁ := schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆
  let R₂ := schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇
  have hR₂ : PowerSeries.coeff 6 R₂ = b₇ := by
    simp [R₂, schoberKernelT6Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 6 (R₁ ^ 2) =
      2 * b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [R₁, schoberKernelT6Row,
      Finset.sum_range_succ, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X]
    ring
  rw [schoberBiCoeff, schoberKernelQ6_outer_two]
  change PowerSeries.coeff 6
      (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]
  ring

end SpringerLean
