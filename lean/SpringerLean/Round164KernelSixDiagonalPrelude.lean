import SpringerLean.Round163SixKernelFifthMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The outer quotient correction after removing its one factor of `X`. -/
noncomputable def schoberKernelOuterR6
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

theorem schoberKernelT6_eq_X_mul_outerR6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ =
      PowerSeries.X *
        schoberKernelOuterR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ := by
  unfold schoberKernelT6 schoberKernelOuterR6
  ring

/-- Sixth outer coefficient of the finite logarithmic kernel, expressed
through only six bounded coefficient reads of the shifted correction. -/
theorem schoberKernelQ6_outer_six_shift
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    let R := schoberKernelOuterR6
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    PowerSeries.coeff 6
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      PowerSeries.coeff 5 R +
      PowerSeries.C ((2 : ℂ)⁻¹) * PowerSeries.coeff 4 (R ^ 2) +
      PowerSeries.C ((3 : ℂ)⁻¹) * PowerSeries.coeff 3 (R ^ 3) +
      PowerSeries.C ((4 : ℂ)⁻¹) * PowerSeries.coeff 2 (R ^ 4) +
      PowerSeries.C ((5 : ℂ)⁻¹) * PowerSeries.coeff 1 (R ^ 5) +
      PowerSeries.C ((6 : ℂ)⁻¹) * PowerSeries.coeff 0 (R ^ 6) := by
  dsimp only
  let R := schoberKernelOuterR6
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  let T := schoberKernelT6
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : T = PowerSeries.X * R :=
    schoberKernelT6_eq_X_mul_outerR6
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hpow (d : ℕ) :
      PowerSeries.coeff 6 (T ^ d) =
        PowerSeries.coeff 6 (PowerSeries.X ^ d * R ^ d) := by
    rw [hT, mul_pow]
  have h1 : PowerSeries.coeff 6 T = PowerSeries.coeff 5 R := by
    rw [hT]
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul R 1 5
  have h2 : PowerSeries.coeff 6 (T ^ 2) = PowerSeries.coeff 4 (R ^ 2) := by
    rw [hpow]
    exact PowerSeries.coeff_X_pow_mul (R ^ 2) 2 4
  have h3 : PowerSeries.coeff 6 (T ^ 3) = PowerSeries.coeff 3 (R ^ 3) := by
    rw [hpow]
    exact PowerSeries.coeff_X_pow_mul (R ^ 3) 3 3
  have h4 : PowerSeries.coeff 6 (T ^ 4) = PowerSeries.coeff 2 (R ^ 4) := by
    rw [hpow]
    exact PowerSeries.coeff_X_pow_mul (R ^ 4) 4 2
  have h5 : PowerSeries.coeff 6 (T ^ 5) = PowerSeries.coeff 1 (R ^ 5) := by
    rw [hpow]
    exact PowerSeries.coeff_X_pow_mul (R ^ 5) 5 1
  have h6 : PowerSeries.coeff 6 (T ^ 6) = PowerSeries.coeff 0 (R ^ 6) := by
    rw [hpow]
    exact PowerSeries.coeff_X_pow_mul (R ^ 6) 6 0
  change PowerSeries.coeff 6
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
        PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) = _
  simp [h1, h2, h3, h4, h5, h6]
  rfl

end SpringerLean
