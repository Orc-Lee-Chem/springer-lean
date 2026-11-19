import SpringerLean.Round173KernelSixInnerQuadratic

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The second inner coefficient of the sixth outer correction row. -/
theorem schoberKernelT6_coeff_two_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 2 6
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) = b₇ := by
  let R := schoberKernelOuterR6
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hR5 : PowerSeries.coeff 5 R =
      schoberKernelT6Row b₆ b₇ b₈ b₉ b₁₀ b₁₁ := by
    simp [R, schoberKernelOuterR6, PowerSeries.coeff_X]
  rw [schoberBiCoeff, schoberKernelT6_eq_X_mul_outerR6,
    show PowerSeries.coeff 6 (PowerSeries.X * R) =
      PowerSeries.coeff 5 R by
        simpa only [pow_one] using PowerSeries.coeff_X_pow_mul R 1 5,
    hR5]
  simp [schoberKernelT6Row, PowerSeries.coeff_X_pow]

/-- The square contribution to the `(2,6)` logarithmic coefficient. -/
theorem schoberKernelT6_square_coeff_two_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 2 6
      ((schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) ^ 2) =
      2 * b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  let R := schoberKernelOuterR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT := schoberKernelT6_inner_constant_zero
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hmode (k : ℕ) (r : PowerSeries ℂ)
      (hr : PowerSeries.coeff k R = r) :
      schoberBiCoeff 1 (k + 1) T = PowerSeries.coeff 1 r := by
    unfold schoberBiCoeff
    rw [show T = PowerSeries.X * R from
      schoberKernelT6_eq_X_mul_outerR6
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁,
      show PowerSeries.coeff (k + 1) (PowerSeries.X * R) =
        PowerSeries.coeff k R by
          simpa only [pow_one] using PowerSeries.coeff_X_pow_mul R 1 k,
      hr]
  have h0 : schoberBiCoeff 1 0 T = 0 := by
    simp [T, schoberBiCoeff, schoberKernelT6]
  have ht1 : schoberBiCoeff 1 1 T = b₁ := by
    have hr : PowerSeries.coeff 0 R =
        schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ := by
      simp [R, schoberKernelOuterR6]
    simpa [schoberKernelT6Row, PowerSeries.coeff_X_pow] using
      hmode 0 _ hr
  have ht2 : schoberBiCoeff 1 2 T = b₂ := by
    have hr : PowerSeries.coeff 1 R =
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
      simp [R, schoberKernelOuterR6, PowerSeries.coeff_X]
    simpa [schoberKernelT6Row, PowerSeries.coeff_X_pow] using
      hmode 1 _ hr
  have ht3 : schoberBiCoeff 1 3 T = b₃ := by
    have hr : PowerSeries.coeff 2 R =
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ := by
      simp [R, schoberKernelOuterR6, PowerSeries.coeff_X]
    simpa [schoberKernelT6Row, PowerSeries.coeff_X_pow] using
      hmode 2 _ hr
  have ht4 : schoberBiCoeff 1 4 T = b₄ := by
    have hr : PowerSeries.coeff 3 R =
        schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉ := by
      simp [R, schoberKernelOuterR6, PowerSeries.coeff_X]
    simpa [schoberKernelT6Row, PowerSeries.coeff_X_pow] using
      hmode 3 _ hr
  have ht5 : schoberBiCoeff 1 5 T = b₅ := by
    have hr : PowerSeries.coeff 4 R =
        schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀ := by
      simp [R, schoberKernelOuterR6, PowerSeries.coeff_X]
    simpa [schoberKernelT6Row, PowerSeries.coeff_X_pow] using
      hmode 4 _ hr
  have ht6 : schoberBiCoeff 1 6 T = b₆ := by
    exact schoberKernelT6_coeff_one_six
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  rw [pow_two]
  rw [schoberBiCoeff_two_mul_of_innerConstantZero hT hT]
  norm_num [Finset.sum_range_succ]
  dsimp only [T] at h0 ht1 ht2 ht3 ht4 ht5 ht6
  rw [h0, ht1, ht2, ht3, ht4, ht5, ht6]
  ring

/-- The reversed `(2,6)` entry of the finite sixth logarithmic kernel.
All higher logarithmic powers disappear by inner-degree counting. -/
theorem schoberKernelQ6_coeff_two_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 2 6
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₇ + b₁ * b₅ + b₂ * b₄ + (2 : ℂ)⁻¹ * b₃ ^ 2 := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT := schoberKernelT6_inner_constant_zero
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hp (k : ℕ) (hk : 3 ≤ k) :
      schoberBiCoeff 2 6 (T ^ k) = 0 :=
    schoberBiCoeff_two_pow_eq_zero hT k 6 hk
  have hfirst : schoberBiCoeff 2 6 T = b₇ :=
    schoberKernelT6_coeff_two_six
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hsq : schoberBiCoeff 2 6 (T ^ 2) =
      2 * b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 :=
    schoberKernelT6_square_coeff_two_six
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  change schoberBiCoeff 2 6
    (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
      PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
      PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) = _
  simp only [schoberBiCoeff] at hp hfirst hsq
  simp [schoberBiCoeff, PowerSeries.coeff_C_mul, hp, hfirst, hsq]
  ring

end SpringerLean
