import SpringerLean.Round179KernelSixCubicSquare

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The cubic logarithmic contribution to the reversed `(3,6)` kernel
entry; all terms are finite Cauchy products of the actual forward slots. -/
theorem schoberKernelT6_cube_coeff_three_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 3 6
      ((schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) ^ 3) =
      3 * b₁ ^ 2 * b₄ + 6 * b₁ * b₂ * b₃ + b₂ ^ 3 := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : schoberInnerConstantZero T :=
    schoberKernelT6_inner_constant_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT2 : schoberInnerConstantZero (T * T) :=
    schoberInnerConstantZero_mul hT hT
  have hT2first (p : ℕ) : schoberBiCoeff 1 p (T * T) = 0 :=
    schoberBiCoeff_one_mul_of_innerConstantZero hT hT p
  have h0 : schoberBiCoeff 1 0 T = 0 := by
    simp [T, schoberBiCoeff, schoberKernelT6]
  have h1 : schoberBiCoeff 1 1 T = b₁ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (0 : Fin 6) (0 : Fin 6))
  have h2 : schoberBiCoeff 1 2 T = b₂ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (1 : Fin 6) (0 : Fin 6))
  have h3 : schoberBiCoeff 1 3 T = b₃ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (2 : Fin 6) (0 : Fin 6))
  have h4 : schoberBiCoeff 1 4 T = b₄ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (3 : Fin 6) (0 : Fin 6))
  have h5 : schoberBiCoeff 1 5 T = b₅ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (4 : Fin 6) (0 : Fin 6))
  have h6 : schoberBiCoeff 1 6 T = b₆ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (5 : Fin 6) (0 : Fin 6))
  rw [show T ^ 3 = (T * T) * T by ring,
    schoberBiCoeff_three_mul_of_innerConstantZero hT2 hT]
  simp only [hT2first, zero_mul, zero_add]
  simp only [schoberBiCoeff_two_mul_of_innerConstantZero hT hT]
  norm_num [Finset.sum_range_succ]
  dsimp only [T] at h0 h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6]
  ring

end SpringerLean
