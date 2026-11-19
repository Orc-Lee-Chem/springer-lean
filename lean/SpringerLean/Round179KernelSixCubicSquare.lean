import SpringerLean.Round178KernelSixFiniteInputTable

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The mixed quadratic logarithmic contribution to the reversed `(3,6)`
entry, computed from the finite original-map forward coefficient table. -/
theorem schoberKernelT6_square_coeff_three_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 3 6
      ((schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) ^ 2) =
      2 * b₁ * b₆ + 4 * b₂ * b₅ + 4 * b₃ * b₄ := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : schoberInnerConstantZero T :=
    schoberKernelT6_inner_constant_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have h01 : schoberBiCoeff 1 0 T = 0 := by
    simp [T, schoberBiCoeff, schoberKernelT6]
  have h02 : schoberBiCoeff 2 0 T = 0 := by
    simp [T, schoberBiCoeff, schoberKernelT6]
  have h11 : schoberBiCoeff 1 1 T = b₁ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (0 : Fin 6) (0 : Fin 6))
  have h21 : schoberBiCoeff 2 1 T = b₂ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (0 : Fin 6) (1 : Fin 6))
  have h12 : schoberBiCoeff 1 2 T = b₂ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (1 : Fin 6) (0 : Fin 6))
  have h22 : schoberBiCoeff 2 2 T = b₃ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (1 : Fin 6) (1 : Fin 6))
  have h13 : schoberBiCoeff 1 3 T = b₃ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (2 : Fin 6) (0 : Fin 6))
  have h23 : schoberBiCoeff 2 3 T = b₄ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (2 : Fin 6) (1 : Fin 6))
  have h14 : schoberBiCoeff 1 4 T = b₄ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (3 : Fin 6) (0 : Fin 6))
  have h24 : schoberBiCoeff 2 4 T = b₅ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (3 : Fin 6) (1 : Fin 6))
  have h15 : schoberBiCoeff 1 5 T = b₅ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (4 : Fin 6) (0 : Fin 6))
  have h25 : schoberBiCoeff 2 5 T = b₆ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (4 : Fin 6) (1 : Fin 6))
  have h16 : schoberBiCoeff 1 6 T = b₆ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (5 : Fin 6) (0 : Fin 6))
  have h26 : schoberBiCoeff 2 6 T = b₇ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (5 : Fin 6) (1 : Fin 6))
  rw [pow_two, schoberBiCoeff_three_mul_of_innerConstantZero hT hT]
  norm_num [Finset.sum_range_succ]
  dsimp only [T] at h01 h02 h11 h21 h12 h22 h13 h23 h14 h24 h15 h25 h16 h26
  rw [h01, h02, h11, h21, h12, h22, h13, h23,
    h14, h24, h15, h25, h16, h26]
  ring

end SpringerLean
