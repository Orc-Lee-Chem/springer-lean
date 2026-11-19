import SpringerLean.Round176KernelSixInnerCubic

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The six finite outer rows of the degree-six quotient correction. -/
noncomputable def schoberKernelT6RowAt
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ)
    (i : Fin 6) : PowerSeries ℂ :=
  match i.val with
  | 0 => schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆
  | 1 => schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇
  | 2 => schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈
  | 3 => schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉
  | 4 => schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀
  | _ => schoberKernelT6Row b₆ b₇ b₈ b₉ b₁₀ b₁₁

/-- Finite lookup for the actual forward coefficient slots used by T6. -/
def schoberKernelT6Slot
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) : ℕ → ℂ
  | 1 => b₁
  | 2 => b₂
  | 3 => b₃
  | 4 => b₄
  | 5 => b₅
  | 6 => b₆
  | 7 => b₇
  | 8 => b₈
  | 9 => b₉
  | 10 => b₁₀
  | 11 => b₁₁
  | _ => 0

theorem schoberKernelT6_outer_coeff_fin
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ)
    (i : Fin 6) :
    PowerSeries.coeff (i.val + 1)
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
    schoberKernelT6RowAt b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ i := by
  fin_cases i <;>
    simp [schoberKernelT6, schoberKernelT6RowAt,
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-- Every finite quotient-correction coefficient is a single actual
forward coefficient, indexed by the sum of its two reciprocal degrees. -/
theorem schoberKernelT6_biCoeff_fin
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ)
    (i j : Fin 6) :
    schoberBiCoeff (j.val + 1) (i.val + 1)
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
    schoberKernelT6Slot b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
      (i.val + j.val + 1) := by
  rw [schoberBiCoeff, schoberKernelT6_outer_coeff_fin]
  fin_cases i <;> fin_cases j <;>
    simp [schoberKernelT6RowAt, schoberKernelT6Slot,
      schoberKernelT6Row, PowerSeries.coeff_X_pow]

end SpringerLean
