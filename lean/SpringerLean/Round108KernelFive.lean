import SpringerLean.Round107NinthCoeff

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Five reciprocal modes in one outer row of the degree-five finite
logarithmic kernel. -/
noncomputable def schoberKernelT5Row
    (a b c d e : ℂ) : PowerSeries ℂ :=
  PowerSeries.C a * PowerSeries.X +
  PowerSeries.C b * PowerSeries.X ^ 2 +
  PowerSeries.C c * PowerSeries.X ^ 3 +
  PowerSeries.C d * PowerSeries.X ^ 4 +
  PowerSeries.C e * PowerSeries.X ^ 5

/-- The degree-five bivariate quotient correction built from the original
forward coefficient slots b₁ through b₉. -/
noncomputable def schoberKernelT5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.X * PowerSeries.C
    (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) +
  PowerSeries.X ^ 2 * PowerSeries.C
    (schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) +
  PowerSeries.X ^ 3 * PowerSeries.C
    (schoberKernelT5Row b₃ b₄ b₅ b₆ b₇) +
  PowerSeries.X ^ 4 * PowerSeries.C
    (schoberKernelT5Row b₄ b₅ b₆ b₇ b₈) +
  PowerSeries.X ^ 5 * PowerSeries.C
    (schoberKernelT5Row b₅ b₆ b₇ b₈ b₉)

/-- Finite `-log(1-T)` through total power five. Higher powers do not
affect matrix entries whose two reciprocal indices are at most five. -/
noncomputable def schoberKernelQ5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  let T := schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
      PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5

/-- The first outer row of the degree-five logarithmic kernel is exactly
the first five original forward coefficients, with no sign reversal. -/
theorem schoberKernelQ5_outer_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ := by
  have hT0 : PowerSeries.constantCoeff
      (schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = 0 := by
    simp [schoberKernelT5]
  simp [schoberKernelQ5, schoberKernelT5,
    PowerSeries.coeff_one_pow, hT0]

theorem schoberKernelQ5_first_row
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    let Q := schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    schoberBiCoeff 1 1 Q = b₁ ∧
    schoberBiCoeff 2 1 Q = b₂ ∧
    schoberBiCoeff 3 1 Q = b₃ ∧
    schoberBiCoeff 4 1 Q = b₄ ∧
    schoberBiCoeff 5 1 Q = b₅ := by
  dsimp only
  simp only [schoberBiCoeff, schoberKernelQ5_outer_one]
  simp [schoberKernelT5Row, PowerSeries.coeff_X_pow]

end SpringerLean
