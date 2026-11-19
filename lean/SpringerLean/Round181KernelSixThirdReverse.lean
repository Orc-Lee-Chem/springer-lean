import SpringerLean.Round180KernelSixCubicCube

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The reversed `(3,6)` entry of the sixth finite logarithmic kernel.
Only the first three logarithmic powers can contribute. -/
theorem schoberKernelQ6_coeff_three_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 3 6
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      b₈ + b₁ * b₆ + 2 * b₂ * b₅ + 2 * b₃ * b₄ +
      b₁ ^ 2 * b₄ + 2 * b₁ * b₂ * b₃ +
      (3 : ℂ)⁻¹ * b₂ ^ 3 := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : schoberInnerConstantZero T :=
    schoberKernelT6_inner_constant_zero
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hp (k : ℕ) (hk : 4 ≤ k) :
      schoberBiCoeff 3 6 (T ^ k) = 0 :=
    schoberBiCoeff_three_pow_eq_zero hT k 6 hk
  have hfirst : schoberBiCoeff 3 6 T = b₈ := by
    simpa [T, schoberKernelT6Slot] using
      (schoberKernelT6_biCoeff_fin
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
        (5 : Fin 6) (2 : Fin 6))
  have hsq : schoberBiCoeff 3 6 (T ^ 2) =
      2 * b₁ * b₆ + 4 * b₂ * b₅ + 4 * b₃ * b₄ :=
    schoberKernelT6_square_coeff_three_six
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hcube : schoberBiCoeff 3 6 (T ^ 3) =
      3 * b₁ ^ 2 * b₄ + 6 * b₁ * b₂ * b₃ + b₂ ^ 3 :=
    schoberKernelT6_cube_coeff_three_six
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  change schoberBiCoeff 3 6
    (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
      PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
      PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) = _
  simp only [schoberBiCoeff] at hp hfirst hsq hcube
  simp [schoberBiCoeff, PowerSeries.coeff_C_mul,
    hp, hfirst, hsq, hcube]
  ring

end SpringerLean
