import SpringerLean.Round109KernelFiveSecond

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The third outer row of the degree-five finite logarithmic kernel, before
its five inner coefficient reads. -/
theorem schoberKernelQ5_outer_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 3
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) ^ 3 := by
  let T := schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  let R : PowerSeries (PowerSeries ℂ) :=
    PowerSeries.C (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) +
    PowerSeries.X * PowerSeries.C
      (schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) +
    PowerSeries.X ^ 2 * PowerSeries.C
      (schoberKernelT5Row b₃ b₄ b₅ b₆ b₇) +
    PowerSeries.X ^ 3 * PowerSeries.C
      (schoberKernelT5Row b₄ b₅ b₆ b₇ b₈) +
    PowerSeries.X ^ 4 * PowerSeries.C
      (schoberKernelT5Row b₅ b₆ b₇ b₈ b₉)
  have hT : T = PowerSeries.X * R := by
    dsimp [T, R, schoberKernelT5]
    ring
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ := by
    simp [R]
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    simp [R, PowerSeries.coeff_X]
  have hR2 : PowerSeries.coeff 2 R =
      schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ := by
    simp [R, PowerSeries.coeff_X]
  have hT3 : PowerSeries.coeff 3 T =
      schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 2).trans hR2
  have hTpow2 : PowerSeries.coeff 3 (T ^ 2) =
      2 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 1
    rw [h]
    rw [PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hTpow3 : PowerSeries.coeff 3 (T ^ 3) =
      (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅) ^ 3 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow4 : PowerSeries.coeff 3 (T ^ 4) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  have hTpow5 : PowerSeries.coeff 3 (T ^ 5) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 3
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5) = _
  simp [hT3, hTpow2, hTpow3, hTpow4, hTpow5]
  have hhalf : (PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  calc
    _ = ((PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2) *
        (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
          schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) := by ring
    _ = _ := by rw [hhalf]; ring

end SpringerLean
