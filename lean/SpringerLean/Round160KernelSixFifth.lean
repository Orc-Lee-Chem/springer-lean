import SpringerLean.Round159SixKernelFourthMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Fifth outer row of the finite degree-six logarithmic kernel.
This is the coefficient identity before its five inner reads. -/
theorem schoberKernelQ6_outer_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries.coeff 5
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀ +
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉ +
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ *
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ +
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 2 *
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ +
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ ^ 2 +
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 3 *
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ +
      PowerSeries.C ((5 : ℂ)⁻¹) *
        (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 5) := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  let R : PowerSeries (PowerSeries ℂ) :=
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
  have hT : T = PowerSeries.X * R := by
    dsimp [T, R, schoberKernelT6]
    ring
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ := by
    simp [R]
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
    simp [R, PowerSeries.coeff_X]
  have hR2 : PowerSeries.coeff 2 R =
      schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ := by
    simp [R, PowerSeries.coeff_X]
  have hR3 : PowerSeries.coeff 3 R =
      schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉ := by
    simp [R, PowerSeries.coeff_X]
  have hR4 : PowerSeries.coeff 4 R =
      schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀ := by
    simp [R, PowerSeries.coeff_X]
  have hT5 : PowerSeries.coeff 5 T =
      schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 4).trans hR4
  have hTpow2 : PowerSeries.coeff 5 (T ^ 2) =
      2 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉ +
      2 * schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ *
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 3
    rw [h, pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2, hR3]
    ring
  have hRpow2_1 : PowerSeries.coeff 1 (R ^ 2) =
      2 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
    rw [PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hRpow2_2 : PowerSeries.coeff 2 (R ^ 2) =
      2 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ +
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2]
    ring
  have hTpow3 : PowerSeries.coeff 5 (T ^ 3) =
      3 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 2 *
        schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ +
      3 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 2
    rw [h, show R ^ 3 = R ^ 2 * R by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2, hRpow2_1, hRpow2_2]
    ring
  have hTpow4 : PowerSeries.coeff 5 (T ^ 4) =
      4 * schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 3 *
        schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 4) 4 1
    rw [h, PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hTpow5 : PowerSeries.coeff 5 (T ^ 5) =
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 5 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 5) 5 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow6 : PowerSeries.coeff 5 (T ^ 6) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 5
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
        PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) = _
  simp [hT5, hTpow2, hTpow3, hTpow4, hTpow5, hTpow6]
  have hhalf : (PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  have hthird : (PowerSeries.C ((3 : ℂ)⁻¹) : PowerSeries ℂ) * 3 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  have hquarter : (PowerSeries.C ((4 : ℂ)⁻¹) : PowerSeries ℂ) * 4 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  calc
    _ = ((PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2) *
          (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
            schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉ +
            schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ *
            schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈) +
        ((PowerSeries.C ((3 : ℂ)⁻¹) : PowerSeries ℂ) * 3) *
          (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 2 *
            schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈ +
            schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ *
            schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇ ^ 2) +
        ((PowerSeries.C ((4 : ℂ)⁻¹) : PowerSeries ℂ) * 4) *
          (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ ^ 3 *
            schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇) +
        schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀ := by ring
    _ = _ := by rw [hhalf, hthird, hquarter]; ring

end SpringerLean
