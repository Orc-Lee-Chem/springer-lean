import SpringerLean.Round112KernelFiveFourth

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Fifth outer row of the finite degree-five logarithmic kernel.
This is the coefficient identity before its five inner reads. -/
theorem schoberKernelQ5_outer_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₅ b₆ b₇ b₈ b₉ +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ +
      schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2 +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 3 *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ +
      PowerSeries.C ((5 : ℂ)⁻¹) *
        (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 5) := by
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
  have hR3 : PowerSeries.coeff 3 R =
      schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ := by
    simp [R, PowerSeries.coeff_X]
  have hR4 : PowerSeries.coeff 4 R =
      schoberKernelT5Row b₅ b₆ b₇ b₈ b₉ := by
    simp [R, PowerSeries.coeff_X]
  have hT5 : PowerSeries.coeff 5 T =
      schoberKernelT5Row b₅ b₆ b₇ b₈ b₉ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 4).trans hR4
  have hTpow2 : PowerSeries.coeff 5 (T ^ 2) =
      2 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ +
      2 * schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 3
    rw [h, pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2, hR3]
    ring
  have hRpow2_1 : PowerSeries.coeff 1 (R ^ 2) =
      2 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    rw [PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hRpow2_2 : PowerSeries.coeff 2 (R ^ 2) =
      2 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2]
    ring
  have hTpow3 : PowerSeries.coeff 5 (T ^ 3) =
      3 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
      3 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 2
    rw [h, show R ^ 3 = R ^ 2 * R by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2, hRpow2_1, hRpow2_2]
    ring
  have hTpow4 : PowerSeries.coeff 5 (T ^ 4) =
      4 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 3 *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 4) 4 1
    rw [h, PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hTpow5 : PowerSeries.coeff 5 (T ^ 5) =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 5 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 5) 5 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  change PowerSeries.coeff 5
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5) = _
  simp [hT5, hTpow2, hTpow3, hTpow4, hTpow5]
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
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
            schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ +
            schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ *
            schoberKernelT5Row b₃ b₄ b₅ b₆ b₇) +
        ((PowerSeries.C ((3 : ℂ)⁻¹) : PowerSeries ℂ) * 3) *
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
            schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
            schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
            schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2) +
        ((PowerSeries.C ((4 : ℂ)⁻¹) : PowerSeries ℂ) * 4) *
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 3 *
            schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) +
        schoberKernelT5Row b₅ b₆ b₇ b₈ b₉ := by ring
    _ = _ := by rw [hhalf, hthird, hquarter]; ring

/-- First inner read of the fifth outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_one_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 1 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = b₅ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  let R₅ := schoberKernelT5Row b₅ b₆ b₇ b₈ b₉
  have h₅ : PowerSeries.coeff 1 R₅ = b₅ := by
    simp [R₅, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT5Row]
  have hmul14 : PowerSeries.coeff 1 (R₁ * R₄) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀, h₄₀]
  have hmul23 : PowerSeries.coeff 1 (R₂ * R₃) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₂₀, h₃₀]
  have hhigh113 : PowerSeries.coeff 1 (R₁ ^ 2 * R₃) = 0 := by
    simp [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, h₁₀, h₃₀]
  have hhigh122 : PowerSeries.coeff 1 (R₁ * R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, h₁₀, h₂₀]
  have hhigh1112 : PowerSeries.coeff 1 (R₁ ^ 3 * R₂) = 0 := by
    simp [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, h₁₀, h₂₀]
  have hhigh5 : PowerSeries.coeff 1 (R₁ ^ 5) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  rw [schoberBiCoeff, schoberKernelQ5_outer_five]
  change PowerSeries.coeff 1
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]

/-- Second inner read of the fifth outer logarithmic-kernel row. -/
theorem schoberKernelQ5_coeff_two_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 2 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₆ + b₁ * b₄ + b₂ * b₃ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  let R₅ := schoberKernelT5Row b₅ b₆ b₇ b₈ b₉
  have h₅ : PowerSeries.coeff 2 R₅ = b₆ := by
    simp [R₅, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₁ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul14 : PowerSeries.coeff 2 (R₁ * R₄) = b₁ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₄₀, h₁₁, h₄₁]
  have hmul23 : PowerSeries.coeff 2 (R₂ * R₃) = b₂ * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₃₀, h₂₁, h₃₁]
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₂1 : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have hcube₁1 : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hhigh113 : PowerSeries.coeff 2 (R₁ ^ 2 * R₃) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, hsq₁1]
  have hhigh122 : PowerSeries.coeff 2 (R₁ * R₂ ^ 2) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, hsq₂1]
  have hhigh1112 : PowerSeries.coeff 2 (R₁ ^ 3 * R₂) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, hcube₁1]
  have hhigh5 : PowerSeries.coeff 2 (R₁ ^ 5) = 0 := by
    rw [show R₁ ^ 5 = (R₁ ^ 2) * (R₁ ^ 3) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hcube₁1]
  rw [schoberBiCoeff, schoberKernelQ5_outer_five]
  change PowerSeries.coeff 2
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]

/-- Third inner read of the fifth outer row, matching the previous
third-row fifth coefficient. -/
theorem schoberKernelQ5_coeff_three_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 3 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₇ + b₁ * b₅ + 2 * b₂ * b₄ + b₃ ^ 2 +
        b₁ ^ 2 * b₃ + b₁ * b₂ ^ 2 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  let R₅ := schoberKernelT5Row b₅ b₆ b₇ b₈ b₉
  have h₅ : PowerSeries.coeff 3 R₅ = b₇ := by
    simp [R₅, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₂ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₁ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₂ : PowerSeries.coeff 2 R₄ = b₅ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul14 : PowerSeries.coeff 3 (R₁ * R₄) =
      b₁ * b₅ + b₂ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₄₀, h₁₁, h₁₂, h₄₁, h₄₂]
  have hmul23 : PowerSeries.coeff 3 (R₂ * R₃) =
      b₂ * b₄ + b₃ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₃₀, h₂₁, h₂₂, h₃₁, h₃₂]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₂1 : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have hsq₁2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq₂2 : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁]
    ring
  have hhigh113 : PowerSeries.coeff 3 (R₁ ^ 2 * R₃) =
      b₁ ^ 2 * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₃₁, hsq₁1, hsq₁2]
  have hhigh122 : PowerSeries.coeff 3 (R₁ * R₂ ^ 2) =
      b₁ * b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, hsq₂1, hsq₂2]
  have hcube₁1 : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hcube₁2 : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1]
  have hhigh1112 : PowerSeries.coeff 3 (R₁ ^ 3 * R₂) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, hcube₁1, hcube₁2]
  have hhigh5 : PowerSeries.coeff 3 (R₁ ^ 5) = 0 := by
    rw [show R₁ ^ 5 = R₁ ^ 2 * R₁ ^ 3 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hcube₁1, hcube₁2]
  rw [schoberBiCoeff, schoberKernelQ5_outer_five]
  change PowerSeries.coeff 3
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]
  ring

/-- Fourth inner read of the fifth row, matching the previous
fourth-row fifth coefficient. -/
theorem schoberKernelQ5_coeff_four_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 4 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₈ + b₁ * b₆ + 2 * b₂ * b₅ + 3 * b₃ * b₄ +
        b₁ ^ 2 * b₄ + 4 * b₁ * b₂ * b₃ +
        b₂ ^ 3 + b₁ ^ 3 * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  let R₅ := schoberKernelT5Row b₅ b₆ b₇ b₈ b₉
  have h₅ : PowerSeries.coeff 4 R₅ = b₈ := by
    simp [R₅, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₃ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₂ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₃ : PowerSeries.coeff 3 R₃ = b₅ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₁ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₂ : PowerSeries.coeff 2 R₄ = b₅ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₃ : PowerSeries.coeff 3 R₄ = b₆ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul14 : PowerSeries.coeff 4 (R₁ * R₄) =
      b₁ * b₆ + b₂ * b₅ + b₃ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₄₀, h₁₁, h₁₂, h₁₃, h₄₁, h₄₂, h₄₃]
  have hmul23 : PowerSeries.coeff 4 (R₂ * R₃) =
      b₂ * b₅ + 2 * b₃ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₃₀, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₂1 : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have hsq₁2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq₁3 : PowerSeries.coeff 3 (R₁ ^ 2) =
      2 * b₁ * b₂ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂]
    ring
  have hsq₂2 : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁]
    ring
  have hsq₂3 : PowerSeries.coeff 3 (R₂ ^ 2) =
      2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂]
    ring
  have hhigh113 : PowerSeries.coeff 4 (R₁ ^ 2 * R₃) =
      b₁ ^ 2 * b₄ + 2 * b₁ * b₂ * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₃₁, h₃₂, hsq₁1, hsq₁2, hsq₁3]
  have hhigh122 : PowerSeries.coeff 4 (R₁ * R₂ ^ 2) =
      2 * b₁ * b₂ * b₃ + b₂ ^ 3 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, hsq₂1, hsq₂2, hsq₂3]
    ring
  have hcube₁1 : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hcube₁2 : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1]
  have hcube₁3 : PowerSeries.coeff 3 (R₁ ^ 3) = b₁ ^ 3 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, hsq₁1, hsq₁2]
    ring
  have hhigh1112 : PowerSeries.coeff 4 (R₁ ^ 3 * R₂) =
      b₁ ^ 3 * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, hcube₁1, hcube₁2, hcube₁3]
  have hhigh5 : PowerSeries.coeff 4 (R₁ ^ 5) = 0 := by
    rw [show R₁ ^ 5 = R₁ ^ 2 * R₁ ^ 3 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hcube₁1, hcube₁2]
  rw [schoberBiCoeff, schoberKernelQ5_outer_five]
  change PowerSeries.coeff 4
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]
  ring

/-- The central fifth-order kernel coefficient. Its twelve terms are
the exact degree-five logarithmic Grunsky diagonal before normalization. -/
theorem schoberKernelQ5_coeff_five_five
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 5 5
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₉ + b₁ * b₇ + 2 * b₂ * b₆ + 3 * b₃ * b₅ + 2 * b₄ ^ 2 +
      b₁ ^ 2 * b₅ + 4 * b₁ * b₂ * b₄ + 3 * b₁ * b₃ ^ 2 +
      4 * b₂ ^ 2 * b₃ + b₁ ^ 3 * b₃ + 3 * b₁ ^ 2 * b₂ ^ 2 +
      (5 : ℂ)⁻¹ * b₁ ^ 5 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  let R₅ := schoberKernelT5Row b₅ b₆ b₇ b₈ b₉
  have h₅ : PowerSeries.coeff 5 R₅ = b₉ := by
    simp [R₅, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₄₀ : PowerSeries.constantCoeff R₄ = 0 := by
    simp [R₄, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₃ : PowerSeries.coeff 3 R₁ = b₃ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₄ : PowerSeries.coeff 4 R₁ = b₄ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₃ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₄ : PowerSeries.coeff 4 R₂ = b₅ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₂ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₃ : PowerSeries.coeff 3 R₃ = b₅ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₄ : PowerSeries.coeff 4 R₃ = b₆ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₁ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₂ : PowerSeries.coeff 2 R₄ = b₅ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₃ : PowerSeries.coeff 3 R₄ = b₆ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₄₄ : PowerSeries.coeff 4 R₄ = b₇ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul14 : PowerSeries.coeff 5 (R₁ * R₄) =
      b₁ * b₇ + b₂ * b₆ + b₃ * b₅ + b₄ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₄₀, h₁₁, h₁₂, h₁₃, h₁₄, h₄₁, h₄₂, h₄₃, h₄₄]
    ring
  have hmul23 : PowerSeries.coeff 5 (R₂ * R₃) =
      b₂ * b₆ + 2 * b₃ * b₅ + b₄ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₃₀, h₂₁, h₂₂, h₂₃, h₂₄, h₃₁, h₃₂, h₃₃, h₃₄]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq₂1 : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have hsq₁2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hsq₁3 : PowerSeries.coeff 3 (R₁ ^ 2) =
      2 * b₁ * b₂ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂]
    ring
  have hsq₁4 : PowerSeries.coeff 4 (R₁ ^ 2) =
      2 * b₁ * b₃ + b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, h₁₃]
    ring
  have hsq₂2 : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁]
    ring
  have hsq₂3 : PowerSeries.coeff 3 (R₂ ^ 2) =
      2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂]
    ring
  have hsq₂4 : PowerSeries.coeff 4 (R₂ ^ 2) =
      2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃]
    ring
  have hhigh113 : PowerSeries.coeff 5 (R₁ ^ 2 * R₃) =
      b₁ ^ 2 * b₅ + 2 * b₁ * b₂ * b₄ +
        2 * b₁ * b₃ ^ 2 + b₂ ^ 2 * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₃₁, h₃₂, h₃₃, hsq₁1, hsq₁2, hsq₁3, hsq₁4]
    ring
  have hhigh122 : PowerSeries.coeff 5 (R₁ * R₂ ^ 2) =
      2 * b₁ * b₂ * b₄ + b₁ * b₃ ^ 2 +
        3 * b₂ ^ 2 * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₁₁, h₁₂, h₁₃, hsq₂1, hsq₂2, hsq₂3, hsq₂4]
    ring
  have hcube₁1 : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hcube₁2 : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1]
  have hcube₁3 : PowerSeries.coeff 3 (R₁ ^ 3) = b₁ ^ 3 := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, hsq₁1, hsq₁2]
    ring
  have hcube₁4 : PowerSeries.coeff 4 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₂ := by
    rw [show R₁ ^ 3 = R₁ * R₁ ^ 2 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁, h₁₂, hsq₁1, hsq₁2, hsq₁3]
    ring
  have hhigh1112 : PowerSeries.coeff 5 (R₁ ^ 3 * R₂) =
      b₁ ^ 3 * b₃ + 3 * b₁ ^ 2 * b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, h₂₂, hcube₁1, hcube₁2, hcube₁3, hcube₁4]
    ring
  have hhigh5 : PowerSeries.coeff 5 (R₁ ^ 5) = b₁ ^ 5 := by
    rw [show R₁ ^ 5 = R₁ ^ 2 * R₁ ^ 3 by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hsq₁2, hcube₁1, hcube₁2, hcube₁3]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_five]
  change PowerSeries.coeff 5
    (R₅ + R₁ * R₄ + R₂ * R₃ + R₁ ^ 2 * R₃ +
      R₁ * R₂ ^ 2 + R₁ ^ 3 * R₂ +
      PowerSeries.C ((5 : ℂ)⁻¹) * R₁ ^ 5) = _
  simp [h₅, hmul14, hmul23, hhigh113, hhigh122, hhigh1112, hhigh5]
  ring

end SpringerLean
