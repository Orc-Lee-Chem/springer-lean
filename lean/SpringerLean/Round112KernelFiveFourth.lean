import SpringerLean.Round111KernelFiveThirdEntries

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The fourth outer row of the degree-five finite logarithmic kernel.
It is the fourth coefficient of `-log(1-T)` and retains the mixed
`T₂²/2` term needed for the Faber matrix. -/
theorem schoberKernelQ5_outer_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    PowerSeries.coeff 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
      PowerSeries.C ((2 : ℂ)⁻¹) *
        (schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2) +
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ +
      PowerSeries.C ((4 : ℂ)⁻¹) *
        (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 4) := by
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
  have hT4 : PowerSeries.coeff 4 T =
      schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 3).trans hR3
  have hTpow2 : PowerSeries.coeff 4 (T ^ 2) =
      2 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
        schoberKernelT5Row b₃ b₄ b₅ b₆ b₇ +
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 2
    rw [h, pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR0, hR1, hR2]
    ring
  have hTpow3 : PowerSeries.coeff 4 (T ^ 3) =
      3 * schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
        schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 1
    rw [h, PowerSeries.coeff_one_pow]
    simp [hR0, hR1]
    ring
  have hTpow4 : PowerSeries.coeff 4 (T ^ 4) =
      schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 4 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 4) 4 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow5 : PowerSeries.coeff 4 (T ^ 5) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 4
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5) = _
  simp [hT4, hTpow2, hTpow3, hTpow4, hTpow5]
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
  calc
    _ = ((PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2) *
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ *
            schoberKernelT5Row b₃ b₄ b₅ b₆ b₇) +
        PowerSeries.C ((2 : ℂ)⁻¹) *
          schoberKernelT5Row b₂ b₃ b₄ b₅ b₆ ^ 2 +
        ((PowerSeries.C ((3 : ℂ)⁻¹) : PowerSeries ℂ) * 3) *
          (schoberKernelT5Row b₁ b₂ b₃ b₄ b₅ ^ 2 *
            schoberKernelT5Row b₂ b₃ b₄ b₅ b₆) +
        schoberKernelT5Row b₄ b₅ b₆ b₇ b₈ := by ring
    _ = _ := by rw [hhalf, hthird]; ring

/-- First inner coefficient of the fourth outer row. -/
theorem schoberKernelQ5_coeff_one_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 1 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = b₄ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  have h₄ : PowerSeries.coeff 1 R₄ = b₄ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have hmul : PowerSeries.coeff 1 (R₁ * R₃) = 0 := by
    simp [PowerSeries.coeff_one_mul, h₁₀, h₃₀]
  have hsq : PowerSeries.coeff 1 (R₂ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₂₀]
  have htwoone : PowerSeries.coeff 1 (R₁ ^ 2 * R₂) = 0 := by
    simp [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, h₁₀, h₂₀]
  have hfour : PowerSeries.coeff 1 (R₁ ^ 4) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  rw [schoberBiCoeff, schoberKernelQ5_outer_four]
  change PowerSeries.coeff 1
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq, htwoone, hfour]

/-- Second inner coefficient of the fourth outer row. -/
theorem schoberKernelQ5_coeff_two_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 2 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₅ + b₁ * b₃ + (2 : ℂ)⁻¹ * b₂ ^ 2 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  have h₄ : PowerSeries.coeff 2 R₄ = b₅ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 2 (R₁ * R₃) = b₁ * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₁₁, h₃₁]
  have hsq : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁]
    ring
  have hsq0 : PowerSeries.constantCoeff (R₁ ^ 2) = 0 := by
    simp [h₁₀]
  have hsq1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hhigh : PowerSeries.coeff 2 (R₁ ^ 2 * R₂) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq1, h₂₀]
  have hfour : PowerSeries.coeff 2 (R₁ ^ 4) = 0 := by
    rw [show R₁ ^ 4 = (R₁ ^ 2) * (R₁ ^ 2) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq1]
  rw [schoberBiCoeff, schoberKernelQ5_outer_four]
  change PowerSeries.coeff 2
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq, hhigh, hfour]

/-- Third inner coefficient of the fourth outer row, matching the
transposed third-row computation. -/
theorem schoberKernelQ5_coeff_three_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 3 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₆ + b₁ * b₄ + 2 * b₂ * b₃ + b₁ ^ 2 * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  have h₄ : PowerSeries.coeff 3 R₄ = b₆ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
  have h₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₁ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₃₂ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have hmul : PowerSeries.coeff 3 (R₁ * R₃) =
      b₁ * b₄ + b₂ * b₃ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₁₁, h₁₂, h₃₁, h₃₂]
  have hsq : PowerSeries.coeff 3 (R₂ ^ 2) = 2 * b₂ * b₃ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    have h₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
      simp [R₂, schoberKernelT5Row, PowerSeries.coeff_X_pow]
    simp [h₂₀, h₂₁, h₂₂]
    ring
  have hsq1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
  have hsq2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₁₁]
    ring
  have hhigh : PowerSeries.coeff 3 (R₁ ^ 2 * R₂) =
      b₁ ^ 2 * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, hsq1, hsq2]
  have hfour : PowerSeries.coeff 3 (R₁ ^ 4) = 0 := by
    rw [show R₁ ^ 4 = (R₁ ^ 2) * (R₁ ^ 2) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq1]
  rw [schoberBiCoeff, schoberKernelQ5_outer_four]
  change PowerSeries.coeff 3
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq, hhigh, hfour]
  ring

/-- The central fourth-order coefficient, including its quartic
normalization. -/
theorem schoberKernelQ5_coeff_four_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 4 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₇ + b₁ * b₅ + 2 * b₂ * b₄ +
        (3 : ℂ) * (2 : ℂ)⁻¹ * b₃ ^ 2 +
        b₁ ^ 2 * b₃ + 2 * b₁ * b₂ ^ 2 +
        (4 : ℂ)⁻¹ * b₁ ^ 4 := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  have h₄ : PowerSeries.coeff 4 R₄ = b₇ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
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
  have hmul : PowerSeries.coeff 4 (R₁ * R₃) =
      b₁ * b₅ + b₂ * b₄ + b₃ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₁₁, h₁₂, h₁₃, h₃₁, h₃₂, h₃₃]
    ring
  have hsq₂ : PowerSeries.coeff 4 (R₂ ^ 2) =
      2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
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
  have hhigh : PowerSeries.coeff 4 (R₁ ^ 2 * R₂) =
      b₁ ^ 2 * b₃ + 2 * b₁ * b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, h₂₂, hsq₁1, hsq₁2, hsq₁3]
    ring
  have hfour : PowerSeries.coeff 4 (R₁ ^ 4) = b₁ ^ 4 := by
    rw [show R₁ ^ 4 = (R₁ ^ 2) * (R₁ ^ 2) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hsq₁2]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_four]
  change PowerSeries.coeff 4
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq₂, hhigh, hfour]
  ring

/-- Final inner coefficient of the fourth outer row. -/
theorem schoberKernelQ5_coeff_five_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) :
    schoberBiCoeff 5 4
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
      b₈ + b₁ * b₆ + 2 * b₂ * b₅ + 3 * b₃ * b₄ +
        b₁ ^ 2 * b₄ + 4 * b₁ * b₂ * b₃ +
        b₂ ^ 3 + b₁ ^ 3 * b₂ := by
  let R₁ := schoberKernelT5Row b₁ b₂ b₃ b₄ b₅
  let R₂ := schoberKernelT5Row b₂ b₃ b₄ b₅ b₆
  let R₃ := schoberKernelT5Row b₃ b₄ b₅ b₆ b₇
  let R₄ := schoberKernelT5Row b₄ b₅ b₆ b₇ b₈
  have h₄ : PowerSeries.coeff 5 R₄ = b₈ := by
    simp [R₄, schoberKernelT5Row, PowerSeries.coeff_X_pow]
  have h₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT5Row]
  have h₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT5Row]
  have h₃₀ : PowerSeries.constantCoeff R₃ = 0 := by
    simp [R₃, schoberKernelT5Row]
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
  have hmul : PowerSeries.coeff 5 (R₁ * R₃) =
      b₁ * b₆ + b₂ * b₅ + 2 * b₃ * b₄ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₃₀, h₁₁, h₁₂, h₁₃, h₁₄, h₃₁, h₃₂, h₃₃, h₃₄]
    ring
  have hsq₂ : PowerSeries.coeff 5 (R₂ ^ 2) =
      2 * b₂ * b₅ + 2 * b₃ * b₄ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₂₀, h₂₁, h₂₂, h₂₃, h₂₄]
    ring
  have hsq₁1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h₁₀]
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
  have hhigh : PowerSeries.coeff 5 (R₁ ^ 2 * R₂) =
      b₁ ^ 2 * b₄ + 4 * b₁ * b₂ * b₃ + b₂ ^ 3 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, h₂₀, h₂₁, h₂₂, h₂₃, hsq₁1, hsq₁2, hsq₁3, hsq₁4]
    ring
  have hfour : PowerSeries.coeff 5 (R₁ ^ 4) =
      4 * b₁ ^ 3 * b₂ := by
    rw [show R₁ ^ 4 = (R₁ ^ 2) * (R₁ ^ 2) by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [h₁₀, hsq₁1, hsq₁2, hsq₁3]
    ring
  rw [schoberBiCoeff, schoberKernelQ5_outer_four]
  change PowerSeries.coeff 5
    (R₄ + R₁ * R₃ + PowerSeries.C ((2 : ℂ)⁻¹) * R₂ ^ 2 +
      R₁ ^ 2 * R₂ + PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp [h₄, hmul, hsq₂, hhigh, hfour]
  ring

end SpringerLean
