import SpringerLean.Round98FaberMatrix

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Four inner coefficients are enough for every bivariate kernel entry
with both indices at most four. -/
noncomputable def schoberKernelT4Row
    (a b c d : ℂ) : PowerSeries ℂ :=
  PowerSeries.C a * PowerSeries.X +
  PowerSeries.C b * PowerSeries.X ^ 2 +
  PowerSeries.C c * PowerSeries.X ^ 3 +
  PowerSeries.C d * PowerSeries.X ^ 4

noncomputable def schoberKernelT4
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.X * PowerSeries.C (schoberKernelT4Row b₁ b₂ b₃ b₄) +
  PowerSeries.X ^ 2 * PowerSeries.C (schoberKernelT4Row b₂ b₃ b₄ b₅) +
  PowerSeries.X ^ 3 * PowerSeries.C (schoberKernelT4Row b₃ b₄ b₅ b₆) +
  PowerSeries.X ^ 4 * PowerSeries.C (schoberKernelT4Row b₄ b₅ b₆ b₇)

/-- Truncated `-log(1-T)` in the two reciprocal variables. Terms above
degree four cannot contribute to a coefficient with either index ≤4. -/
noncomputable def schoberKernelQ4
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) : PowerSeries (PowerSeries ℂ) :=
  let T := schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4

private noncomputable def schoberKernelR4
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.C (schoberKernelT4Row b₁ b₂ b₃ b₄) +
  PowerSeries.X * PowerSeries.C (schoberKernelT4Row b₂ b₃ b₄ b₅) +
  PowerSeries.X ^ 2 * PowerSeries.C (schoberKernelT4Row b₃ b₄ b₅ b₆) +
  PowerSeries.X ^ 3 * PowerSeries.C (schoberKernelT4Row b₄ b₅ b₆ b₇)

private theorem schoberKernelT4_eq_X_mul_R4
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇ =
      PowerSeries.X * schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  unfold schoberKernelT4 schoberKernelR4
  ring

private theorem schoberKernelR4_coeff_zero
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.constantCoeff
      (schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₁ b₂ b₃ b₄ := by
  simp [schoberKernelR4]

private theorem schoberKernelR4_coeff_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₂ b₃ b₄ b₅ := by
  simp [schoberKernelR4, PowerSeries.coeff_X]

private theorem schoberKernelR4_coeff_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 2
      (schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₃ b₄ b₅ b₆ := by
  simp [schoberKernelR4, PowerSeries.coeff_X]

private theorem schoberKernelR4_coeff_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 3
      (schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₄ b₅ b₆ b₇ := by
  simp [schoberKernelR4, PowerSeries.coeff_X]

private theorem schoberKernelR4_square_coeff_two
    (R : PowerSeries (PowerSeries ℂ)) :
    PowerSeries.coeff 2 (R ^ 2) =
      2 * PowerSeries.coeff 0 R * PowerSeries.coeff 2 R +
        (PowerSeries.coeff 1 R) ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem schoberKernelR4_cube_coeff_one
    (R : PowerSeries (PowerSeries ℂ)) :
    PowerSeries.coeff 1 (R ^ 3) =
      3 * (PowerSeries.coeff 0 R) ^ 2 * PowerSeries.coeff 1 R := by
  rw [PowerSeries.coeff_one_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

/-- The whole fourth outer logarithmic-kernel row before inner coefficient
extraction. This is the finite algebraic identity needed to identify the
fourth Faber factor with four Grunsky coefficients. -/
theorem schoberKernelQ4_outer_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 4
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₄ b₅ b₆ b₇ +
      PowerSeries.C ((2 : ℂ)⁻¹) *
        (2 * schoberKernelT4Row b₁ b₂ b₃ b₄ *
          schoberKernelT4Row b₃ b₄ b₅ b₆ +
          (schoberKernelT4Row b₂ b₃ b₄ b₅) ^ 2) +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        (3 * (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 2 *
          schoberKernelT4Row b₂ b₃ b₄ b₅) +
      PowerSeries.C ((4 : ℂ)⁻¹) *
        (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 4 := by
  let T := schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  let R := schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT : T = PowerSeries.X * R :=
    schoberKernelT4_eq_X_mul_R4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR0 : PowerSeries.coeff 0 R =
      schoberKernelT4Row b₁ b₂ b₃ b₄ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberKernelR4_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT4Row b₂ b₃ b₄ b₅ :=
    schoberKernelR4_coeff_one b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR2 : PowerSeries.coeff 2 R =
      schoberKernelT4Row b₃ b₄ b₅ b₆ :=
    schoberKernelR4_coeff_two b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR3 : PowerSeries.coeff 3 R =
      schoberKernelT4Row b₄ b₅ b₆ b₇ :=
    schoberKernelR4_coeff_three b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT4 : PowerSeries.coeff 4 T =
      schoberKernelT4Row b₄ b₅ b₆ b₇ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 3).trans hR3
  have hT2 : PowerSeries.coeff 4 (T ^ 2) =
      2 * schoberKernelT4Row b₁ b₂ b₃ b₄ *
        schoberKernelT4Row b₃ b₄ b₅ b₆ +
        (schoberKernelT4Row b₂ b₃ b₄ b₅) ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 2
    have hsq := schoberKernelR4_square_coeff_two R
    rw [hR0, hR1, hR2] at hsq
    simpa only [Nat.reduceAdd] using h.trans hsq
  have hT3 : PowerSeries.coeff 4 (T ^ 3) =
      3 * (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 2 *
        schoberKernelT4Row b₂ b₃ b₄ b₅ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 1
    have hcube := schoberKernelR4_cube_coeff_one R
    rw [hR0, hR1] at hcube
    simpa only [Nat.reduceAdd] using h.trans hcube
  have hT4pow : PowerSeries.coeff 4 (T ^ 4) =
      (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 4 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 4) 4 0
    have hzero : PowerSeries.coeff 0 (R ^ 4) =
        (PowerSeries.coeff 0 R) ^ 4 := by
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
    rw [hR0] at hzero
    simpa only [Nat.add_zero] using h.trans hzero
  change PowerSeries.coeff 4
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4) = _
  simp [hT4, hT2, hT3, hT4pow]

/-- First inner entry of the fourth outer logarithmic-kernel row. The
`schoberBiCoeff` convention reads the inner index first. -/
theorem schoberKernelQ4_coeff_one_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 1 4
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) = b₄ := by
  rw [schoberBiCoeff, schoberKernelQ4_outer_four]
  simp [schoberKernelT4Row, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow]

private theorem schoberKernelT4Row_const (a b c d : ℂ) :
    PowerSeries.constantCoeff (schoberKernelT4Row a b c d) = 0 := by
  simp [schoberKernelT4Row]

private theorem schoberKernelT4Row_coeff_one (a b c d : ℂ) :
    PowerSeries.coeff 1 (schoberKernelT4Row a b c d) = a := by
  simp [schoberKernelT4Row]

private theorem schoberKernelT4Row_coeff_two (a b c d : ℂ) :
    PowerSeries.coeff 2 (schoberKernelT4Row a b c d) = b := by
  simp [schoberKernelT4Row]

private theorem schoberKernelT4Row_product_coeff_two
    (a b c d e f g h : ℂ) :
    PowerSeries.coeff 2
      (schoberKernelT4Row a b c d * schoberKernelT4Row e f g h) = a * e := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, schoberKernelT4Row_const,
    schoberKernelT4Row_coeff_one]

private theorem schober_coeff_two_mul_of_low_zero
    (A B : PowerSeries ℂ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hA1 : PowerSeries.coeff 1 A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 2 (A * B) = 0 := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, hA0, hA1, hB0]

private theorem schoberKernelT4Row_cube_coeff_two_zero
    (a b c d : ℂ) :
    PowerSeries.coeff 2 ((schoberKernelT4Row a b c d) ^ 3) = 0 := by
  let A := schoberKernelT4Row a b c d
  have hA0 : PowerSeries.constantCoeff A = 0 :=
    schoberKernelT4Row_const a b c d
  have hA20 : PowerSeries.constantCoeff (A ^ 2) = 0 := by
    simp [hA0]
  have hA21 : PowerSeries.coeff 1 (A ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, hA0]
  change PowerSeries.coeff 2 (A ^ 2 * A) = 0
  exact schober_coeff_two_mul_of_low_zero (A ^ 2) A hA20 hA21 hA0

private theorem schoberKernelT4Row_fourth_coeff_two_zero
    (a b c d : ℂ) :
    PowerSeries.coeff 2 ((schoberKernelT4Row a b c d) ^ 4) = 0 := by
  let A := schoberKernelT4Row a b c d
  have hA0 : PowerSeries.constantCoeff A = 0 :=
    schoberKernelT4Row_const a b c d
  have hA20 : PowerSeries.constantCoeff (A ^ 2) = 0 := by
    simp [hA0]
  have hA21 : PowerSeries.coeff 1 (A ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, hA0]
  rw [show A ^ 4 = A ^ 2 * A ^ 2 by ring]
  exact schober_coeff_two_mul_of_low_zero (A ^ 2) (A ^ 2) hA20 hA21 hA20

/-- Second inner entry of the fourth outer row. Its half-square term is
the first nonlinear contribution and matches the fourth Faber mode at 6. -/
theorem schoberKernelQ4_coeff_two_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 2 4
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₅ + b₁ * b₃ + (2 : ℂ)⁻¹ * b₂ ^ 2 := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  let R₄ := schoberKernelT4Row b₄ b₅ b₆ b₇
  have hR4 : PowerSeries.coeff 2 R₄ = b₅ :=
    schoberKernelT4Row_coeff_two b₄ b₅ b₆ b₇
  have h13 : PowerSeries.coeff 2 (R₁ * R₃) = b₁ * b₃ :=
    schoberKernelT4Row_product_coeff_two
      b₁ b₂ b₃ b₄ b₃ b₄ b₅ b₆
  have h22 : PowerSeries.coeff 2 (R₂ ^ 2) = b₂ ^ 2 := by
    rw [pow_two, schoberKernelT4Row_product_coeff_two]
    ring
  have h112 : PowerSeries.coeff 2 (R₁ ^ 2 * R₂) = 0 := by
    have h10 : PowerSeries.constantCoeff R₁ = 0 :=
      schoberKernelT4Row_const b₁ b₂ b₃ b₄
    have h20 : PowerSeries.constantCoeff R₂ = 0 :=
      schoberKernelT4Row_const b₂ b₃ b₄ b₅
    have hA0 : PowerSeries.constantCoeff (R₁ ^ 2) = 0 := by simp [h10]
    have hA1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
      simp [PowerSeries.coeff_one_pow, h10]
    exact schober_coeff_two_mul_of_low_zero (R₁ ^ 2) R₂ hA0 hA1 h20
  have h1111 : PowerSeries.coeff 2 (R₁ ^ 4) = 0 :=
    schoberKernelT4Row_fourth_coeff_two_zero b₁ b₂ b₃ b₄
  have htwice : PowerSeries.coeff 2 ((2 : PowerSeries ℂ) * R₁ * R₃) =
      2 * b₁ * b₃ := by
    rw [show (2 : PowerSeries ℂ) * R₁ * R₃ =
      R₁ * R₃ + R₁ * R₃ by ring]
    simp [h13]
    ring
  have hthrice : PowerSeries.coeff 2 ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) = 0 := by
    rw [show (3 : PowerSeries ℂ) * R₁ ^ 2 * R₂ =
      R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ by ring]
    simp [h112]
  rw [schoberBiCoeff, schoberKernelQ4_outer_four]
  change PowerSeries.coeff 2
    (R₄ + PowerSeries.C ((2 : ℂ)⁻¹) *
      ((2 : PowerSeries ℂ) * R₁ * R₃ + R₂ ^ 2) +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) +
      PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp only [map_add, PowerSeries.coeff_C_mul]
  rw [hR4, htwice, h22, hthrice, h1111]
  ring

private theorem schober_coeff_three_mul_of_const_zero
    (A B : PowerSeries ℂ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 3 (A * B) =
      PowerSeries.coeff 1 A * PowerSeries.coeff 2 B +
        PowerSeries.coeff 2 A * PowerSeries.coeff 1 B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, hA0, hB0]

private theorem schoberKernelT4Row_coeff_three (a b c d : ℂ) :
    PowerSeries.coeff 3 (schoberKernelT4Row a b c d) = c := by
  simp [schoberKernelT4Row]

/-- The third inner coefficient of the same fourth outer row. -/
theorem schoberKernelQ4_coeff_three_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 3 4
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₆ + b₁ * b₄ + 2 * b₂ * b₃ + b₁ ^ 2 * b₂ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  let R₄ := schoberKernelT4Row b₄ b₅ b₆ b₇
  have h10 : PowerSeries.constantCoeff R₁ = 0 :=
    schoberKernelT4Row_const b₁ b₂ b₃ b₄
  have h20 : PowerSeries.constantCoeff R₂ = 0 :=
    schoberKernelT4Row_const b₂ b₃ b₄ b₅
  have h30 : PowerSeries.constantCoeff R₃ = 0 :=
    schoberKernelT4Row_const b₃ b₄ b₅ b₆
  have hR4 : PowerSeries.coeff 3 R₄ = b₆ :=
    schoberKernelT4Row_coeff_three b₄ b₅ b₆ b₇
  have h13 : PowerSeries.coeff 3 (R₁ * R₃) =
      b₁ * b₄ + b₂ * b₃ := by
    rw [schober_coeff_three_mul_of_const_zero R₁ R₃ h10 h30]
    simp [R₁, R₃, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
  have h22 : PowerSeries.coeff 3 (R₂ ^ 2) = 2 * b₂ * b₃ := by
    rw [pow_two,
      schober_coeff_three_mul_of_const_zero R₂ R₂ h20 h20,
      schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
    ring
  have hA0 : PowerSeries.constantCoeff (R₁ ^ 2) = 0 := by simp [h10]
  have hA1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h10]
  have hA2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, schoberKernelT4Row_product_coeff_two]
    ring
  have h112 : PowerSeries.coeff 3 (R₁ ^ 2 * R₂) = b₁ ^ 2 * b₂ := by
    rw [schober_coeff_three_mul_of_const_zero (R₁ ^ 2) R₂ hA0 h20,
      hA1, hA2, schoberKernelT4Row_coeff_one]
    ring
  have h1111 : PowerSeries.coeff 3 (R₁ ^ 4) = 0 := by
    rw [show R₁ ^ 4 = R₁ ^ 2 * R₁ ^ 2 by ring,
      schober_coeff_three_mul_of_const_zero (R₁ ^ 2) (R₁ ^ 2) hA0 hA0,
      hA1]
    ring
  have htwice : PowerSeries.coeff 3 ((2 : PowerSeries ℂ) * R₁ * R₃) =
      2 * (b₁ * b₄ + b₂ * b₃) := by
    rw [show (2 : PowerSeries ℂ) * R₁ * R₃ =
      R₁ * R₃ + R₁ * R₃ by ring]
    simp [h13]
    ring
  have hthrice : PowerSeries.coeff 3 ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) =
      3 * b₁ ^ 2 * b₂ := by
    rw [show (3 : PowerSeries ℂ) * R₁ ^ 2 * R₂ =
      R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ by ring]
    simp [h112]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_four]
  change PowerSeries.coeff 3
    (R₄ + PowerSeries.C ((2 : ℂ)⁻¹) *
      ((2 : PowerSeries ℂ) * R₁ * R₃ + R₂ ^ 2) +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) +
      PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp only [map_add, PowerSeries.coeff_C_mul]
  rw [hR4, htwice, h22, hthrice, h1111]
  ring

private theorem schober_coeff_four_mul_of_const_zero
    (A B : PowerSeries ℂ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 4 (A * B) =
      PowerSeries.coeff 1 A * PowerSeries.coeff 3 B +
      PowerSeries.coeff 2 A * PowerSeries.coeff 2 B +
      PowerSeries.coeff 3 A * PowerSeries.coeff 1 B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, hA0, hB0]

private theorem schoberKernelT4Row_coeff_four (a b c d : ℂ) :
    PowerSeries.coeff 4 (schoberKernelT4Row a b c d) = d := by
  simp [schoberKernelT4Row]

/-- Fourth inner entry and diagonal coefficient of the degree-four
truncated logarithmic kernel. -/
theorem schoberKernelQ4_coeff_four_four
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 4 4
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₇ + b₁ * b₅ + 2 * b₂ * b₄ +
      (3 : ℂ) / 2 * b₃ ^ 2 + b₁ ^ 2 * b₃ +
      2 * b₁ * b₂ ^ 2 + (4 : ℂ)⁻¹ * b₁ ^ 4 := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  let R₄ := schoberKernelT4Row b₄ b₅ b₆ b₇
  have h10 : PowerSeries.constantCoeff R₁ = 0 :=
    schoberKernelT4Row_const b₁ b₂ b₃ b₄
  have h20 : PowerSeries.constantCoeff R₂ = 0 :=
    schoberKernelT4Row_const b₂ b₃ b₄ b₅
  have h30 : PowerSeries.constantCoeff R₃ = 0 :=
    schoberKernelT4Row_const b₃ b₄ b₅ b₆
  have hR4 : PowerSeries.coeff 4 R₄ = b₇ :=
    schoberKernelT4Row_coeff_four b₄ b₅ b₆ b₇
  have h13 : PowerSeries.coeff 4 (R₁ * R₃) =
      b₁ * b₅ + b₂ * b₄ + b₃ ^ 2 := by
    rw [schober_coeff_four_mul_of_const_zero R₁ R₃ h10 h30]
    simp [R₁, R₃, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two, schoberKernelT4Row_coeff_three]
    ring
  have h22 : PowerSeries.coeff 4 (R₂ ^ 2) =
      2 * b₂ * b₄ + b₃ ^ 2 := by
    rw [pow_two, schober_coeff_four_mul_of_const_zero R₂ R₂ h20 h20]
    simp [R₂, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two, schoberKernelT4Row_coeff_three]
    ring
  have hA0 : PowerSeries.constantCoeff (R₁ ^ 2) = 0 := by simp [h10]
  have hA1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h10]
  have hA2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, schoberKernelT4Row_product_coeff_two]
    ring
  have hA3 : PowerSeries.coeff 3 (R₁ ^ 2) = 2 * b₁ * b₂ := by
    rw [pow_two, schober_coeff_three_mul_of_const_zero R₁ R₁ h10 h10]
    simp [R₁, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
    ring
  have h112 : PowerSeries.coeff 4 (R₁ ^ 2 * R₂) =
      b₁ ^ 2 * b₃ + 2 * b₁ * b₂ ^ 2 := by
    rw [schober_coeff_four_mul_of_const_zero (R₁ ^ 2) R₂ hA0 h20,
      hA1, hA2, hA3]
    simp [R₂, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
    ring
  have h1111 : PowerSeries.coeff 4 (R₁ ^ 4) = b₁ ^ 4 := by
    rw [show R₁ ^ 4 = R₁ ^ 2 * R₁ ^ 2 by ring,
      schober_coeff_four_mul_of_const_zero (R₁ ^ 2) (R₁ ^ 2) hA0 hA0,
      hA1, hA2]
    ring
  have htwice : PowerSeries.coeff 4 ((2 : PowerSeries ℂ) * R₁ * R₃) =
      2 * (b₁ * b₅ + b₂ * b₄ + b₃ ^ 2) := by
    rw [show (2 : PowerSeries ℂ) * R₁ * R₃ =
      R₁ * R₃ + R₁ * R₃ by ring]
    simp [h13]
    ring
  have hthrice : PowerSeries.coeff 4 ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) =
      3 * (b₁ ^ 2 * b₃ + 2 * b₁ * b₂ ^ 2) := by
    rw [show (3 : PowerSeries ℂ) * R₁ ^ 2 * R₂ =
      R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ + R₁ ^ 2 * R₂ by ring]
    simp [h112]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_four]
  change PowerSeries.coeff 4
    (R₄ + PowerSeries.C ((2 : ℂ)⁻¹) *
      ((2 : PowerSeries ℂ) * R₁ * R₃ + R₂ ^ 2) +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        ((3 : PowerSeries ℂ) * R₁ ^ 2 * R₂) +
      PowerSeries.C ((4 : ℂ)⁻¹) * R₁ ^ 4) = _
  simp only [map_add, PowerSeries.coeff_C_mul]
  rw [hR4, htwice, h22, hthrice, h1111]
  ring

/-- The entire fourth row of the actual Faber factor agrees, coefficient
by coefficient, with four times the finite logarithmic-kernel row of the
same actual map. This removes the fourth-row index/sign ambiguity. -/
theorem fourthFaberFactor_actual_modes_eq_logKernel4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let Q := schoberKernelQ4
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
      (exteriorForwardCoeff F 7)
    actualTaylorCoeff (fourthFaberFactor F) 5 =
      4 * schoberBiCoeff 1 4 Q ∧
    actualTaylorCoeff (fourthFaberFactor F) 6 =
      4 * schoberBiCoeff 2 4 Q ∧
    actualTaylorCoeff (fourthFaberFactor F) 7 =
      4 * schoberBiCoeff 3 4 Q ∧
    actualTaylorCoeff (fourthFaberFactor F) 8 =
      4 * schoberBiCoeff 4 4 Q := by
  dsimp only
  constructor
  · have h5 := fourthFaberFactor_actual_mode_five F hc
    change actualTaylorCoeff (fourthFaberFactor F) 5 =
      4 * exteriorForwardCoeff F 4 at h5
    rw [h5, schoberKernelQ4_coeff_one_four]
  constructor
  · rw [fourthFaberFactor_actual_mode_six F hc,
      schoberKernelQ4_coeff_two_four]
    norm_num
    ring
  constructor
  · rw [fourthFaberFactor_actual_mode_seven F hc,
      schoberKernelQ4_coeff_three_four]
    ring
  · rw [fourthFaberFactor_actual_mode_eight F hc,
      schoberKernelQ4_coeff_four_four]
    norm_num
    ring

/-- The first outer row of the same degree-four logarithmic kernel. -/
theorem schoberKernelQ4_outer_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₁ b₂ b₃ b₄ := by
  let T := schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  let R := schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT : T = PowerSeries.X * R :=
    schoberKernelT4_eq_X_mul_R4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT0 : PowerSeries.constantCoeff T = 0 := by
    rw [hT]
    simp
  have hT1 : PowerSeries.coeff 1 T =
      schoberKernelT4Row b₁ b₂ b₃ b₄ := by
    rw [hT]
    have hR0 : PowerSeries.coeff 0 R =
        schoberKernelT4Row b₁ b₂ b₃ b₄ := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
        (schoberKernelR4_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇)
    simpa only [pow_one, Nat.reduceAdd,
      PowerSeries.coeff_zero_eq_constantCoeff] using
      (PowerSeries.coeff_X_pow_mul R 1 0).trans hR0
  change PowerSeries.coeff 1
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4) = _
  simp [PowerSeries.coeff_one_pow, hT0, hT1]

theorem schoberKernelQ4_outer_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 2
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₂ b₃ b₄ b₅ +
        PowerSeries.C ((2 : ℂ)⁻¹) *
          (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 2 := by
  let T := schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  let R := schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT : T = PowerSeries.X * R :=
    schoberKernelT4_eq_X_mul_R4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT4Row b₁ b₂ b₃ b₄ :=
    schoberKernelR4_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT4Row b₂ b₃ b₄ b₅ :=
    schoberKernelR4_coeff_one b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT2 : PowerSeries.coeff 2 T =
      schoberKernelT4Row b₂ b₃ b₄ b₅ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 1).trans hR1
  have hTpow2 : PowerSeries.coeff 2 (T ^ 2) =
      (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow3 : PowerSeries.coeff 2 (T ^ 3) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  have hTpow4 : PowerSeries.coeff 2 (T ^ 4) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 2
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4) = _
  simp [hT2, hTpow2, hTpow3, hTpow4]

theorem schoberKernelQ4_outer_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    PowerSeries.coeff 3
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      schoberKernelT4Row b₃ b₄ b₅ b₆ +
      schoberKernelT4Row b₁ b₂ b₃ b₄ *
        schoberKernelT4Row b₂ b₃ b₄ b₅ +
      PowerSeries.C ((3 : ℂ)⁻¹) *
        (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 3 := by
  let T := schoberKernelT4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  let R := schoberKernelR4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT : T = PowerSeries.X * R :=
    schoberKernelT4_eq_X_mul_R4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR0 : PowerSeries.constantCoeff R =
      schoberKernelT4Row b₁ b₂ b₃ b₄ :=
    schoberKernelR4_coeff_zero b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR1 : PowerSeries.coeff 1 R =
      schoberKernelT4Row b₂ b₃ b₄ b₅ :=
    schoberKernelR4_coeff_one b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hR2 : PowerSeries.coeff 2 R =
      schoberKernelT4Row b₃ b₄ b₅ b₆ :=
    schoberKernelR4_coeff_two b₁ b₂ b₃ b₄ b₅ b₆ b₇
  have hT3 : PowerSeries.coeff 3 T =
      schoberKernelT4Row b₃ b₄ b₅ b₆ := by
    rw [hT]
    simpa only [pow_one, Nat.reduceAdd] using
      (PowerSeries.coeff_X_pow_mul R 1 2).trans hR2
  have hTpow2 : PowerSeries.coeff 3 (T ^ 2) =
      2 * schoberKernelT4Row b₁ b₂ b₃ b₄ *
        schoberKernelT4Row b₂ b₃ b₄ b₅ := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 1
    have hfirst : PowerSeries.coeff 1 (R ^ 2) =
        2 * schoberKernelT4Row b₁ b₂ b₃ b₄ *
          schoberKernelT4Row b₂ b₃ b₄ b₅ := by
      rw [PowerSeries.coeff_one_pow]
      simp only [hR0, hR1]
      ring
    simpa only [Nat.reduceAdd] using h.trans hfirst
  have hTpow3 : PowerSeries.coeff 3 (T ^ 3) =
      (schoberKernelT4Row b₁ b₂ b₃ b₄) ^ 3 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hTpow4 : PowerSeries.coeff 3 (T ^ 4) = 0 := by
    rw [hT, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  change PowerSeries.coeff 3
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4) = _
  simp [hT3, hTpow2, hTpow3, hTpow4]
  have hhalf : (PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  calc
    _ = ((PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2) *
        (schoberKernelT4Row b₁ b₂ b₃ b₄ *
          schoberKernelT4Row b₂ b₃ b₄ b₅) := by ring
    _ = _ := by rw [hhalf]; ring

/-- The fourth inner entry of the second outer row agrees with the
already verified fourth outer row's second inner entry. -/
theorem schoberKernelQ4_coeff_four_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 4 2
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₅ + b₁ * b₃ + (2 : ℂ)⁻¹ * b₂ ^ 2 := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  have hR2 : PowerSeries.coeff 4 R₂ = b₅ :=
    schoberKernelT4Row_coeff_four b₂ b₃ b₄ b₅
  have h10 : PowerSeries.constantCoeff R₁ = 0 :=
    schoberKernelT4Row_const b₁ b₂ b₃ b₄
  have hsq : PowerSeries.coeff 4 (R₁ ^ 2) =
      2 * b₁ * b₃ + b₂ ^ 2 := by
    rw [pow_two, schober_coeff_four_mul_of_const_zero R₁ R₁ h10 h10]
    simp [R₁, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two, schoberKernelT4Row_coeff_three]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_two]
  change PowerSeries.coeff 4
    (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp only [map_add, PowerSeries.coeff_C_mul]
  rw [hR2, hsq]
  ring

theorem schoberKernelQ4_coeff_four_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 4 3
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₆ + b₁ * b₄ + 2 * b₂ * b₃ + b₁ ^ 2 * b₂ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  have hR3 : PowerSeries.coeff 4 R₃ = b₆ :=
    schoberKernelT4Row_coeff_four b₃ b₄ b₅ b₆
  have h10 : PowerSeries.constantCoeff R₁ = 0 :=
    schoberKernelT4Row_const b₁ b₂ b₃ b₄
  have h20 : PowerSeries.constantCoeff R₂ = 0 :=
    schoberKernelT4Row_const b₂ b₃ b₄ b₅
  have hprod : PowerSeries.coeff 4 (R₁ * R₂) =
      b₁ * b₄ + 2 * b₂ * b₃ := by
    rw [schober_coeff_four_mul_of_const_zero R₁ R₂ h10 h20]
    simp [R₁, R₂, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two, schoberKernelT4Row_coeff_three]
    ring
  have hA0 : PowerSeries.constantCoeff (R₁ ^ 2) = 0 := by simp [h10]
  have hA1 : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, h10]
  have hA2 : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, schoberKernelT4Row_product_coeff_two]
    ring
  have hA3 : PowerSeries.coeff 3 (R₁ ^ 2) = 2 * b₁ * b₂ := by
    rw [pow_two, schober_coeff_three_mul_of_const_zero R₁ R₁ h10 h10]
    simp [R₁, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
    ring
  have hcube : PowerSeries.coeff 4 (R₁ ^ 3) =
      3 * b₁ ^ 2 * b₂ := by
    change PowerSeries.coeff 4 (R₁ ^ 2 * R₁) = _
    rw [schober_coeff_four_mul_of_const_zero (R₁ ^ 2) R₁ hA0 h10,
      hA1, hA2, hA3]
    simp [R₁, schoberKernelT4Row_coeff_one,
      schoberKernelT4Row_coeff_two]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_three]
  change PowerSeries.coeff 4
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp only [map_add, PowerSeries.coeff_C_mul]
  rw [hR3, hprod, hcube]
  ring

theorem schoberKernelQ4_coeff_four_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 4 1
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) = b₄ := by
  rw [schoberBiCoeff, schoberKernelQ4_outer_one]
  simp [schoberKernelT4Row]

/-- Symmetry of every entry involving the fourth index, proved from the
actual finite-kernel formulas rather than assumed from a formal transpose. -/
theorem schoberKernelQ4_last_row_column_symm
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    let Q := schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
    schoberBiCoeff 1 4 Q = schoberBiCoeff 4 1 Q ∧
    schoberBiCoeff 2 4 Q = schoberBiCoeff 4 2 Q ∧
    schoberBiCoeff 3 4 Q = schoberBiCoeff 4 3 Q := by
  dsimp only
  constructor
  · rw [schoberKernelQ4_coeff_one_four,
      schoberKernelQ4_coeff_four_one]
  constructor
  · rw [schoberKernelQ4_coeff_two_four,
      schoberKernelQ4_coeff_four_two]
  · rw [schoberKernelQ4_coeff_three_four,
      schoberKernelQ4_coeff_four_three]

end SpringerLean
