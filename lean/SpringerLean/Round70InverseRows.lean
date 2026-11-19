import SpringerLean.Round69WeightedArea

namespace SpringerLean

open PowerSeries

/-- The unit factor in the actual reciprocal inverse coordinate. -/
noncomputable def schoberReciprocalUnit (B : PowerSeries ℂ) : PowerSeries ℂ :=
  (1 - PowerSeries.X * B)⁻¹

theorem schoberReciprocalUnit_coeff_zero (B : PowerSeries ℂ) :
    PowerSeries.coeff 0 (schoberReciprocalUnit B) = 1 := by
  simp [schoberReciprocalUnit, PowerSeries.coeff_zero_eq_constantCoeff]

/-- A reusable coefficient recurrence for the reciprocal inverse coordinate. -/
theorem schoberReciprocalUnit_coeff_succ (B : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (schoberReciprocalUnit B) =
      PowerSeries.coeff n (B * schoberReciprocalUnit B) := by
  let R := schoberReciprocalUnit B
  let D : PowerSeries ℂ := 1 - PowerSeries.X * B
  have hD0 : PowerSeries.constantCoeff D ≠ 0 := by simp [D]
  have hDR : D * R = 1 := PowerSeries.mul_inv_cancel D hD0
  have hR : R = 1 + PowerSeries.X * (B * R) := by
    have h : D + PowerSeries.X * B = 1 := by simp [D]
    calc
      R = (D + PowerSeries.X * B) * R := by rw [h]; ring
      _ = 1 + PowerSeries.X * (B * R) := by
        rw [add_mul, hDR]
        ring
  change PowerSeries.coeff (n + 1) R = PowerSeries.coeff n (B * R)
  conv_lhs => rw [hR]
  simp [PowerSeries.coeff_succ_X_mul]

/-- For every degree, the formal coefficient is the Taylor coefficient of
an analytic extension that equals `(F⁻¹(1/t))⁻¹` near punctured zero. -/
theorem schoberActualPowerCoeff_eq_actualTaylorCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n j : ℕ) :
    PowerSeries.coeff n
        ((schoberReciprocalSeries (schoberActualInverseSeries F)) ^ j) =
      actualTaylorCoeff (fun t => (schoberActualReciprocalGerm F t) ^ j) n := by
  rw [← actualTaylorSeries_coeff,
    actualTaylorSeries_pow (schoberActualReciprocalGerm F)
      (schoberActualReciprocalGerm_analyticAt F hc) j,
    schoberActualReciprocalGerm_taylorSeries F hc]


/-- First reciprocal-unit coefficients for an inverse correction with zero constant term. -/
theorem schoberReciprocalUnit_coeff_one_to_four
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    PowerSeries.coeff 1 (schoberReciprocalUnit B) = 0 ∧
    PowerSeries.coeff 2 (schoberReciprocalUnit B) = PowerSeries.coeff 1 B ∧
    PowerSeries.coeff 3 (schoberReciprocalUnit B) = PowerSeries.coeff 2 B ∧
    PowerSeries.coeff 4 (schoberReciprocalUnit B) =
      PowerSeries.coeff 3 B + (PowerSeries.coeff 1 B) ^ 2 := by
  let R := schoberReciprocalUnit B
  have hR0 : PowerSeries.coeff 0 R = 1 := schoberReciprocalUnit_coeff_zero B
  have hR1 : PowerSeries.coeff 1 R = 0 := by
    have h := schoberReciprocalUnit_coeff_succ B 0
    simpa [R, PowerSeries.coeff_mul, hB0] using h
  have hR2 : PowerSeries.coeff 2 R = PowerSeries.coeff 1 B := by
    have h := schoberReciprocalUnit_coeff_succ B 1
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR1, R] at h
    exact h
  have hR3 : PowerSeries.coeff 3 R = PowerSeries.coeff 2 B := by
    have h := schoberReciprocalUnit_coeff_succ B 2
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR1, hR2, R] at h
    exact h
  have hR4 : PowerSeries.coeff 4 R =
      PowerSeries.coeff 3 B + (PowerSeries.coeff 1 B) ^ 2 := by
    have h := schoberReciprocalUnit_coeff_succ B 3
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR1, hR2, hR3, R] at h
    convert h using 1 <;> ring
  exact ⟨hR1, hR2, hR3, hR4⟩

noncomputable def schoberA (B : PowerSeries ℂ) (n j : ℕ) : ℂ :=
  PowerSeries.coeff n ((schoberReciprocalSeries B) ^ j)

theorem schoberA_shift (B : PowerSeries ℂ) (j d : ℕ) :
    schoberA B (d + j) j =
      PowerSeries.coeff d ((schoberReciprocalUnit B) ^ j) := by
  change PowerSeries.coeff (d + j)
    ((PowerSeries.X * schoberReciprocalUnit B) ^ j) = _
  rw [mul_pow]
  exact PowerSeries.coeff_X_pow_mul ((schoberReciprocalUnit B) ^ j) j d

/-- The complete fourth row, including its zero term. -/
theorem schoberA_row_four
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberA B 4 1 = PowerSeries.coeff 2 B ∧
    schoberA B 4 2 = 2 * PowerSeries.coeff 1 B ∧
    schoberA B 4 3 = 0 ∧
    schoberA B 4 4 = 1 := by
  let R := schoberReciprocalUnit B
  have hR := schoberReciprocalUnit_coeff_one_to_four B hB0
  have hR0 : PowerSeries.constantCoeff R = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberReciprocalUnit_coeff_zero B
  constructor
  · simpa only [show 4 = 3 + 1 by omega, schoberA_shift, pow_one] using hR.2.2.1
  constructor
  · rw [show 4 = 2 + 2 by omega, schoberA_shift, pow_two,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1, R]
    ring
  constructor
  · rw [show 4 = 1 + 3 by omega, schoberA_shift, PowerSeries.coeff_one_pow]
    simp [hR.1]
  · rw [show 4 = 0 + 4 by omega, schoberA_shift,
      PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.constantCoeff (R ^ 4) = 1
    simp [hR0]

/-- The complete fifth row, including the zero before the terminal one. -/
theorem schoberA_row_five
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberA B 5 1 = PowerSeries.coeff 3 B + (PowerSeries.coeff 1 B) ^ 2 ∧
    schoberA B 5 2 = 2 * PowerSeries.coeff 2 B ∧
    schoberA B 5 3 = 3 * PowerSeries.coeff 1 B ∧
    schoberA B 5 4 = 0 ∧
    schoberA B 5 5 = 1 := by
  let R := schoberReciprocalUnit B
  have hR := schoberReciprocalUnit_coeff_one_to_four B hB0
  have hR0 : PowerSeries.constantCoeff R = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberReciprocalUnit_coeff_zero B
  have hR2pow : PowerSeries.coeff 2 (R ^ 2) =
      2 * PowerSeries.coeff 1 B := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1, R]
    ring
  have hR3pow : PowerSeries.coeff 3 (R ^ 2) =
      2 * PowerSeries.coeff 2 B := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
      hR.2.2.1, R]
    ring
  have hR3cube : PowerSeries.coeff 2 (R ^ 3) =
      3 * PowerSeries.coeff 1 B := by
    rw [show R ^ 3 = R ^ 2 * R by ring, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1, hR2pow, R]
    ring
  constructor
  · simpa only [show 5 = 4 + 1 by omega, schoberA_shift, pow_one] using hR.2.2.2
  constructor
  · simpa only [show 5 = 3 + 2 by omega, schoberA_shift] using hR3pow
  constructor
  · simpa only [show 5 = 2 + 3 by omega, schoberA_shift] using hR3cube
  constructor
  · rw [show 5 = 1 + 4 by omega, schoberA_shift, PowerSeries.coeff_one_pow]
    simp [hR.1]
  · rw [show 5 = 0 + 5 by omega, schoberA_shift,
      PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.constantCoeff (R ^ 5) = 1
    simp [hR0]

/-- Reciprocal-unit coefficients needed by the rows up to eight. -/
theorem schoberReciprocalUnit_coeff_five_to_seven
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    PowerSeries.coeff 5 (schoberReciprocalUnit B) =
      PowerSeries.coeff 4 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 2 B ∧
    PowerSeries.coeff 6 (schoberReciprocalUnit B) =
      PowerSeries.coeff 5 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 3 B +
        (PowerSeries.coeff 2 B) ^ 2 + (PowerSeries.coeff 1 B) ^ 3 ∧
    PowerSeries.coeff 7 (schoberReciprocalUnit B) =
      PowerSeries.coeff 6 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 4 B +
        2 * PowerSeries.coeff 2 B * PowerSeries.coeff 3 B +
        3 * (PowerSeries.coeff 1 B) ^ 2 * PowerSeries.coeff 2 B := by
  let R := schoberReciprocalUnit B
  have hR0 : PowerSeries.coeff 0 R = 1 := schoberReciprocalUnit_coeff_zero B
  have hR := schoberReciprocalUnit_coeff_one_to_four B hB0
  have hR5 : PowerSeries.coeff 5 R =
      PowerSeries.coeff 4 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 2 B := by
    have h := schoberReciprocalUnit_coeff_succ B 4
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR.1,
      hR.2.1, hR.2.2.1, hR.2.2.2, R] at h
    convert h using 1 <;> ring
  have hR6 : PowerSeries.coeff 6 R =
      PowerSeries.coeff 5 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 3 B +
        (PowerSeries.coeff 2 B) ^ 2 + (PowerSeries.coeff 1 B) ^ 3 := by
    have h := schoberReciprocalUnit_coeff_succ B 5
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR.1,
      hR.2.1, hR.2.2.1, hR.2.2.2, hR5, R] at h
    convert h using 1 <;> ring
  have hR7 : PowerSeries.coeff 7 R =
      PowerSeries.coeff 6 B + 2 * PowerSeries.coeff 1 B * PowerSeries.coeff 4 B +
        2 * PowerSeries.coeff 2 B * PowerSeries.coeff 3 B +
        3 * (PowerSeries.coeff 1 B) ^ 2 * PowerSeries.coeff 2 B := by
    have h := schoberReciprocalUnit_coeff_succ B 6
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hB0, hR0, hR.1,
      hR.2.1, hR.2.2.1, hR.2.2.2, hR5, hR6, R] at h
    convert h using 1 <;> ring
  exact ⟨hR5, hR6, hR7⟩
end SpringerLean