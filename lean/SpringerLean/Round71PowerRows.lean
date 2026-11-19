import SpringerLean.Round70InverseRows

namespace SpringerLean

open PowerSeries

/-- Low-degree coefficients of powers of the reciprocal unit factor. -/
theorem schoberReciprocalUnit_pow_coeff_upto_three
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) (j : ℕ) :
    PowerSeries.coeff 0 ((schoberReciprocalUnit B) ^ j) = 1 ∧
    PowerSeries.coeff 1 ((schoberReciprocalUnit B) ^ j) = 0 ∧
    PowerSeries.coeff 2 ((schoberReciprocalUnit B) ^ j) =
      (j : ℂ) * PowerSeries.coeff 1 B ∧
    PowerSeries.coeff 3 ((schoberReciprocalUnit B) ^ j) =
      (j : ℂ) * PowerSeries.coeff 2 B := by
  let R := schoberReciprocalUnit B
  have hR0 : PowerSeries.coeff 0 R = 1 := schoberReciprocalUnit_coeff_zero B
  have hR := schoberReciprocalUnit_coeff_one_to_four B hB0
  induction j with
  | zero =>
      norm_num [PowerSeries.coeff_one, R]
  | succ j ih =>
      rcases ih with ⟨ih0, ih1, ih2, ih3⟩
      constructor
      · have hcR : PowerSeries.constantCoeff R = 1 := by
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hR0
        have hcP : PowerSeries.constantCoeff (R ^ j) = 1 := by
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using ih0
        change PowerSeries.coeff 0 (R ^ (j + 1)) = 1
        simp [PowerSeries.coeff_zero_eq_constantCoeff, hcR]
      constructor
      · rw [pow_succ, PowerSeries.coeff_one_mul]
        simp [ih0, ih1, hR0, hR.1]
      constructor
      · rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
          ih0, ih1, ih2, R]
        push_cast
        ring
      · rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
          hR.2.2.1, ih0, ih1, ih2, ih3, R]
        push_cast
        ring


/-- Uniform degree-four through degree-six coefficients of reciprocal powers.
This one induction yields every nontrivial entry in rows six through eight. -/
theorem schoberReciprocalUnit_pow_coeff_four_to_six
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) (j : ℕ) :
    PowerSeries.coeff 4 ((schoberReciprocalUnit B) ^ j) =
      (j : ℂ) * PowerSeries.coeff 3 B +
        (j : ℂ) * ((j : ℂ) + 1) / 2 * (PowerSeries.coeff 1 B) ^ 2 ∧
    PowerSeries.coeff 5 ((schoberReciprocalUnit B) ^ j) =
      (j : ℂ) * PowerSeries.coeff 4 B +
        (j : ℂ) * ((j : ℂ) + 1) *
          PowerSeries.coeff 1 B * PowerSeries.coeff 2 B ∧
    PowerSeries.coeff 6 ((schoberReciprocalUnit B) ^ j) =
      (j : ℂ) * PowerSeries.coeff 5 B +
        (j : ℂ) * ((j : ℂ) + 1) *
          PowerSeries.coeff 1 B * PowerSeries.coeff 3 B +
        (j : ℂ) * ((j : ℂ) + 1) / 2 * (PowerSeries.coeff 2 B) ^ 2 +
        (j : ℂ) * ((j : ℂ) + 1) * ((j : ℂ) + 2) / 6 *
          (PowerSeries.coeff 1 B) ^ 3 := by
  let R := schoberReciprocalUnit B
  have hR0 : PowerSeries.coeff 0 R = 1 := schoberReciprocalUnit_coeff_zero B
  have hR := schoberReciprocalUnit_coeff_one_to_four B hB0
  have hR567 := schoberReciprocalUnit_coeff_five_to_seven B hB0
  induction j with
  | zero =>
      norm_num [PowerSeries.coeff_one, R]
  | succ j ih =>
      rcases ih with ⟨ih4, ih5, ih6⟩
      have hl := schoberReciprocalUnit_pow_coeff_upto_three B hB0 j
      rcases hl with ⟨hl0, hl1, hl2, hl3⟩
      constructor
      · rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
          hR.2.2.1, hR.2.2.2, hl0, hl1, hl2, hl3, ih4, R]
        push_cast
        ring
      constructor
      · rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
          hR.2.2.1, hR.2.2.2, hR567.1,
          hl0, hl1, hl2, hl3, ih4, ih5, R]
        push_cast
        ring
      · rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hR0, hR.1, hR.2.1,
          hR.2.2.1, hR.2.2.2, hR567.1, hR567.2.1,
          hl0, hl1, hl2, hl3, ih4, ih5, ih6, R]
        push_cast
        ring

/-- Every row ends in one, immediately preceded by zero. -/
theorem schoberA_diagonal_one
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) (n : ℕ) :
    schoberA B n n = 1 := by
  have h := (schoberReciprocalUnit_pow_coeff_upto_three B hB0 n).1
  simpa only [zero_add] using (schoberA_shift B n 0).trans h

theorem schoberA_prediagonal_zero
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) (n : ℕ) :
    schoberA B (n + 1) n = 0 := by
  have h := (schoberReciprocalUnit_pow_coeff_upto_three B hB0 n).2.1
  simpa only [add_comm] using (schoberA_shift B n 1).trans h

/-- Entire sixth row of the inverse-coordinate coefficient table. -/
theorem schoberA_row_six
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberA B 6 1 = PowerSeries.coeff 4 B +
        2 * PowerSeries.coeff 1 B * PowerSeries.coeff 2 B ∧
    schoberA B 6 2 = 2 * PowerSeries.coeff 3 B +
        3 * (PowerSeries.coeff 1 B) ^ 2 ∧
    schoberA B 6 3 = 3 * PowerSeries.coeff 2 B ∧
    schoberA B 6 4 = 4 * PowerSeries.coeff 1 B ∧
    schoberA B 6 5 = 0 ∧
    schoberA B 6 6 = 1 := by
  have hR := schoberReciprocalUnit_coeff_five_to_seven B hB0
  constructor
  · simpa using (schoberA_shift B 1 5).trans (by simpa using hR.1)
  constructor
  · have h := (schoberA_shift B 2 4).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 2).1
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 3 3).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 3).2.2.2
    simpa using h
  constructor
  · have h := (schoberA_shift B 4 2).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 4).2.2.1
    simpa using h
  constructor
  · simpa using schoberA_prediagonal_zero B hB0 5
  · exact schoberA_diagonal_one B hB0 6

/-- Entire seventh row of the inverse-coordinate coefficient table. -/
theorem schoberA_row_seven
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberA B 7 1 = PowerSeries.coeff 5 B +
        2 * PowerSeries.coeff 1 B * PowerSeries.coeff 3 B +
        (PowerSeries.coeff 2 B) ^ 2 + (PowerSeries.coeff 1 B) ^ 3 ∧
    schoberA B 7 2 = 2 * PowerSeries.coeff 4 B +
        6 * PowerSeries.coeff 1 B * PowerSeries.coeff 2 B ∧
    schoberA B 7 3 = 3 * PowerSeries.coeff 3 B +
        6 * (PowerSeries.coeff 1 B) ^ 2 ∧
    schoberA B 7 4 = 4 * PowerSeries.coeff 2 B ∧
    schoberA B 7 5 = 5 * PowerSeries.coeff 1 B ∧
    schoberA B 7 6 = 0 ∧
    schoberA B 7 7 = 1 := by
  have hR := schoberReciprocalUnit_coeff_five_to_seven B hB0
  constructor
  · simpa using (schoberA_shift B 1 6).trans (by simpa using hR.2.1)
  constructor
  · have h := (schoberA_shift B 2 5).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 2).2.1
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 3 4).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 3).1
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 4 3).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 4).2.2.2
    simpa using h
  constructor
  · have h := (schoberA_shift B 5 2).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 5).2.2.1
    simpa using h
  constructor
  · simpa using schoberA_prediagonal_zero B hB0 6
  · exact schoberA_diagonal_one B hB0 7

/-- Entire eighth row of the inverse-coordinate coefficient table. -/
theorem schoberA_row_eight
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberA B 8 1 = PowerSeries.coeff 6 B +
        2 * PowerSeries.coeff 1 B * PowerSeries.coeff 4 B +
        2 * PowerSeries.coeff 2 B * PowerSeries.coeff 3 B +
        3 * (PowerSeries.coeff 1 B) ^ 2 * PowerSeries.coeff 2 B ∧
    schoberA B 8 2 = 2 * PowerSeries.coeff 5 B +
        6 * PowerSeries.coeff 1 B * PowerSeries.coeff 3 B +
        3 * (PowerSeries.coeff 2 B) ^ 2 +
        4 * (PowerSeries.coeff 1 B) ^ 3 ∧
    schoberA B 8 3 = 3 * PowerSeries.coeff 4 B +
        12 * PowerSeries.coeff 1 B * PowerSeries.coeff 2 B ∧
    schoberA B 8 4 = 4 * PowerSeries.coeff 3 B +
        10 * (PowerSeries.coeff 1 B) ^ 2 ∧
    schoberA B 8 5 = 5 * PowerSeries.coeff 2 B ∧
    schoberA B 8 6 = 6 * PowerSeries.coeff 1 B ∧
    schoberA B 8 7 = 0 ∧
    schoberA B 8 8 = 1 := by
  have hR := schoberReciprocalUnit_coeff_five_to_seven B hB0
  constructor
  · simpa using (schoberA_shift B 1 7).trans (by simpa using hR.2.2)
  constructor
  · have h := (schoberA_shift B 2 6).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 2).2.2
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 3 5).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 3).2.1
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 4 4).trans
        (schoberReciprocalUnit_pow_coeff_four_to_six B hB0 4).1
    convert h using 1 <;> norm_num <;> ring
  constructor
  · have h := (schoberA_shift B 5 3).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 5).2.2.2
    simpa using h
  constructor
  · have h := (schoberA_shift B 6 2).trans
        (schoberReciprocalUnit_pow_coeff_upto_three B hB0 6).2.2.1
    simpa using h
  constructor
  · simpa using schoberA_prediagonal_zero B hB0 7
  · exact schoberA_diagonal_one B hB0 8
end SpringerLean