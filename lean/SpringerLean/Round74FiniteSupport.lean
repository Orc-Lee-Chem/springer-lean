import SpringerLean.Round73KernelMatrix

namespace SpringerLean

open PowerSeries

/-- In a degree-n diagonal kernel coefficient, powers above n cannot contribute. -/
theorem schoberA_eq_zero_of_lt
    (B : PowerSeries ℂ) {n j : ℕ} (h : n < j) :
    schoberA B n j = 0 := by
  change PowerSeries.coeff n
    ((PowerSeries.X * schoberReciprocalUnit B) ^ j) = 0
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr h]

/-- The last nonzero entry of every Schober row is exactly one. -/
theorem schoberA_diag (B : PowerSeries ℂ) (n : ℕ) :
    schoberA B n n = 1 := by
  have h := schoberA_shift B n 0
  have hc : PowerSeries.constantCoeff (schoberReciprocalUnit B) = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberReciprocalUnit_coeff_zero B
  simpa [PowerSeries.coeff_zero_eq_constantCoeff, hc] using h

theorem schoberActualA_eq_zero_of_lt
    (F : ℂ → ℂ) {n j : ℕ} (h : n < j) :
    schoberActualA F n j = 0 :=
  schoberA_eq_zero_of_lt (schoberActualInverseSeries F) h

theorem schoberActualA_diag (F : ℂ → ℂ) (n : ℕ) :
    schoberActualA F n n = 1 :=
  schoberA_diag (schoberActualInverseSeries F) n

end SpringerLean
