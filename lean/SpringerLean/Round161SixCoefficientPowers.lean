import SpringerLean.Round160KernelSixFifth

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- A constant-free power series has only one partition of degree six
into five positive degrees, up to the choice of the degree-two slot. -/
theorem powerSeries_coeff_six_pow_five_of_const_zero
    (g : PowerSeries ℂ) (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 6 (g ^ 5) =
      5 * PowerSeries.coeff 1 g ^ 4 * PowerSeries.coeff 2 g := by
  let h : PowerSeries ℂ :=
    PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) g)
  have hshift : g = PowerSeries.X * h := by
    simpa [h, hg0] using (PowerSeries.eq_X_mul_shift_add_const g)
  rw [hshift, mul_pow]
  have hcoeff := PowerSeries.coeff_X_pow_mul (h ^ 5) 5 1
  rw [hcoeff, PowerSeries.coeff_one_pow]
  simp [h, PowerSeries.coeff_zero_eq_constantCoeff]
  ring

private theorem powerSeries_coeff_two_pow_four (h : PowerSeries ℂ) :
    PowerSeries.coeff 2 (h ^ 4) =
      4 * PowerSeries.coeff 0 h ^ 3 * PowerSeries.coeff 2 h +
      6 * PowerSeries.coeff 0 h ^ 2 * PowerSeries.coeff 1 h ^ 2 := by
  have hs1 : PowerSeries.coeff 1 (h ^ 2) =
      2 * PowerSeries.coeff 0 h * PowerSeries.coeff 1 h := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hs2 := fourthFaber_shifted_square_coeff_two h
  rw [show h ^ 4 = h ^ 2 * h ^ 2 by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hs1 hs2
  rw [hs1, hs2]
  ring

/-- The degree-six term of a fourth power of a constant-free series. -/
theorem powerSeries_coeff_six_pow_four_of_const_zero
    (g : PowerSeries ℂ) (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 6 (g ^ 4) =
      4 * PowerSeries.coeff 1 g ^ 3 * PowerSeries.coeff 3 g +
      6 * PowerSeries.coeff 1 g ^ 2 * PowerSeries.coeff 2 g ^ 2 := by
  let h : PowerSeries ℂ :=
    PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) g)
  have hshift : g = PowerSeries.X * h := by
    simpa [h, hg0] using (PowerSeries.eq_X_mul_shift_add_const g)
  rw [hshift, mul_pow]
  have hcoeff := PowerSeries.coeff_X_pow_mul (h ^ 4) 4 2
  rw [hcoeff, powerSeries_coeff_two_pow_four]
  simp [h]

end SpringerLean
