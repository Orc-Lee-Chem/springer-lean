import SpringerLean.Round137FifthTensorAlgebra

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The same forward coefficient shift used in the verified fifth-order
residue calculation, now exposed for the next order. -/
noncomputable def schoberActualForwardShift (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun p =>
    PowerSeries.coeff (p + 1) (exteriorFormalForward F))

theorem schoberActualForwardShift_coeff (F : ℂ → ℂ) (p : ℕ) :
    PowerSeries.coeff p (schoberActualForwardShift F) =
      exteriorForwardCoeff F (p + 1) := by
  simp [schoberActualForwardShift, exteriorFormalForward_coeff]

/-- A reusable finite Cauchy-product formula for the next inverse residue.
It reads the actual forward coefficients of the same F. -/
theorem schoberActualForwardShift_square_coeff (F : ℂ → ℂ) (m : ℕ) :
    PowerSeries.coeff m ((schoberActualForwardShift F) ^ 2) =
      ∑ i ∈ Finset.range (m + 1),
        exteriorForwardCoeff F (i + 1) *
          exteriorForwardCoeff F (m - i + 1) := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [schoberActualForwardShift_coeff]

/-- The degree-eight square coefficient needed at inverse index eleven. -/
theorem schoberActualForwardShift_square_eight (F : ℂ → ℂ) :
    PowerSeries.coeff 8 ((schoberActualForwardShift F) ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 9 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 8 +
      2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 7 +
      2 * exteriorForwardCoeff F 4 * exteriorForwardCoeff F 6 +
      exteriorForwardCoeff F 5 ^ 2 := by
  rw [schoberActualForwardShift_square_coeff]
  norm_num [Finset.sum_range_succ]
  ring

theorem schoberActualForwardShift_cube_six (F : ℂ → ℂ) :
    PowerSeries.coeff 6 ((schoberActualForwardShift F) ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 7 +
      6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 6 +
      6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 *
        exteriorForwardCoeff F 5 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 ^ 2 +
      3 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 5 +
      6 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 *
        exteriorForwardCoeff F 4 +
      exteriorForwardCoeff F 3 ^ 3 := by
  let g := schoberActualForwardShift F
  change PowerSeries.coeff 6 (g ^ 3) = _
  rw [show g ^ 3 = g ^ 2 * g by ring,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp [g, schoberActualForwardShift_square_coeff,
    schoberActualForwardShift_coeff, Finset.sum_range_succ]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [schoberActualForwardShift_coeff]
  ring

theorem schoberActualForwardShift_four_four (F : ℂ → ℂ) :
    PowerSeries.coeff 4 ((schoberActualForwardShift F) ^ 4) =
      4 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 5 +
      12 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 4 +
      6 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 ^ 2 +
      12 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2 *
        exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 4 := by
  let g := schoberActualForwardShift F
  change PowerSeries.coeff 4 (g ^ 4) = _
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by ring,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp [g, schoberActualForwardShift_square_coeff, Finset.sum_range_succ]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [schoberActualForwardShift_coeff]
  ring

theorem schoberActualForwardShift_four_one (F : ℂ → ℂ) :
    PowerSeries.coeff 1 ((schoberActualForwardShift F) ^ 4) =
      4 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 2 := by
  let g := schoberActualForwardShift F
  change PowerSeries.coeff 1 (g ^ 4) = _
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by ring, PowerSeries.coeff_one_mul]
  simp [g, schoberActualForwardShift_square_coeff,
    Finset.sum_range_succ,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    schoberActualForwardShift_coeff]
  ring

theorem schoberActualForwardShift_four_two (F : ℂ → ℂ) :
    PowerSeries.coeff 2 ((schoberActualForwardShift F) ^ 4) =
      4 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
      6 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 := by
  let g := schoberActualForwardShift F
  change PowerSeries.coeff 2 (g ^ 4) = _
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by ring,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp [g, schoberActualForwardShift_square_coeff,
    Finset.sum_range_succ,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    schoberActualForwardShift_coeff]
  ring

theorem schoberActualForwardShift_five_two (F : ℂ → ℂ) :
    PowerSeries.coeff 2 ((schoberActualForwardShift F) ^ 5) =
      5 * exteriorForwardCoeff F 1 ^ 4 * exteriorForwardCoeff F 3 +
      10 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 2 ^ 2 := by
  let g := schoberActualForwardShift F
  change PowerSeries.coeff 2 (g ^ 5) = _
  rw [show g ^ 5 = g ^ 2 * g ^ 2 * g by ring,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp [g, schoberActualForwardShift_square_coeff,
    schoberActualForwardShift_coeff, Finset.sum_range_succ]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [schoberActualForwardShift_coeff]
  rw [show (schoberActualForwardShift F) ^ 2 *
      (schoberActualForwardShift F) ^ 2 =
      (schoberActualForwardShift F) ^ 4 by ring]
  rw [schoberActualForwardShift_four_one,
    schoberActualForwardShift_four_two]
  ring

theorem schoberActualForwardShift_six_zero (F : ℂ → ℂ) :
    PowerSeries.coeff 0 ((schoberActualForwardShift F) ^ 6) =
      exteriorForwardCoeff F 1 ^ 6 := by
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [schoberActualForwardShift_coeff]

end SpringerLean
