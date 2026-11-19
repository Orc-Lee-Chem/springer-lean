import SpringerLean.Round158SixKernelFourthEntry

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

private theorem sixth_shifted_square_coeff_six (g : PowerSeries ℂ) :
    PowerSeries.coeff 6 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 6 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 4 g +
      PowerSeries.coeff 3 g ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sixth_shifted_cube_coeff_four (g : PowerSeries ℂ) :
    PowerSeries.coeff 4 (g ^ 3) =
      3 * PowerSeries.coeff 0 g ^ 2 * PowerSeries.coeff 4 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g *
        PowerSeries.coeff 3 g +
      3 * PowerSeries.coeff 0 g * PowerSeries.coeff 2 g ^ 2 +
      3 * PowerSeries.coeff 1 g ^ 2 * PowerSeries.coeff 2 g := by
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) =
      PowerSeries.coeff 0 g ^ 2 := by simp
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  have hsq4 := fourthFaber_shifted_square_coeff_four g
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hsq0 hsq1 hsq2 hsq3 hsq4
  rw [hsq1, hsq2, hsq3, hsq4]
  ring

private theorem sixth_shifted_fourth_coeff_two (g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (g ^ 4) =
      4 * PowerSeries.coeff 0 g ^ 3 * PowerSeries.coeff 2 g +
      6 * PowerSeries.coeff 0 g ^ 2 * PowerSeries.coeff 1 g ^ 2 := by
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) =
      PowerSeries.coeff 0 g ^ 2 := by simp
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hsq0 hsq1 hsq2
  rw [hsq1, hsq2]
  ring

/-- Sixth negative mode of the original map's fourth Faber factor. -/
theorem fourthFaberFactor_actual_mode_ten
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 10 =
      4 * (exteriorForwardCoeff F 9 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
        3 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
        (3 : ℂ) / 2 * exteriorForwardCoeff F 4 ^ 2 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
        3 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
        (3 : ℂ) / 2 * exteriorForwardCoeff F 1 ^ 2 *
          exteriorForwardCoeff F 2 ^ 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [b₁, PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [b₂] using hg 1
  have hsq4 := fourthFaber_shifted_square_coeff_four g
  have hsq6 := sixth_shifted_square_coeff_six g
  have hcube4 := sixth_shifted_cube_coeff_four g
  have hfour2 := sixth_shifted_fourth_coeff_two g
  rw [← actualTaylorSeries_coeff]
  have h := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor F) = _ at h
  rw [h]
  change PowerSeries.coeff 10 (fourthFaberFormalFactor F) = _
  rw [fourthFaberFormalFactor_expand F]
  change PowerSeries.coeff 10
    (1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
      PowerSeries.X ^ 4 *
        (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
          PowerSeries.C (4 * exteriorForwardCoeff F 3 - 2 * b₁ ^ 2)) -
      PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
      PowerSeries.X ^ 6 *
        (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
      PowerSeries.X ^ 8 * g ^ 4) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm₁ : PowerSeries.coeff 6
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * exteriorForwardCoeff F 7 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
          PowerSeries.C (8 * b₁) * g by
      rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
        PowerSeries.C (4 * b₁) by rw [map_mul], fourthFaber_two_C_four],
      PowerSeries.coeff_C_mul, hg 6]
  have hterm₂ : PowerSeries.coeff 5
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ * g) =
        4 * b₂ * exteriorForwardCoeff F 6 := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ =
      PowerSeries.C (4 * b₂) by rw [map_mul],
      PowerSeries.coeff_C_mul, hg 5]
  have hterm₃ : PowerSeries.coeff 4
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ * g ^ 2) =
        4 * b₁ *
          (2 * b₁ * exteriorForwardCoeff F 5 +
            2 * b₂ * exteriorForwardCoeff F 4 +
            exteriorForwardCoeff F 3 ^ 2) := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
      PowerSeries.C (4 * b₁) by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq4]
    simp only [hg]
    dsimp only [b₁, b₂]
  have hzero : PowerSeries.coeff 6 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hzero,
    hsq6, hcube4, hfour2]
  simp only [hg, hg0, hg1]
  dsimp only [b₁, b₂]
  ring

theorem fourthFaberFactor_actual_mode_ten_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 10 =
      4 * schoberBiCoeff 6 4
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [fourthFaberFactor_actual_mode_ten F hc,
    schoberKernelQ6_coeff_six_four]

end SpringerLean
