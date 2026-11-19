import SpringerLean.Round124FiveKernelThirdColumn

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem fifth_shifted_square_coeff_five (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 4 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 3 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem fifth_shifted_cube_coeff_three (g : PowerSeries ℂ) :
    PowerSeries.coeff 3 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 3 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g *
        PowerSeries.coeff 2 g +
      (PowerSeries.coeff 1 g) ^ 3 := by
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hsq1 hsq2 hsq3
  rw [hsq1, hsq2, hsq3]
  ring

private theorem fifth_shifted_fourth_coeff_one (g : PowerSeries ℂ) :
    PowerSeries.coeff 1 (g ^ 4) =
      4 * (PowerSeries.coeff 0 g) ^ 3 * PowerSeries.coeff 1 g := by
  rw [PowerSeries.coeff_one_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

/-- Fifth negative mode of the original map's fourth Faber factor. -/
theorem fourthFaberFactor_actual_mode_nine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 9 =
      4 * (exteriorForwardCoeff F 8 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 6 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 5 +
        3 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 4 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 2 ^ 3 +
        exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [b₁, PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [b₂] using hg 1
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  have hsq5 := fifth_shifted_square_coeff_five g
  have hcube3 := fifth_shifted_cube_coeff_three g
  have hfour1 := fifth_shifted_fourth_coeff_one g
  rw [← actualTaylorSeries_coeff]
  have h := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor F) = _ at h
  rw [h]
  change PowerSeries.coeff 9 (fourthFaberFormalFactor F) = _
  rw [fourthFaberFormalFactor_expand F]
  change PowerSeries.coeff 9
    (1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
      PowerSeries.X ^ 4 *
        (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
          PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
      PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
      PowerSeries.X ^ 6 *
        (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
      PowerSeries.X ^ 8 * g ^ 4) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm₁ : PowerSeries.coeff 5
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * exteriorForwardCoeff F 6 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
          PowerSeries.C (8 * b₁) * g by
      rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
        PowerSeries.C (4 * b₁) by rw [map_mul], fourthFaber_two_C_four],
      PowerSeries.coeff_C_mul, hg 5]
  have hterm₂ : PowerSeries.coeff 4
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ * g) =
        4 * b₂ * exteriorForwardCoeff F 5 := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ =
      PowerSeries.C (4 * b₂) by rw [map_mul],
      PowerSeries.coeff_C_mul, hg 4]
  have hterm₃ : PowerSeries.coeff 3
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ * g ^ 2) =
        4 * b₁ *
          (2 * b₁ * exteriorForwardCoeff F 4 +
            2 * b₂ * exteriorForwardCoeff F 3) := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
      PowerSeries.C (4 * b₁) by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq3]
    simp only [hg]
    dsimp only [b₁, b₂]
  have hzero : PowerSeries.coeff 5 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hzero,
    hsq5, hcube3, hfour1]
  simp only [hg, hg0, hg1]
  dsimp only [b₁, b₂, b₃]
  ring

theorem fourthFaberFactor_actual_mode_nine_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 9 =
      4 * schoberBiCoeff 5 4
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rw [fourthFaberFactor_actual_mode_nine F hc,
    schoberKernelQ5_coeff_five_four]

end SpringerLean
