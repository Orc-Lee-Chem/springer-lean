import SpringerLean.Round128FiveFaberThirdMode

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem fifth_square_coeff_five (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 4 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 3 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem fifth_cube_coeff_three (g : PowerSeries ℂ) :
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

private theorem fifth_fourth_coeff_one (g : PowerSeries ℂ) :
    PowerSeries.coeff 1 (g ^ 4) =
      4 * (PowerSeries.coeff 0 g) ^ 3 * PowerSeries.coeff 1 g := by
  rw [PowerSeries.coeff_one_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

theorem fifthFaberFactor_actual_mode_nine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 9 =
      5 * (exteriorForwardCoeff F 8 +
        3 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 5 +
        (exteriorForwardCoeff F 2) ^ 3 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 6 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 3 +
        (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 4 +
        (exteriorForwardCoeff F 1) ^ 3 * exteriorForwardCoeff F 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hsq5 := fifth_square_coeff_five g
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  have hcube3 := fifth_cube_coeff_three g
  have hcube1 : PowerSeries.coeff 1 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 1 g := by
    rw [PowerSeries.coeff_one_pow]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hfour1 := fifth_fourth_coeff_one g
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  rw [← actualTaylorSeries_coeff,
    fifthFaberFactor_actualTaylorSeries F hc,
    fifthFaberFormalFactor_expand F]
  change PowerSeries.coeff 9
    (1 + PowerSeries.X ^ 2 *
        (5 * g - PowerSeries.C (5 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (5 * b₂) +
      PowerSeries.X ^ 4 *
        (10 * g ^ 2 -
          3 * PowerSeries.C (5 * b₁) * g +
          PowerSeries.C (5 * (b₁ ^ 2 - b₃))) +
      PowerSeries.X ^ 5 *
        (-(2 * PowerSeries.C (5 * b₂) * g) +
          PowerSeries.C (5 * (b₁ * b₂ - b₄))) +
      PowerSeries.X ^ 6 *
        (10 * g ^ 3 -
          3 * PowerSeries.C (5 * b₁) * g ^ 2 +
          PowerSeries.C (5 * (b₁ ^ 2 - b₃)) * g) -
      PowerSeries.X ^ 7 *
        (PowerSeries.C (5 * b₂) * g ^ 2) +
      PowerSeries.X ^ 8 *
        (5 * g ^ 4 - PowerSeries.C (5 * b₁) * g ^ 3) +
      PowerSeries.X ^ 10 * g ^ 5) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm₁ : PowerSeries.coeff 5
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g) =
        15 * b₁ * exteriorForwardCoeff F 6 := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g =
        3 * (PowerSeries.C (5 * b₁) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 5]
    ring
  have hterm₂ : PowerSeries.coeff 4
      (2 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g) =
        10 * b₂ * exteriorForwardCoeff F 5 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g =
        2 * (PowerSeries.C (5 * b₂) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 4]
    ring
  have hterm₃ : PowerSeries.coeff 3
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2) =
        15 * b₁ *
          (2 * b₁ * exteriorForwardCoeff F 4 + 2 * b₂ * b₃) := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2 =
        3 * (PowerSeries.C (5 * b₁) * g ^ 2) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hsq3]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
    ring
  have hterm₄ : PowerSeries.coeff 3
      (PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g) =
        5 * (b₁ ^ 2 - b₃) * b₄ := by
    rw [show PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g =
        PowerSeries.C (5 * (b₁ ^ 2 - b₃)) * g by
      simp only [← map_pow, ← map_sub, ← map_mul],
      PowerSeries.coeff_C_mul, hg 3]
  have hterm₅ : PowerSeries.coeff 2
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2) =
        5 * b₂ * (2 * b₁ * b₃ + b₂ ^ 2) := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2 =
        PowerSeries.C (5 * b₂) * g ^ 2 by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq2]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
  have hterm₆ : PowerSeries.coeff 1
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3) =
        15 * b₁ ^ 3 * b₂ := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3 =
        PowerSeries.C (5 * b₁) * g ^ 3 by rw [map_mul],
      PowerSeries.coeff_C_mul, hcube1]
    simp only [hg]
    dsimp only [b₁, b₂]
    ring
  have hzero : PowerSeries.coeff 5 (PowerSeries.C b₁ ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆,
    hzero, hsq5, hcube3, hfour1]
  simp only [hg0, hg]
  dsimp only [b₁, b₂, b₃, b₄]
  ring

theorem fifthFaberFactor_actual_mode_nine_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 9 =
      5 * schoberBiCoeff 4 5
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rw [fifthFaberFactor_actual_mode_nine F hc,
    schoberKernelQ5_coeff_four_five]
  ring

end SpringerLean
