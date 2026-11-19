import SpringerLean.Round128FiveFaberThirdMode

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem fifth_square_coeff_six (g : PowerSeries ℂ) :
    PowerSeries.coeff 6 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 6 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 4 g +
      (PowerSeries.coeff 3 g) ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem fifth_cube_coeff_four (g : PowerSeries ℂ) :
    PowerSeries.coeff 4 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 4 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g *
        PowerSeries.coeff 3 g +
      3 * PowerSeries.coeff 0 g * (PowerSeries.coeff 2 g) ^ 2 +
      3 * (PowerSeries.coeff 1 g) ^ 2 * PowerSeries.coeff 2 g := by
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  rw [fourthFaber_shifted_square_coeff_four,
    fourthFaber_shifted_square_coeff_three,
    fourthFaber_shifted_square_coeff_two]
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  rw [hsq1]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

private theorem fifth_fourth_coeff_two (g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (g ^ 4) =
      4 * (PowerSeries.coeff 0 g) ^ 3 * PowerSeries.coeff 2 g +
      6 * (PowerSeries.coeff 0 g) ^ 2 *
        (PowerSeries.coeff 1 g) ^ 2 := by
  rw [show g ^ 4 = g ^ 3 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  rw [fourthFaber_shifted_cube_coeff_two]
  have hcube1 : PowerSeries.coeff 1 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 1 g := by
    rw [PowerSeries.coeff_one_pow]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  rw [hcube1]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

/-- The central negative mode of the actual fifth Faber factor. -/
theorem fifthFaberFactor_actual_mode_ten
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 10 =
      5 * (exteriorForwardCoeff F 9 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
        3 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
        2 * (exteriorForwardCoeff F 4) ^ 2 +
        (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 3) ^ 2 +
        4 * (exteriorForwardCoeff F 2) ^ 2 * exteriorForwardCoeff F 3 +
        (exteriorForwardCoeff F 1) ^ 3 * exteriorForwardCoeff F 3 +
        3 * (exteriorForwardCoeff F 1) ^ 2 *
          (exteriorForwardCoeff F 2) ^ 2) +
      (exteriorForwardCoeff F 1) ^ 5 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hsq6 := fifth_square_coeff_six g
  have hsq4 := fourthFaber_shifted_square_coeff_four g
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  have hcube4 := fifth_cube_coeff_four g
  have hcube2 := fourthFaber_shifted_cube_coeff_two g
  have hfour2 := fifth_fourth_coeff_two g
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  rw [← actualTaylorSeries_coeff,
    fifthFaberFactor_actualTaylorSeries F hc,
    fifthFaberFormalFactor_expand F]
  change PowerSeries.coeff 10
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
  have hterm₁ : PowerSeries.coeff 6
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g) =
        15 * b₁ * exteriorForwardCoeff F 7 := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g =
        3 * (PowerSeries.C (5 * b₁) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 6]
    ring
  have hterm₂ : PowerSeries.coeff 5
      (2 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g) =
        10 * b₂ * exteriorForwardCoeff F 6 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g =
        2 * (PowerSeries.C (5 * b₂) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 5]
    ring
  have hterm₃ : PowerSeries.coeff 4
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2) =
        15 * b₁ *
          (2 * b₁ * exteriorForwardCoeff F 5 +
            2 * b₂ * exteriorForwardCoeff F 4 + b₃ ^ 2) := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2 =
        3 * (PowerSeries.C (5 * b₁) * g ^ 2) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hsq4]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
    ring
  have hterm₄ : PowerSeries.coeff 4
      (PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g) =
        5 * (b₁ ^ 2 - b₃) * exteriorForwardCoeff F 5 := by
    rw [show PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g =
        PowerSeries.C (5 * (b₁ ^ 2 - b₃)) * g by
      simp only [← map_pow, ← map_sub, ← map_mul],
      PowerSeries.coeff_C_mul, hg 4]
  have hterm₅ : PowerSeries.coeff 3
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2) =
        5 * b₂ * (2 * b₁ * b₄ + 2 * b₂ * b₃) := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2 =
        PowerSeries.C (5 * b₂) * g ^ 2 by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq3]
    simp only [hg]
    dsimp only [b₁, b₂, b₃, b₄]
  have hterm₆ : PowerSeries.coeff 2
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3) =
        5 * b₁ * (3 * b₁ ^ 2 * b₃ + 3 * b₁ * b₂ ^ 2) := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3 =
        PowerSeries.C (5 * b₁) * g ^ 3 by rw [map_mul],
      PowerSeries.coeff_C_mul, hcube2]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
  have hzero : PowerSeries.coeff 6 (PowerSeries.C b₁ ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆,
    hzero, hsq6, hcube4, hfour2]
  simp only [hg0, hg]
  dsimp only [b₁, b₂, b₃, b₄]
  simp only [Nat.zero_add, Nat.reduceAdd]
  ring

theorem fifthFaberFactor_actual_mode_ten_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 10 =
      5 * schoberBiCoeff 5 5
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rw [fifthFaberFactor_actual_mode_ten F hc,
    schoberKernelQ5_coeff_five_five]
  ring

end SpringerLean
