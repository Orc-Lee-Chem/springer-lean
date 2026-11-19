import SpringerLean.Round162SixKernelFifthEntry

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

theorem sixth_square_coeff_seven (g : PowerSeries ℂ) :
    PowerSeries.coeff 7 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 7 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 6 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 3 g * PowerSeries.coeff 4 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

theorem sixth_square_coeff_five (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 4 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 3 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

theorem sixth_cube_coeff_five (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 3) =
      3 * PowerSeries.coeff 0 g ^ 2 * PowerSeries.coeff 5 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g *
        PowerSeries.coeff 4 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 2 g *
        PowerSeries.coeff 3 g +
      3 * PowerSeries.coeff 1 g ^ 2 * PowerSeries.coeff 3 g +
      3 * PowerSeries.coeff 1 g * PowerSeries.coeff 2 g ^ 2 := by
  have hs1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hs2 := fourthFaber_shifted_square_coeff_two g
  have hs3 := fourthFaber_shifted_square_coeff_three g
  have hs4 := fourthFaber_shifted_square_coeff_four g
  have hs5 := sixth_square_coeff_five g
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hs1 hs2 hs3 hs4 hs5
  rw [hs1, hs2, hs3, hs4, hs5]
  ring

theorem sixth_cube_coeff_three (g : PowerSeries ℂ) :
    PowerSeries.coeff 3 (g ^ 3) =
      3 * PowerSeries.coeff 0 g ^ 2 * PowerSeries.coeff 3 g +
      6 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g *
        PowerSeries.coeff 2 g +
      PowerSeries.coeff 1 g ^ 3 := by
  have hs1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hs2 := fourthFaber_shifted_square_coeff_two g
  have hs3 := fourthFaber_shifted_square_coeff_three g
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hs1 hs2 hs3
  rw [hs1, hs2, hs3]
  ring

theorem sixth_fourth_coeff_three (g : PowerSeries ℂ) :
    PowerSeries.coeff 3 (g ^ 4) =
      4 * PowerSeries.coeff 0 g ^ 3 * PowerSeries.coeff 3 g +
      12 * PowerSeries.coeff 0 g ^ 2 * PowerSeries.coeff 1 g *
        PowerSeries.coeff 2 g +
      4 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g ^ 3 := by
  have hs1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hs2 := fourthFaber_shifted_square_coeff_two g
  have hs3 := fourthFaber_shifted_square_coeff_three g
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hs1 hs2 hs3
  rw [hs1, hs2, hs3]
  ring

/-- Sixth negative mode of the actual fifth Faber factor. -/
theorem fifthFaberFactor_actual_mode_eleven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 11 =
      5 * (exteriorForwardCoeff F 10 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 8 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 7 +
        3 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 6 +
        4 * exteriorForwardCoeff F 4 * exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 6 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 5 +
        6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 *
          exteriorForwardCoeff F 4 +
        4 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 4 +
        5 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 ^ 2 +
        exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 4 +
        6 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 3 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 3 +
        exteriorForwardCoeff F 1 ^ 4 * exteriorForwardCoeff F 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hsq7 := sixth_square_coeff_seven g
  have hsq5 := sixth_square_coeff_five g
  have hsq4 := fourthFaber_shifted_square_coeff_four g
  have hcube5 := sixth_cube_coeff_five g
  have hcube3 := sixth_cube_coeff_three g
  have hfour3 := sixth_fourth_coeff_three g
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hpow5 : PowerSeries.coeff 1 (g ^ 5) =
      5 * b₁ ^ 4 * b₂ := by
    rw [PowerSeries.coeff_one_pow]
    simp [hg0, hg, b₁, b₂]
    ring
  rw [← actualTaylorSeries_coeff,
    fifthFaberFactor_actualTaylorSeries F hc,
    fifthFaberFormalFactor_expand F]
  change PowerSeries.coeff 11
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
  have hterm₁ : PowerSeries.coeff 7
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g) =
        15 * b₁ * exteriorForwardCoeff F 8 := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g =
        3 * (PowerSeries.C (5 * b₁) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 7]
    ring
  have hterm₂ : PowerSeries.coeff 6
      (2 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g) =
        10 * b₂ * exteriorForwardCoeff F 7 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂) * g =
        2 * (PowerSeries.C (5 * b₂) * g) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hg 6]
    ring
  have hterm₃ : PowerSeries.coeff 5
      (3 * (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2) =
        15 * b₁ *
          (2 * b₁ * exteriorForwardCoeff F 6 +
            2 * b₂ * exteriorForwardCoeff F 5 +
            2 * b₃ * exteriorForwardCoeff F 4) := by
    rw [show (3 : PowerSeries ℂ) *
        (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁) * g ^ 2 =
        3 * (PowerSeries.C (5 * b₁) * g ^ 2) by
      rw [map_mul]; ring,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_C_mul, hsq5]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
    ring
  have hterm₄ : PowerSeries.coeff 5
      (PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g) =
        5 * (b₁ ^ 2 - b₃) * exteriorForwardCoeff F 6 := by
    rw [show PowerSeries.C (5 : ℂ) *
        (PowerSeries.C b₁ ^ 2 - PowerSeries.C b₃) * g =
        PowerSeries.C (5 * (b₁ ^ 2 - b₃)) * g by
      simp only [← map_pow, ← map_sub, ← map_mul],
      PowerSeries.coeff_C_mul, hg 5]
  have hterm₅ : PowerSeries.coeff 4
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2) =
        5 * b₂ * (2 * b₁ * exteriorForwardCoeff F 5 +
          2 * b₂ * exteriorForwardCoeff F 4 + b₃ ^ 2) := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₂ * g ^ 2 =
        PowerSeries.C (5 * b₂) * g ^ 2 by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq4]
    simp only [hg]
    dsimp only [b₁, b₂, b₃]
  have hterm₆ : PowerSeries.coeff 3
      (PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3) =
        5 * b₁ * (3 * b₁ ^ 2 * b₄ +
          6 * b₁ * b₂ * b₃ + b₂ ^ 3) := by
    rw [show PowerSeries.C (5 : ℂ) * PowerSeries.C b₁ * g ^ 3 =
        PowerSeries.C (5 * b₁) * g ^ 3 by rw [map_mul],
      PowerSeries.coeff_C_mul, hcube3]
    simp only [hg]
    dsimp only [b₁, b₂, b₃, b₄]
  have hzero : PowerSeries.coeff 7 (PowerSeries.C b₁ ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆,
    hzero, hsq7, hcube5, hfour3, hpow5]
  simp only [hg0, hg]
  dsimp only [b₁, b₂, b₃, b₄]
  simp only [Nat.zero_add, Nat.reduceAdd]
  ring

theorem fifthFaberFactor_actual_mode_eleven_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 11 =
      5 * schoberBiCoeff 6 5
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [fifthFaberFactor_actual_mode_eleven F hc,
    schoberKernelQ6_coeff_six_five]

end SpringerLean
