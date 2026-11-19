import SpringerLean.Round176KernelSixInnerCubic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace SpringerLean

open PowerSeries

private theorem sixth_square_coeff_five_for_mode (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 4 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 3 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sixth_cube_coeff_three_for_mode (g : PowerSeries ℂ) :
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
  rw [show g ^ 3 = g ^ 2 * g by ring,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hs1 hs2 hs3
  rw [hs1, hs2, hs3]
  ring

/-- The third negative mode of the actual sixth Faber factor, computed from
the independently Taylor-read forward coefficients of one map. -/
theorem sixthFaberFactor_actual_mode_nine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 9 =
      6 * (exteriorForwardCoeff F 8 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 6 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 5 +
        2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 3 +
        (3 : ℂ)⁻¹ * exteriorForwardCoeff F 2 ^ 3) := by
  let g := schoberActualForwardShift F
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) :=
    schoberActualForwardShift_coeff F p
  have hconst : PowerSeries.constantCoeff g = exteriorForwardCoeff F 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hsq5 : PowerSeries.coeff 5 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 6 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 := by
    rw [sixth_square_coeff_five_for_mode]
    simp [hg]
  have hsq3 : PowerSeries.coeff 3 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 := by
    rw [fourthFaber_shifted_square_coeff_three]
    simp [hg]
  have hsq2 : PowerSeries.coeff 2 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 2 := by
    rw [fourthFaber_shifted_square_coeff_two]
    simp [hg]
  have hcube3 : PowerSeries.coeff 3 (g ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 4 +
      6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 3 := by
    rw [sixth_cube_coeff_three_for_mode]
    simp [hg]
  have hC (c : ℂ) (p m : ℕ) (hm : m ≠ 0) :
      PowerSeries.coeff m ((PowerSeries.C c) ^ p) = 0 := by
    rw [show (PowerSeries.C c) ^ p = PowerSeries.C (c ^ p) from
      (map_pow (PowerSeries.C : ℂ →+* PowerSeries ℂ) c p).symm]
    exact PowerSeries.coeff_C_of_ne_zero hm
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, PowerSeries.coeff_one_pow]
  dsimp only [g] at hconst hsq5 hsq3 hsq2 hcube3
  rw [hsq5, hsq3, hsq2, hcube3, hconst]
  simp [hC, PowerSeries.coeff_X]
  ring

end SpringerLean
