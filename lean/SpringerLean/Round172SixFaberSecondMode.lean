import SpringerLean.Round171SixFaberKernelFirst

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace SpringerLean

open PowerSeries

/-- The second negative mode in the actual sixth Faber factor. -/
theorem sixthFaberFactor_actual_mode_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 8 =
      6 * (exteriorForwardCoeff F 7 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
        (2 : ℂ)⁻¹ * exteriorForwardCoeff F 3 ^ 2) := by
  let g := schoberActualForwardShift F
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) :=
    schoberActualForwardShift_coeff F p
  have hconst : PowerSeries.constantCoeff g = exteriorForwardCoeff F 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hsq4 : PowerSeries.coeff 4 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      exteriorForwardCoeff F 3 ^ 2 := by
    rw [fourthFaber_shifted_square_coeff_four]
    simp [hg]
  have hsq2 : PowerSeries.coeff 2 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 2 := by
    rw [fourthFaber_shifted_square_coeff_two]
    simp [hg]
  have hcube2 : PowerSeries.coeff 2 (g ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2 := by
    rw [fourthFaber_shifted_cube_coeff_two]
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
  dsimp only [g] at hsq4 hsq2 hcube2 hconst
  rw [hsq4, hsq2, hcube2, hconst]
  simp [hC]
  ring

end SpringerLean
