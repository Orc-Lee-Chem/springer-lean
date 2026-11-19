import SpringerLean.Round122FiveKernelFirstRow

namespace SpringerLean

/-- Fifth negative mode of the second actual Faber factor. -/
theorem secondFaberFactor_actual_mode_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 7 =
      2 * exteriorForwardCoeff F 6 +
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 := by
  let φ := actualTaylorSeries (exteriorPhi F)
  have hs := secondFaberFactor_actualTaylorSeries F hc
  rw [← actualTaylorSeries_coeff, hs]
  rw [← exteriorPhi_actualTaylorSeries F hc]
  change PowerSeries.coeff 7
    (φ ^ 2 - PowerSeries.C (2 * exteriorForwardCoeff F 1) *
      PowerSeries.X ^ 2) = _
  simp only [map_sub, PowerSeries.coeff_C_mul]
  have hcor : PowerSeries.coeff 7 (PowerSeries.X ^ 2 : PowerSeries ℂ) = 0 := by
    simp [PowerSeries.coeff_X_pow]
  rw [hcor]
  simp only [mul_zero, sub_zero, pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [φ, actualTaylorSeries_coeff,
    actualTaylorCoeff_exteriorPhi_zero,
    actualTaylorCoeff_exteriorPhi_succ F hc]
  simp [φ, actualTaylorSeries, actualTaylorCoeff_exteriorPhi_zero,
    exteriorForwardCoeff_zero]
  ring

theorem secondFaberFactor_actual_mode_seven_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 7 =
      2 * schoberBiCoeff 5 2
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rw [secondFaberFactor_actual_mode_seven F hc,
    schoberKernelQ5_coeff_five_two]
  ring

end SpringerLean
