import SpringerLean.Round168SixMatrixConditional
import SpringerLean.Round146SixLowModes

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace SpringerLean

open PowerSeries

/-- The first negative Fourier mode of the genuine sixth Faber factor is
read from the same actual forward map. -/
theorem sixthFaberFactor_actual_mode_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 7 =
      6 * exteriorForwardCoeff F 6 := by
  have hsquare : PowerSeries.coeff 3
      ((schoberActualForwardShift F) ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 := by
    rw [schoberActualForwardShift_square_coeff]
    norm_num [Finset.sum_range_succ]
    ring
  have hconst : PowerSeries.constantCoeff (schoberActualForwardShift F) =
      exteriorForwardCoeff F 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberActualForwardShift_coeff F 0
  have hC : PowerSeries.coeff 3
      ((PowerSeries.C (exteriorForwardCoeff F 1)) ^ 2) = 0 := by
    rw [show (PowerSeries.C (exteriorForwardCoeff F 1)) ^ 2 =
      PowerSeries.C ((exteriorForwardCoeff F 1) ^ 2) from
        (map_pow (PowerSeries.C : ℂ →+* PowerSeries ℂ)
          (exteriorForwardCoeff F 1) 2).symm]
    exact PowerSeries.coeff_C_of_ne_zero (by decide : (3 : ℕ) ≠ 0)
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, PowerSeries.coeff_one_pow]
  rw [hsquare, hconst, hC]
  ring

end SpringerLean
