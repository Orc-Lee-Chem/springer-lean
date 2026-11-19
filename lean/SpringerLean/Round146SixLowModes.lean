import SpringerLean.Round145SixFactorSeries
import SpringerLean.Round138SixthPrelude

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The sixth Faber factor separated into the coefficients relevant to its
six positive Fourier modes and a remainder divisible by `X⁷`. -/
theorem sixthFaberFormalFactor_low_expansion (F : ℂ → ℂ) :
    let g := schoberActualForwardShift F
    let c₂ : PowerSeries ℂ := -(PowerSeries.C (6 * exteriorForwardCoeff F 1))
    let c₃ : PowerSeries ℂ := -(PowerSeries.C (6 * exteriorForwardCoeff F 2))
    let c₄ : PowerSeries ℂ := PowerSeries.C
      (9 * exteriorForwardCoeff F 1 ^ 2 - 6 * exteriorForwardCoeff F 3)
    let c₅ : PowerSeries ℂ := PowerSeries.C
      (12 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 -
        6 * exteriorForwardCoeff F 4)
    let c₆ : PowerSeries ℂ := PowerSeries.C
      (-2 * exteriorForwardCoeff F 1 ^ 3 +
        6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        3 * exteriorForwardCoeff F 2 ^ 2 - 6 * exteriorForwardCoeff F 5)
    sixthFaberFormalFactor F =
      1 + X ^ 2 * (6 * g + c₂) + X ^ 3 * c₃ +
        X ^ 4 * (15 * g ^ 2 + 4 * c₂ * g + c₄) +
        X ^ 5 * (3 * c₃ * g + c₅) +
        X ^ 6 * (20 * g ^ 3 + 6 * c₂ * g ^ 2 + 2 * c₄ * g + c₆) +
        X ^ 7 * (c₅ * g + 3 * c₃ * g ^ 2 +
          X * (15 * g ^ 4 + 4 * c₂ * g ^ 3 + c₄ * g ^ 2) +
          X ^ 2 * (c₃ * g ^ 3) +
          X ^ 3 * (6 * g ^ 5 + c₂ * g ^ 4) +
          X ^ 5 * g ^ 6) := by
  let f := exteriorFormalForward F
  let g := schoberActualForwardShift F
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = X * g := by
    simpa [g, schoberActualForwardShift, hf0] using
      (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : formalExteriorPhi f = 1 + X ^ 2 * g := by
    rw [formalExteriorPhi, hf]
    ring
  dsimp only
  dsimp [sixthFaberFormalFactor]
  rw [hφ]
  dsimp only [g]
  ring

/-- The positive frequency six of the actual sixth Faber boundary curve. -/
theorem sixthFaberFactor_actual_coeff_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 0 = 1 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul']

/-- The next positive Fourier frequency is absent. -/
theorem sixthFaberFactor_actual_coeff_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 1 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul']

/-- The first nontrivial Faber cancellation. -/
theorem sixthFaberFactor_actual_coeff_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 2 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff]
  simp only [map_natCast, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [schoberActualForwardShift_coeff]
  have h6 : PowerSeries.coeff 0 (6 : PowerSeries ℂ) = 6 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.constantCoeff ((6 : ℕ) : PowerSeries ℂ) =
      ((6 : ℕ) : ℂ)
    simp only [map_natCast]
  rw [h6]
  ring

theorem sixthFaberFactor_actual_coeff_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 3 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff]

theorem sixthFaberFactor_actual_coeff_four
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 4 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [schoberActualForwardShift_coeff]
  simp only [map_ofNat]
  ring

theorem sixthFaberFactor_actual_coeff_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 5 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff,
    schoberActualForwardShift_square_coeff, Finset.sum_range_succ]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.coeff_mul, Finset.sum_range_succ,
    PowerSeries.coeff_C, schoberActualForwardShift_coeff]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, PowerSeries.coeff_one_pow,
    PowerSeries.coeff_C]
  simp only [map_ofNat]
  ring

theorem sixthFaberFactor_actual_coeff_six
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 6 = 0 := by
  rw [← actualTaylorSeries_coeff,
    sixthFaberFactor_actualTaylorSeries F hc,
    sixthFaberFormalFactor_low_expansion F]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    schoberActualForwardShift_coeff,
    schoberActualForwardShift_square_coeff, Finset.sum_range_succ]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.coeff_mul, Finset.sum_range_succ,
    PowerSeries.coeff_C, schoberActualForwardShift_coeff]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, PowerSeries.coeff_one_pow,
    PowerSeries.coeff_C]
  simp only [map_ofNat]
  have hC : (PowerSeries.C (exteriorForwardCoeff F 1)) ^ 2 =
      PowerSeries.C ((exteriorForwardCoeff F 1) ^ 2) :=
    (map_pow (PowerSeries.C : ℂ →+* PowerSeries ℂ)
      (exteriorForwardCoeff F 1) 2).symm
  rw [hC, PowerSeries.coeff_C_of_ne_zero (by decide : (2 : ℕ) ≠ 0)]
  ring

/-- All nonnegative Fourier modes of the sixth Faber polynomial are now
read from actual Taylor derivatives: only the leading `+6` mode remains. -/
theorem sixthFaberFactor_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 0 = 1 ∧
    actualTaylorCoeff (sixthFaberFactor F) 1 = 0 ∧
    actualTaylorCoeff (sixthFaberFactor F) 2 = 0 ∧
    actualTaylorCoeff (sixthFaberFactor F) 3 = 0 ∧
    actualTaylorCoeff (sixthFaberFactor F) 4 = 0 ∧
    actualTaylorCoeff (sixthFaberFactor F) 5 = 0 ∧
    actualTaylorCoeff (sixthFaberFactor F) 6 = 0 := by
  exact ⟨sixthFaberFactor_actual_coeff_zero F hc,
    sixthFaberFactor_actual_coeff_one F hc,
    sixthFaberFactor_actual_coeff_two F hc,
    sixthFaberFactor_actual_coeff_three F hc,
    sixthFaberFactor_actual_coeff_four F hc,
    sixthFaberFactor_actual_coeff_five F hc,
    sixthFaberFactor_actual_coeff_six F hc⟩

end SpringerLean
