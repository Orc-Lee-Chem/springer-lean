import SpringerLean.Round123FiveKernelSecondColumn

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- Fifth negative mode of the genuine third Faber factor. -/
theorem thirdFaberFactor_actual_mode_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 8 =
      3 * (exteriorForwardCoeff F 7 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 3 ^ 2 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg (p : ℕ) : PowerSeries.coeff p g =
      exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [b₁, PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [b₂] using hg 1
  have hsq : PowerSeries.coeff 4 (g ^ 2) =
      2 * b₁ * exteriorForwardCoeff F 5 +
      2 * b₂ * exteriorForwardCoeff F 4 +
      exteriorForwardCoeff F 3 ^ 2 := by
    rw [fourthFaber_shifted_square_coeff_four]
    simp only [hg]
    dsimp only [b₁, b₂]
  have hcube : PowerSeries.coeff 2 (g ^ 3) =
      3 * b₁ ^ 2 * exteriorForwardCoeff F 3 +
      3 * b₁ * b₂ ^ 2 := by
    rw [fourthFaber_shifted_cube_coeff_two]
    simp only [hg]
    simp [hg0, b₁, b₂]
  have hseries := thirdFaberFactor_actualTaylorSeries F hc
  rw [← actualTaylorSeries_coeff, hseries]
  change PowerSeries.coeff 8
    (φ ^ 3 - PowerSeries.C (3 * b₁) * PowerSeries.X ^ 2 * φ -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3) = _
  have hform : φ ^ 3 - PowerSeries.C (3 * b₁) * PowerSeries.X ^ 2 * φ -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3 =
      1 + PowerSeries.X ^ 2 * (3 * g - PowerSeries.C (3 * b₁)) -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4 * (3 * g ^ 2 - PowerSeries.C (3 * b₁) * g) +
      PowerSeries.X ^ 6 * g ^ 3 := by
    rw [hφ]
    ring
  rw [hform]
  simp only [map_add, map_sub]
  have hfirst : PowerSeries.coeff 8 (1 : PowerSeries ℂ) = 0 := by simp
  have hsecond : PowerSeries.coeff 8
      (PowerSeries.X ^ 2 * (3 * g - PowerSeries.C (3 * b₁))) =
      3 * exteriorForwardCoeff F 7 := by
    rw [show 8 = 6 + 2 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hg]
  have hthird : PowerSeries.coeff 8
      (PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3) = 0 := by
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_assoc]
  have hfourth : PowerSeries.coeff 8
      (PowerSeries.X ^ 4 * (3 * g ^ 2 - PowerSeries.C (3 * b₁) * g)) =
      3 * (2 * b₁ * exteriorForwardCoeff F 5 +
        2 * b₂ * exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 3 ^ 2) -
      3 * b₁ * exteriorForwardCoeff F 5 := by
    rw [show 8 = 4 + 4 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hsq, hg, PowerSeries.coeff_C_mul, mul_assoc]
  have hfifth : PowerSeries.coeff 8 (PowerSeries.X ^ 6 * g ^ 3) =
      3 * b₁ ^ 2 * exteriorForwardCoeff F 3 +
      3 * b₁ * b₂ ^ 2 := by
    rw [show 8 = 2 + 6 by omega, PowerSeries.coeff_X_pow_mul]
    exact hcube
  rw [hfirst, hsecond, hthird, hfourth, hfifth]
  dsimp only [b₁, b₂]
  ring

/-- The third actual Faber row's fifth column is three times its kernel
coefficient, for the same actual exterior map. -/
theorem thirdFaberFactor_actual_mode_eight_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 8 =
      3 * schoberBiCoeff 5 3
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rw [thirdFaberFactor_actual_mode_eight F hc,
    schoberKernelQ5_coeff_five_three]

end SpringerLean
