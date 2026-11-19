import SpringerLean.Round155SixKernelThirdEntry

set_option maxHeartbeats 2000000

namespace SpringerLean

open PowerSeries

private theorem sixth_shifted_square_coeff_five (g : PowerSeries ℂ) :
    PowerSeries.coeff 5 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 5 g +
      2 * PowerSeries.coeff 1 g * PowerSeries.coeff 4 g +
      2 * PowerSeries.coeff 2 g * PowerSeries.coeff 3 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sixth_shifted_cube_coeff_three (g : PowerSeries ℂ) :
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

/-- The sixth negative mode of the genuine third Faber factor. -/
theorem thirdFaberFactor_actual_mode_nine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 9 =
      3 * (exteriorForwardCoeff F 8 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 6 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 5 +
        2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 3 +
        (3 : ℂ)⁻¹ * exteriorForwardCoeff F 2 ^ 3) := by
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
  have hsq : PowerSeries.coeff 5 (g ^ 2) =
      2 * b₁ * exteriorForwardCoeff F 6 +
      2 * b₂ * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4 := by
    rw [sixth_shifted_square_coeff_five]
    simp only [hg]
    dsimp only [b₁, b₂]
  have hcube : PowerSeries.coeff 3 (g ^ 3) =
      3 * b₁ ^ 2 * exteriorForwardCoeff F 4 +
      6 * b₁ * b₂ * exteriorForwardCoeff F 3 + b₂ ^ 3 := by
    rw [sixth_shifted_cube_coeff_three]
    simp only [hg]
    simp [hg0, b₁, b₂]
  have hseries := thirdFaberFactor_actualTaylorSeries F hc
  rw [← actualTaylorSeries_coeff, hseries]
  change PowerSeries.coeff 9
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
  have hfirst : PowerSeries.coeff 9 (1 : PowerSeries ℂ) = 0 := by simp
  have hsecond : PowerSeries.coeff 9
      (PowerSeries.X ^ 2 * (3 * g - PowerSeries.C (3 * b₁))) =
      3 * exteriorForwardCoeff F 8 := by
    rw [show 9 = 7 + 2 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hg]
  have hthird : PowerSeries.coeff 9
      (PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3) = 0 := by
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_assoc]
  have hfourth : PowerSeries.coeff 9
      (PowerSeries.X ^ 4 * (3 * g ^ 2 - PowerSeries.C (3 * b₁) * g)) =
      3 * (2 * b₁ * exteriorForwardCoeff F 6 +
        2 * b₂ * exteriorForwardCoeff F 5 +
        2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 4) -
      3 * b₁ * exteriorForwardCoeff F 6 := by
    rw [show 9 = 5 + 4 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hsq, hg, PowerSeries.coeff_C_mul, mul_assoc]
  have hfifth : PowerSeries.coeff 9 (PowerSeries.X ^ 6 * g ^ 3) =
      3 * b₁ ^ 2 * exteriorForwardCoeff F 4 +
      6 * b₁ * b₂ * exteriorForwardCoeff F 3 + b₂ ^ 3 := by
    rw [show 9 = 3 + 6 by omega, PowerSeries.coeff_X_pow_mul]
    exact hcube
  rw [hfirst, hsecond, hthird, hfourth, hfifth]
  dsimp only [b₁, b₂]
  ring

/-- The actual third Faber row agrees with the sixth kernel's new entry. -/
theorem thirdFaberFactor_actual_mode_nine_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 9 =
      3 * schoberBiCoeff 6 3
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [thirdFaberFactor_actual_mode_nine F hc,
    schoberKernelQ6_coeff_six_three]

end SpringerLean
