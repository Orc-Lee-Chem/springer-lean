import SpringerLean.Round99KernelFour

namespace SpringerLean

/-- The first row of the degree-four logarithmic kernel agrees with the
first three entries of the previously verified degree-three kernel. -/
theorem schoberKernelQ4_first_row_low
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    let Q := schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇
    schoberBiCoeff 1 1 Q = b₁ ∧
    schoberBiCoeff 2 1 Q = b₂ ∧
    schoberBiCoeff 3 1 Q = b₃ := by
  dsimp only
  simp only [schoberBiCoeff, schoberKernelQ4_outer_one]
  simp [schoberKernelT4Row, PowerSeries.coeff_X_pow]

/-- The first actual Faber row agrees with the first row of the same
degree-four logarithmic kernel, including its newly checked fourth column. -/
theorem fourthActualFaberMode_first_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 4) :
    fourthActualFaberMode F 0 j =
      schoberBiCoeff (j.val + 1) 1
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  fin_cases j
  · simp only [fourthActualFaberMode, ↓reduceIte, Fin.val_zero,
      Nat.zero_add, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 1]
    exact (schoberKernelQ4_first_row_low ..).1.symm
  · simp only [fourthActualFaberMode, ↓reduceIte, Fin.val_one,
      Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 2]
    exact (schoberKernelQ4_first_row_low ..).2.1.symm
  · simp only [fourthActualFaberMode, ↓reduceIte, Fin.val_two,
      Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 3]
    exact (schoberKernelQ4_first_row_low ..).2.2.symm
  · simp only [fourthActualFaberMode, ↓reduceIte,
      Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 4]
    exact (schoberKernelQ4_coeff_four_one ..).symm

/-- The fourth negative mode of the second actual Faber factor. -/
theorem secondFaberFactor_actual_mode_six
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 6 =
      2 * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 2 := by
  let φ := actualTaylorSeries (exteriorPhi F)
  have hs := secondFaberFactor_actualTaylorSeries F hc
  rw [← actualTaylorSeries_coeff, hs]
  rw [← exteriorPhi_actualTaylorSeries F hc]
  change PowerSeries.coeff 6
    (φ ^ 2 - PowerSeries.C (2 * exteriorForwardCoeff F 1) *
      PowerSeries.X ^ 2) = _
  simp only [map_sub, PowerSeries.coeff_C_mul]
  have hcor : PowerSeries.coeff 6 (PowerSeries.X ^ 2 : PowerSeries ℂ) = 0 := by
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

/-- The fourth column of the second actual Faber row is twice the
corresponding degree-four logarithmic-kernel coefficient. -/
theorem secondFaberFactor_actual_mode_six_eq_logKernel4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 6 =
      2 * schoberBiCoeff 4 2
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  rw [secondFaberFactor_actual_mode_six F hc,
    schoberKernelQ4_coeff_four_two]
  ring

end SpringerLean
