import SpringerLean.Round77FaberThree

namespace SpringerLean

/-- The first basis row of the finite Grunsky matrix is precisely the
ordinary finite exterior area sum. This is the part of matrix contraction
already supplied by the verified area theorem. -/
theorem schoberFiniteC_first_row_energy
    (b1 b2 b3 b4 b5 : ℂ) :
    (∑ j : Fin 3, ‖schoberFiniteC b1 b2 b3 b4 b5 0 j‖ ^ 2) =
      ‖b1‖ ^ 2 + 2 * ‖b2‖ ^ 2 + 3 * ‖b3‖ ^ 2 := by
  rw [Fin.sum_univ_three]
  simp [schoberFiniteC, schoberKernelQ3_coeff_one_one,
    schoberKernelQ3_coeff_one_two, schoberKernelQ3_coeff_one_three,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem schoberFiniteC_first_row_energy_le_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let b1 := exteriorForwardCoeff F 1
    let b2 := exteriorForwardCoeff F 2
    let b3 := exteriorForwardCoeff F 3
    let b4 := exteriorForwardCoeff F 4
    let b5 := exteriorForwardCoeff F 5
    (∑ j : Fin 3, ‖schoberFiniteC b1 b2 b3 b4 b5 0 j‖ ^ 2) ≤ 1 := by
  dsimp
  rw [schoberFiniteC_first_row_energy]
  have h := exteriorForwardCoeff_finite_area F hc 3
  norm_num [Finset.sum_Icc_succ_top] at h
  nlinarith

end SpringerLean
