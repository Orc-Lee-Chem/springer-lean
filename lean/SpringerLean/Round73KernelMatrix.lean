import SpringerLean.Round72ActualRows

namespace SpringerLean

/-- The full three by three logarithmic coefficient matrix is symmetric.
The off-diagonal entries contain the nonlinear product of the first two coefficients. -/
theorem schoberFiniteC_symmetric
    (b1 b2 b3 b4 b5 : ℂ) (i j : Fin 3) :
    schoberFiniteC b1 b2 b3 b4 b5 i j =
      schoberFiniteC b1 b2 b3 b4 b5 j i := by
  fin_cases i <;> fin_cases j <;>
    simp [schoberFiniteC,
      schoberKernelQ3_coeff_one_two, schoberKernelQ3_coeff_two_one,
      schoberKernelQ3_coeff_one_three, schoberKernelQ3_coeff_three_one,
      schoberKernelQ3_coeff_two_three, schoberKernelQ3_coeff_three_two,
      mul_comm]

end SpringerLean
