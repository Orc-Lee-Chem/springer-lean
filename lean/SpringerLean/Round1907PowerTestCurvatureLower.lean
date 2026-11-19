import SpringerLean.Round1906PowerTestCurvature

namespace SpringerLean

/-- The paper's exact compensated convexity curvature bound at positive
radius. The remaining endpoint t=0 follows by continuity of powers
when a≥4. -/
theorem interpolationPowerTest_second_deriv_lower
    {a θ t : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    -2 * (a + 2 * θ) * θ * (1 - θ) *
        interpolationCurvatureConstant a ≤
      deriv (deriv (interpolationPowerTest a θ)) t := by
  have ha0 : a ≠ 0 := by linarith
  have ha2 : a + 2 ≠ 0 := by linarith
  have hp : 0 ≤ a + 2 * θ := by linarith
  have hsec := interpolationCurvatureKernel_secant ha ht ht1 hθ0 hθ1
  have hmul := mul_le_mul_of_nonneg_left hsec hp
  rw [interpolationPowerTest_second_deriv ht ha0 ha2]
  nlinarith

theorem interpolationCurvatureConstant_four :
    interpolationCurvatureConstant 4 = 19 / 84 := by
  norm_num [interpolationCurvatureConstant]

theorem interpolationCurvatureConstant_six :
    interpolationCurvatureConstant 6 = 13 / 168 := by
  norm_num [interpolationCurvatureConstant]

end SpringerLean

#print axioms SpringerLean.interpolationPowerTest_second_deriv_lower
