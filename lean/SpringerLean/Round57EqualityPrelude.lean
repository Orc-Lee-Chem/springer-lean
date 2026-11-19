import SpringerLean.Round56SecondMoment

namespace SpringerLean

/-- Equality in the actual third inverse-coefficient bound forces saturation
of the filling second moment and vanishing of the omitted second moment. -/
theorem exteriorInverseCoeff_three_eq_one_moment_saturation
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hB : ‖exteriorInverseCoeff F 3‖ = 1) :
    actualHarmonicMoment F 2 = 1 ∧ actualOmittedMoment F 2 = 0 := by
  have hM : actualHarmonicMoment F 2 ≤ 1 :=
    actualHarmonicMoment_two_le_one F hc
  have hM0 : 0 ≤ actualHarmonicMoment F 2 := by
    unfold actualHarmonicMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply MeasureTheory.integral_nonneg
    intro z
    positivity
  have hA0 : 0 ≤ actualOmittedMoment F 2 := by
    unfold actualOmittedMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply MeasureTheory.integral_nonneg
    intro z
    positivity
  have hCS := exteriorInverseCoeff_odd_norm_sq_le_moment_product F hc
    (k := 2) (by norm_num)
  norm_num at hCS
  rw [hB] at hCS
  norm_num at hCS
  have hMA : 0 ≤ actualHarmonicMoment F 2 * actualOmittedMoment F 2 :=
    mul_nonneg hM0 hA0
  have hM2 : actualHarmonicMoment F 2 ^ 2 ≤ 1 := by nlinarith
  have hMeq : actualHarmonicMoment F 2 = 1 := by nlinarith
  constructor
  · exact hMeq
  · rw [hMeq] at hCS
    nlinarith

end SpringerLean