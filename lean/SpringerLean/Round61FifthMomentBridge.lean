import SpringerLean.Round60FifthCoeff
import SpringerLean.Round12CompareMoments

namespace SpringerLean

open MeasureTheory

/-- A sharp actual fourth filling moment suffices for the universal fifth coefficient. -/
theorem exteriorInverseCoeff_five_norm_le_two_of_fourth_moment_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hM : actualHarmonicMoment F 4 ≤ 2) :
    ‖exteriorInverseCoeff F 5‖ ≤ 2 := by
  have hM0 : 0 ≤ actualHarmonicMoment F 4 := by
    unfold actualHarmonicMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hA0 : 0 ≤ actualOmittedMoment F 4 := by
    unfold actualOmittedMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hCS := exteriorInverseCoeff_odd_norm_sq_le_moment_product F hc
    (k := 3) (by norm_num)
  norm_num at hCS
  have hMA : 0 ≤ actualHarmonicMoment F 4 * actualOmittedMoment F 4 :=
    mul_nonneg hM0 hA0
  have hM2 : actualHarmonicMoment F 4 ^ 2 ≤ 4 := by nlinarith
  have hB2 : ‖exteriorInverseCoeff F 5‖ ^ 2 ≤ 4 := by nlinarith
  nlinarith [norm_nonneg (exteriorInverseCoeff F 5)]

/-- Under the moment bound, fifth-coefficient equality forces moment saturation. -/
theorem exteriorInverseCoeff_five_eq_two_fourth_moment_saturation
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hM : actualHarmonicMoment F 4 ≤ 2)
    (hB : ‖exteriorInverseCoeff F 5‖ = 2) :
    actualHarmonicMoment F 4 = 2 := by
  have hM0 : 0 ≤ actualHarmonicMoment F 4 := by
    unfold actualHarmonicMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hA0 : 0 ≤ actualOmittedMoment F 4 := by
    unfold actualOmittedMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hCS := exteriorInverseCoeff_odd_norm_sq_le_moment_product F hc
    (k := 3) (by norm_num)
  norm_num at hCS
  rw [hB] at hCS
  have hMA : 0 ≤ actualHarmonicMoment F 4 * actualOmittedMoment F 4 :=
    mul_nonneg hM0 hA0
  nlinarith


/-- The unrotated slit saturates the fourth filling moment at Catalan(2)=2. -/
theorem slitMap_one_actualHarmonicMoment_four :
    actualHarmonicMoment (slitMap 1) 4 = 2 := by
  unfold actualHarmonicMoment
  simp_rw [slitMap_one_actualHarmonic_eq_two_re]
  simpa [Complex.norm_real, Real.norm_eq_abs, catalan_two] using
    (comparisonDisk_absoluteMoment 2)


/-- A strict fourth filling moment gives the high-range strict coefficient bound. -/
theorem exteriorInverseCoeff_five_norm_lt_two_of_fourth_moment_lt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hM : actualHarmonicMoment F 4 < 2) :
    ‖exteriorInverseCoeff F 5‖ < 2 := by
  have hle := exteriorInverseCoeff_five_norm_le_two_of_fourth_moment_le
    F hc hM.le
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · have hsat := exteriorInverseCoeff_five_eq_two_fourth_moment_saturation
      F hc hM.le heq
    exact (ne_of_lt hM hsat).elim

end SpringerLean