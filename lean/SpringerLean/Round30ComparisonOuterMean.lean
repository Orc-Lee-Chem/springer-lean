import SpringerLean.Round30ComparisonSwap
import SpringerLean.Round27ComparisonMean

open MeasureTheory Set Metric

namespace SpringerLean

/-- Translating a real-valued potential before circular averaging translates
the circle center by the same vertical displacement. -/
theorem circleAverage_vertical_translate_general
    (P : ℂ → ℝ) (c : ℂ) (t ρ : ℝ) :
    Real.circleAverage (fun z : ℂ => P (z + (t : ℂ) * Complex.I)) c ρ =
      Real.circleAverage P (c + (t : ℂ) * Complex.I) ρ := by
  rw [Real.circleAverage_def, Real.circleAverage_def]
  congr 1
  simp only [circleMap]
  apply intervalIntegral.integral_congr
  intro θ hθ
  congr 1
  ring

/-- On bounded vertical sets separated from the real comparison segment,
the integrated comparison potential has the exact circle mean-value property. -/
theorem comparisonSegmentPotential_vertical_integral_circleAverage_eq_of_sep
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a h ρ : ℝ) (hρ : 0 < ρ) (hρh : ρ < h)
    (hsep : ∀ t ∈ E, h ≤ |t|) :
    Real.circleAverage
      (fun z : ℂ => ∫ t in E,
        comparisonSegmentPotential (z + (t : ℂ) * Complex.I))
      (a : ℂ) ρ =
    ∫ t in E, comparisonSegmentPotential
      ((a : ℂ) + (t : ℂ) * Complex.I) := by
  rw [← comparisonSegmentPotential_vertical_circle_swap_of_sep
    E hEm hEb a h ρ hρ.le hρh hsep]
  apply setIntegral_congr_fun hEm
  intro t ht
  change Real.circleAverage (fun z : ℂ =>
    comparisonSegmentPotential (z + (t : ℂ) * Complex.I)) (a : ℂ) ρ =
    comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)
  rw [circleAverage_vertical_translate_general]
  apply comparisonSegmentPotential_circleAverage_eq_of_im_radius _ ρ hρ
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, zero_mul, mul_one, zero_add, add_zero] using
    (lt_of_lt_of_le hρh (hsep t ht))

end SpringerLean
