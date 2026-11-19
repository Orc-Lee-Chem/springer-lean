import SpringerLean.Round17ImagMean

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual regularized boundary logarithm is integrable in the angle
variable for every point on every vertical line. -/
theorem regularExterior_rotated_log_angle_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a y : ℝ) :
    IntegrableOn
      (fun θ : ℝ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
        conj ξ * rescaleExterior s F (circleMap 0 1 θ)‖)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
  let w : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have h := regularExterior_rotated_log_circleIntegrable F hc hs0 hs1 ξ w
  have hi : IntegrableOn
      (fun θ : ℝ => Real.log ‖conj ξ * rescaleExterior s F (circleMap 0 1 θ) - w‖)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using
      (intervalIntegrable_iff).mp h
  convert hi using 1
  funext θ
  exact congrArg Real.log (norm_sub_rev w _)

theorem comparisonCircle_log_angle_integrable (a y : ℝ) :
    IntegrableOn
      (fun θ : ℝ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
        ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ)‖)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
  let w : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have h := comparisonCircle_log_circleIntegrable w
  have hi : IntegrableOn
      (fun θ : ℝ => Real.log ‖((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) - w‖)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using
      (intervalIntegrable_iff).mp h
  convert hi using 1
  funext θ
  exact congrArg Real.log (norm_sub_rev w _)

/-- For every vertical coordinate, the imaginary correction cancels in
the actual-minus-comparison angular potential difference. -/
theorem regularExterior_compensated_eq_raw_angle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a y : ℝ) :
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      verticalPointKernel a
        (conj ξ * rescaleExterior s F (circleMap 0 1 θ)) y) -
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      verticalPointKernel a
        ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) y) =
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
        conj ξ * rescaleExterior s F (circleMap 0 1 θ)‖) -
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
        ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ)‖) := by
  apply verticalCurveKernel_difference_eq_raw a y
    (fun θ : ℝ => conj ξ * rescaleExterior s F (circleMap 0 1 θ))
    (fun θ : ℝ => ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ))
    (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
    comparisonCircle_angle_continuous
    (regularExterior_rotated_log_angle_integrable F hc hs0 hs1 ξ a y)
    (comparisonCircle_log_angle_integrable a y)
  rw [rescaleExterior_imaginary_angle_integral_zero F hc hs0 hs1 ξ]
  simp

end SpringerLean
