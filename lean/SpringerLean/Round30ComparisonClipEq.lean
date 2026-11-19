import SpringerLean.Round30ComparisonClip

open MeasureTheory Set Metric

namespace SpringerLean

/-- Clipping changes nothing at a point whose imaginary part lies at least
the clipping distance from the comparison segment. -/
theorem comparisonSegmentPotentialClipped_eq_of_im
    {δ : ℝ} (z : ℂ) (hz : δ ≤ |z.im|) :
    comparisonSegmentPotentialClipped δ z = comparisonSegmentPotential z := by
  dsimp [comparisonSegmentPotentialClipped, comparisonSegmentPotential]
  apply Real.circleAverage_congr_sphere
  intro ζ _
  change Real.log (max δ ‖z - ((2 * ζ.re : ℝ) : ℂ)‖) =
    Real.log ‖z - ((2 * ζ.re : ℝ) : ℂ)‖
  have him : |z.im| ≤ ‖z - ((2 * ζ.re : ℝ) : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z - ((2 * ζ.re : ℝ) : ℂ))
  rw [max_eq_right (hz.trans him)]

end SpringerLean
