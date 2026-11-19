import SpringerLean.Round30ShiftedTailSigned

open MeasureTheory Set

namespace SpringerLean

/-- The compensated vertical difference at a complex center is exactly the
actual-minus-comparison potential evaluated after vertical translation. -/
theorem regularExteriorVerticalPotentialDifference_at_complex
    (F : ℂ → ℂ) (s : ℝ) (ξ z : ℂ) (t : ℝ) :
    regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im) =
      regularExteriorRotatedPotential F s ξ
        (z + (t : ℂ) * Complex.I) -
      comparisonSegmentPotential (z + (t : ℂ) * Complex.I) := by
  have hz : ((z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * Complex.I) =
      z + (t : ℂ) * Complex.I := by
    calc
      ((z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * Complex.I) =
          ((z.re : ℂ) + (z.im : ℂ) * Complex.I) + (t : ℂ) * Complex.I := by
        push_cast
        ring
      _ = z + (t : ℂ) * Complex.I := by rw [Complex.re_add_im]
  simp only [regularExteriorVerticalPotentialDifference,
    regularExteriorRotatedPotential, comparisonSegmentPotential, hz]

end SpringerLean