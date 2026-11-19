import SpringerLean.Round31OuterSubmean
import SpringerLean.Round30ActualCenterComplement
import SpringerLean.Round30FiniteComplementMean

open MeasureTheory Set Metric

namespace SpringerLean

noncomputable def regularVerticalBoundedComplement
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (h T : ℝ) (E : Set ℝ) (z : ℂ) : ℝ :=
  (∫ t in Icc (-T) T \ E,
    regularExteriorRotatedPotential F s ξ (z + (t : ℂ) * Complex.I)) -
  (∫ t in Icc (-T) T \ Icc (-h) h,
    comparisonSegmentPotential (z + (t : ℂ) * Complex.I))

/-- Exact complex-coordinate decomposition of a finite complement. -/
theorem regularVerticalFiniteComplement_at_complex
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (h T : ℝ) (E : Set ℝ) (z : ℂ) :
    regularVerticalFiniteComplement F s ξ z.re h T z.im E =
      regularVerticalBoundedComplement F s ξ h T E z +
        regularVerticalOuterTail F s ξ T z := by
  have hz (t : ℝ) :
      (z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * Complex.I =
        z + (t : ℂ) * Complex.I := by
    calc
      (z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * Complex.I =
        (z.re : ℂ) + (z.im : ℂ) * Complex.I + (t : ℂ) * Complex.I := by
          push_cast
          ring
      _ = z + (t : ℂ) * Complex.I := by rw [Complex.re_add_im]
  simp only [regularVerticalFiniteComplement, regularVerticalBoundedComplement,
    regularVerticalOuterTail]
  simp_rw [hz]

end SpringerLean
