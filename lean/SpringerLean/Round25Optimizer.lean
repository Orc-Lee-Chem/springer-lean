import SpringerLean.Round24ShiftMass

open MeasureTheory Set

namespace SpringerLean

/-- At each positive height the actual BLP auxiliary value can be written
using a genuine bounded measurable minimizing set. -/
theorem regularVerticalAuxiliary_eq_of_actual_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      regularVerticalAuxiliary F s ξ a h =
        (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ a t) +
        (∫ t in Icc (-h) h,
          comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t in E,
          regularExteriorRotatedPotential F s ξ
            ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨E, hE, hmin⟩ :=
    regularVerticalCosts_exists_minimizer F hc hs0 hs1 ξ hξ a h hh
  refine ⟨E, hE, ?_⟩
  simp only [regularVerticalAuxiliary, not_le.mpr hh, ↓reduceIte]
  rw [← hmin]

end SpringerLean
