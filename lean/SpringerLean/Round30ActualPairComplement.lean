import SpringerLean.Round30CompensatedPair

open MeasureTheory Set

namespace SpringerLean

/-- The actual finite-window complement expression for one vertical translate.
The final tail remains a single integrable potential difference. -/
noncomputable def regularVerticalFiniteComplement
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (x h T ε : ℝ) (E : Set ℝ) : ℝ :=
  (∫ t in Icc (-T) T \ E, regularExteriorRotatedPotential F s ξ
    ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) -
  (∫ t in Icc (-T) T \ Icc (-h) h,
    comparisonSegmentPotential
      ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) +
  (∫ t in (Icc (-T) T)ᶜ,
    regularExteriorVerticalPotentialDifference F s ξ x (t + ε))

/-- The two translated cost terms in the actual auxiliary lower bound are
exactly two finite complements; no divergent whole-line logarithm is formed. -/
theorem regularExterior_actual_finite_complements_pair
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (x h T ε : ℝ)
    (hh : 0 < h) (hT : h ≤ T)
    (E : Set ℝ) (hEm : MeasurableSet E) (hES : E ⊆ Icc (-T) T) :
    2 * (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential
          ((x : ℂ) + ((t - ε : ℝ) : ℂ) * Complex.I)) +
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential
          ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) -
      ((∫ t in E, regularExteriorRotatedPotential F s ξ
          ((x : ℂ) + ((t - ε : ℝ) : ℂ) * Complex.I)) +
       (∫ t in E, regularExteriorRotatedPotential F s ξ
          ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I))) =
      regularVerticalFiniteComplement F s ξ x h T (-ε) E +
        regularVerticalFiniteComplement F s ξ x h T ε E := by
  have hplus := regularExterior_actual_finite_complements_shift
    F hc hs0 hs1 ξ hξ x h T ε hh hT E hEm hES
  have hminus := regularExterior_actual_finite_complements_shift
    F hc hs0 hs1 ξ hξ x h T (-ε) hh hT E hEm hES
  simp only [regularVerticalFiniteComplement, sub_eq_add_neg] at hplus hminus ⊢
  linarith

end SpringerLean