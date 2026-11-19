import SpringerLean.Round31CircleUniformIntegrable

open MeasureTheory Set Metric Filter

namespace SpringerLean

/-- The actual unbounded compensated outer-tail function is genuinely
circle integrable for every radius strictly below the truncation height. -/
theorem regularVerticalOuterTail_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a T ρ : ℝ) (hρ : 0 < ρ) (hρT : ρ < T) :
    CircleIntegrable (regularVerticalOuterTail F s ξ T) (a : ℂ) ρ := by
  apply circleIntegrable_of_tendstoUniformlyOn
    (fun n : ℕ => regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)))
    (regularVerticalOuterTail F s ξ T) (a : ℂ) ρ
  · intro n
    exact regularExterior_vertical_difference_finite_annulus_circleIntegrable
      F hc hs0 hs1 ξ hξ a T (2 * (n : ℝ)) ρ hρ hρT
  · exact regularVerticalFiniteAnnulus_tendstoUniformlyOn_circle
      F hc hs0 hs1 ξ a T ρ hρ.le hρT

end SpringerLean