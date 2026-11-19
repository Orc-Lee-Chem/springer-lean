import SpringerLean.Round31OuterCenterLimit

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- Circle averages of the actual finite annuli converge to the circle
average of the genuinely circle-integrable unbounded outer tail. -/
theorem regularVerticalFiniteAnnulus_circleAverage_tendsto_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a T ρ : ℝ) (hρ : 0 < ρ) (hρT : ρ < T) :
    Tendsto
      (fun n : ℕ => Real.circleAverage
        (regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ))) (a : ℂ) ρ)
      atTop (𝓝 (Real.circleAverage
        (regularVerticalOuterTail F s ξ T) (a : ℂ) ρ)) := by
  apply circleAverage_tendsto_of_tendstoUniformlyOn
  · intro n
    exact regularExterior_vertical_difference_finite_annulus_circleIntegrable
      F hc hs0 hs1 ξ hξ a T (2 * (n : ℝ)) ρ hρ hρT
  · exact regularVerticalOuterTail_circleIntegrable
      F hc hs0 hs1 ξ hξ a T ρ hρ hρT
  · exact regularVerticalFiniteAnnulus_tendstoUniformlyOn_circle
      F hc hs0 hs1 ξ a T ρ hρ.le hρT

end SpringerLean