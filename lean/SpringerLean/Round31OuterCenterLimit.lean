import SpringerLean.Round31CircleUniformAverage

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- At the real center, finite compensated annuli converge to the actual
unbounded outer-tail integral. -/
theorem regularVerticalFiniteAnnulus_tendsto_outer_center
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a T : ℝ) (hT : 0 < T) :
    Tendsto
      (fun n : ℕ => regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)) (a : ℂ))
      atTop (𝓝 (regularVerticalOuterTail F s ξ T (a : ℂ))) := by
  have hU := regularVerticalFiniteAnnulus_tendstoUniformlyOn_circle
    F hc hs0 hs1 ξ a T 0 (le_refl 0) hT
  exact hU.tendsto_at (by simp [mem_sphere])

end SpringerLean