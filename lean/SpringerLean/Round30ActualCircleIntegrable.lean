import SpringerLean.Round30VerticalSetCircleIntegrable
import SpringerLean.Round28PotentialUniformStrip

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual rotated potential integrated over any bounded measurable
vertical set is circle integrable at every complex center and radius. -/
theorem regularExterior_rotated_potential_vertical_set_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ) :
    CircleIntegrable
      (fun z : ℂ => ∫ t in E,
        regularExteriorRotatedPotential F s ξ
          (z + (t : ℂ) * Complex.I)) c ρ := by
  apply continuous_vertical_set_integral_circleIntegrable
    (fun t z => regularExteriorRotatedPotential F s ξ
      (z + (t : ℂ) * Complex.I)) ?_ E hEm hEb c ρ
  exact (regularExterior_rotated_potential_continuous
    F hc hs0 hs1 ξ hξ).comp (by fun_prop)

end SpringerLean