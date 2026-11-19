import SpringerLean.Round31AnnulusCircleIntegrable
import SpringerLean.Round30OuterSplit

open MeasureTheory Set

namespace SpringerLean

/-- The actual unbounded compensated outer integral is the finite annulus
plus an outer tail, at every complex parameter point. -/
theorem regularExterior_vertical_difference_outer_split
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ z : ℂ) (T M : ℝ) (hTM : T ≤ M) :
    (∫ t in (Icc (-T) T)ᶜ,
      regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) =
    (∫ t in Icc (-M) M \ Icc (-T) T,
      regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) +
    (∫ t in (Icc (-M) M)ᶜ,
      regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) := by
  let f : ℝ → ℝ := fun t =>
    regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)
  have hInt : Integrable f :=
    (regularExteriorVerticalPotentialDifference_integrable
      F hc hs0 hs1 ξ z.re).comp_add_right z.im
  have hSM : Icc (-T) T ⊆ Icc (-M) M := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact integral_compl_eq_sdiff_add_compl f hInt
    (Icc (-T) T) (Icc (-M) M)
    measurableSet_Icc measurableSet_Icc hSM

end SpringerLean