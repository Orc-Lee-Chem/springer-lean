import SpringerLean.Round27ActualL1

open MeasureTheory Set

namespace SpringerLean

/-- Integrating the actual compensated potential over any measurable part
of a vertical line preserves its horizontal Lipschitz bound. -/
theorem regularExterior_vertical_difference_setIntegral_lipschitz_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (S : Set ℝ) (a a' : ℝ) :
    |(∫ y in S, regularExteriorVerticalPotentialDifference F s ξ a y) -
      (∫ y in S, regularExteriorVerticalPotentialDifference F s ξ a' y)| ≤
      2 * Real.pi * |a - a'| := by
  have ha := regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a
  have hb := regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a'
  have hd := ha.sub hb
  have hOnA := ha.integrableOn (s := S)
  have hOnB := hb.integrableOn (s := S)
  calc
    |(∫ y in S, regularExteriorVerticalPotentialDifference F s ξ a y) -
      (∫ y in S, regularExteriorVerticalPotentialDifference F s ξ a' y)| =
        |∫ y in S, regularExteriorVerticalPotentialDifference F s ξ a y -
          regularExteriorVerticalPotentialDifference F s ξ a' y| := by
          rw [integral_sub hOnA hOnB]
    _ ≤ ∫ y in S, |regularExteriorVerticalPotentialDifference F s ξ a y -
        regularExteriorVerticalPotentialDifference F s ξ a' y| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, |regularExteriorVerticalPotentialDifference F s ξ a y -
        regularExteriorVerticalPotentialDifference F s ξ a' y| :=
      setIntegral_le_integral hd.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    _ ≤ 2 * Real.pi * |a - a'| :=
      regularExterior_vertical_difference_L1_lipschitz_horizontal
        F hc hs0 hs1 ξ a a'

end SpringerLean