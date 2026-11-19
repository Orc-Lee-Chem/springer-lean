import SpringerLean.Round30ActualPairSemicircle

open MeasureTheory Set

namespace SpringerLean

/-- The whole-line compensated potential, unlike either logarithmic potential
separately, is integrable and invariant under a vertical translation. -/
theorem regularExterior_vertical_difference_integral_shift
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a ε : ℝ) :
    (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a (t + ε)) =
    (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a t) := by
  exact integral_add_right_eq_self
    (fun t : ℝ => regularExteriorVerticalPotentialDifference F s ξ a t) ε

/-- The sign-reversed vertical translate has the same whole-line compensated
integral. The two directions are both needed for paired angles. -/
theorem regularExterior_vertical_difference_integral_shift_sub
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a ε : ℝ) :
    (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a (t - ε)) =
    (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a t) := by
  simpa only [sub_eq_add_neg] using
    regularExterior_vertical_difference_integral_shift F s ξ a (-ε)

end SpringerLean