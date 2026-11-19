import SpringerLean.Round31OuterSplit

open MeasureTheory Set

namespace SpringerLean

/-- The actual compensated vertical potential outside a symmetric interval. -/
noncomputable def regularVerticalOuterTail
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (T : ℝ) (z : ℂ) : ℝ :=
  ∫ t in (Icc (-T) T)ᶜ,
    regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)

/-- Its finite-annulus truncation. -/
noncomputable def regularVerticalFiniteAnnulus
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (T M : ℝ) (z : ℂ) : ℝ :=
  ∫ t in Icc (-M) M \ Icc (-T) T,
    regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)

/-- Exact truncation of the actual outer-tail function. -/
theorem regularVerticalOuterTail_eq_finite_add_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ z : ℂ) (T M : ℝ) (hTM : T ≤ M) :
    regularVerticalOuterTail F s ξ T z =
      regularVerticalFiniteAnnulus F s ξ T M z +
      (∫ t in (Icc (-M) M)ᶜ,
        regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) :=
  regularExterior_vertical_difference_outer_split F hc hs0 hs1 ξ z T M hTM

end SpringerLean