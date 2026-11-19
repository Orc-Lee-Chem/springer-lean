import SpringerLean.Round31OuterAverageLimit

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- The actual unbounded compensated outer tail satisfies the circle submean.
All terms remain compensated on the unbounded set. -/
theorem regularVerticalOuterTail_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a T ρ : ℝ) (hρ : 0 < ρ) (hρT : ρ < T) :
    regularVerticalOuterTail F s ξ T (a : ℂ) ≤
      Real.circleAverage (regularVerticalOuterTail F s ξ T) (a : ℂ) ρ := by
  have hleft := regularVerticalFiniteAnnulus_tendsto_outer_center
    F hc hs0 hs1 ξ a T (lt_trans hρ hρT)
  have hright := regularVerticalFiniteAnnulus_circleAverage_tendsto_outer
    F hc hs0 hs1 ξ hξ a T ρ hρ hρT
  have hbound : ∀ᶠ n : ℕ in atTop,
      regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)) (a : ℂ) ≤
        Real.circleAverage
          (regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ))) (a : ℂ) ρ := by
    filter_upwards [(eventually_ge_atTop (Nat.ceil T))] with n hn
    have hTn : T ≤ 2 * (n : ℝ) := by
      have hT0 : T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
      have hN : (Nat.ceil T : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hN0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have h := regularExterior_vertical_difference_finite_annulus_submean
      F hc hs0 hs1 ξ hξ a T (2 * (n : ℝ)) ρ hρ hρT hTn
    have heq : regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)) =
      (fun z : ℂ => ∫ t in Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)) \ Icc (-T) T,
        regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) := rfl
    rw [heq]
    simpa only [Complex.ofReal_re, Complex.ofReal_im, add_zero] using h

  exact le_of_tendsto_of_tendsto hleft hright hbound

end SpringerLean