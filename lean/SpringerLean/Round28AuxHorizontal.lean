import SpringerLean.Round28ActualIntegralHorizontal
import SpringerLean.Round18Continuity

open MeasureTheory Set Metric

namespace SpringerLean

/-- The comparison-potential integral over a fixed centered interval is
continuous in the horizontal coordinate. It is expressed as the actual
potential integral minus one integrable compensated difference. -/
theorem comparisonSegmentPotential_interval_integral_continuousAt_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h : ℝ) (hh : 0 < h) :
    ContinuousAt
      (fun x : ℝ => ∫ t in Icc (-h) h,
        comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)) a := by
  let actual : ℝ → ℝ := fun x => ∫ t in Icc (-h) h,
    regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I)
  let delta : ℝ → ℝ := fun x => ∫ t in Icc (-h) h,
    regularExteriorVerticalPotentialDifference F s ξ x t
  have hActual : ContinuousAt actual a :=
    regularExterior_rotated_potential_interval_integral_continuousAt_horizontal
      F hc hs0 hs1 ξ hξ a h hh
  have hDelta : Continuous delta := by
    let C : NNReal := ⟨2 * Real.pi, by positivity⟩
    have hlip : LipschitzWith C delta := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq]
      exact regularExterior_vertical_difference_setIntegral_lipschitz_horizontal
        F hc hs0 hs1 ξ (Icc (-h) h) x y
    exact hlip.continuous
  have hEq (x : ℝ) :
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)) =
      actual x - delta x := by
    have hE : Icc (-h) h ∈ verticalFeasible h := by
      simpa using centered_interval_verticalFeasible h 0
    have hAi := regularExterior_vertical_cost_integrableOn
      F hc hs0 hs1 ξ hξ x h (Icc (-h) h) hE
    have hDi := (regularExteriorVerticalPotentialDifference_integrable
      F hc hs0 hs1 ξ x).integrableOn (s := Icc (-h) h)
    have halg (t : ℝ) :
        comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I) =
          regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I) -
          regularExteriorVerticalPotentialDifference F s ξ x t := by
      dsimp [regularExteriorVerticalPotentialDifference,
        regularExteriorRotatedPotential, comparisonSegmentPotential]
      ring
    simp_rw [halg]
    exact integral_sub hAi hDi
  have htarget : ContinuousAt (fun x : ℝ => actual x - delta x) a :=
    hActual.sub hDelta.continuousAt
  convert htarget using 1
  funext x
  exact hEq x

/-- At each positive height, the actual BLP auxiliary value is continuous
in the horizontal coordinate, with the minimization still over the paper's
actual bounded-measurable sets. -/
theorem regularVerticalAuxiliary_continuousAt_horizontal_of_pos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h : ℝ) (hh : 0 < h) :
    ContinuousAt (fun x : ℝ => regularVerticalAuxiliary F s ξ x h) a := by
  have hw : Continuous (fun x : ℝ =>
      ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) :=
    regularExteriorVerticalPotentialDifference_integral_continuous
      F hc hs0 hs1 ξ
  have hcomp := comparisonSegmentPotential_interval_integral_continuousAt_horizontal
    F hc hs0 hs1 ξ hξ a h hh
  have hcost := regularVerticalCosts_inf_continuousAt_horizontal
    F hc hs0 hs1 ξ hξ a h hh
  have hEq (x : ℝ) : regularVerticalAuxiliary F s ξ x h =
      (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)) -
      sInf (regularVerticalCosts F s ξ x h) := by
    simp [regularVerticalAuxiliary, not_le.mpr hh]
  have ht := (hw.continuousAt.add hcomp).sub hcost
  convert ht using 1
  funext x
  exact hEq x

end SpringerLean