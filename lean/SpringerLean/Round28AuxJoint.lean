import SpringerLean.Round28ComparisonJoint
import SpringerLean.Round28CostJoint
import SpringerLean.Round18Continuity

open MeasureTheory Set Filter

namespace SpringerLean

/-- The actual finite-interval BLP auxiliary function is jointly continuous
at each point of positive height. -/
theorem regularVerticalAuxiliary_continuousAt_positive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ContinuousAt (fun p : ℝ × ℝ => regularVerticalAuxiliary F s ξ p.1 p.2) (a, h) := by
  have hw : Continuous (fun x : ℝ =>
      ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) :=
    regularExteriorVerticalPotentialDifference_integral_continuous F hc hs0 hs1 ξ
  have hw' : ContinuousAt (fun p : ℝ × ℝ =>
      ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ p.1 t) (a, h) :=
    hw.continuousAt.comp continuousAt_fst
  have hcomp := comparisonSegmentPotential_interval_integral_continuousAt_positive
    F hc hs0 hs1 ξ hξ a h hh
  have hcost := regularVerticalCosts_inf_continuousAt_positive
    F hc hs0 hs1 ξ hξ a h hh
  have hExpr := (hw'.add hcomp).sub hcost
  apply hExpr.congr_of_eventuallyEq
  have hpos : ∀ᶠ p : ℝ × ℝ in nhds (a, h), 0 < p.2 := by
    have hopen : IsOpen {p : ℝ × ℝ | 0 < p.2} :=
      isOpen_lt continuous_const continuous_snd
    exact hopen.mem_nhds (show (a, h) ∈ {p : ℝ × ℝ | 0 < p.2} from hh)
  filter_upwards [hpos] with p hp
  simp [regularVerticalAuxiliary, not_le.mpr hp]
end SpringerLean