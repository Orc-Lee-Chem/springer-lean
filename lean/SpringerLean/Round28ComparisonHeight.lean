import SpringerLean.Round28CostJoint
import SpringerLean.Round28ActualPotentialContinuous
import SpringerLean.Round28AuxHorizontal

open MeasureTheory Set Metric

namespace SpringerLean

/-- Along any vertical line the comparison logarithmic potential is locally integrable. -/
theorem comparisonSegmentPotential_vertical_intervalIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a b c : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I))
      volume b c := by
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let d : ℝ → ℝ := regularExteriorVerticalPotentialDifference F s ξ a
  have hmap : Continuous (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hg : Continuous g :=
    (regularExterior_rotated_potential_continuous F hc hs0 hs1 ξ hξ).comp hmap
  have hd : Integrable d :=
    regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a
  have hEq (t : ℝ) :
      comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I) = g t - d t := by
    change comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I) =
      regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I) -
      regularExteriorVerticalPotentialDifference F s ξ a t
    dsimp [regularExteriorVerticalPotentialDifference,
      regularExteriorRotatedPotential, comparisonSegmentPotential]
    ring
  simpa only [hEq] using (hg.intervalIntegrable b c).sub hd.intervalIntegrable

/-- For fixed horizontal coordinate the comparison integral is continuous in interval height. -/
theorem comparisonSegmentPotential_interval_integral_continuousAt_height
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ContinuousAt
      (fun u : ℝ => ∫ t in Icc (-u) u,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) h := by
  let f : ℝ → ℝ := fun t => comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)
  have hf (b c : ℝ) : IntervalIntegrable f volume b c :=
    comparisonSegmentPotential_vertical_intervalIntegrable
      F hc hs0 hs1 ξ hξ a b c
  let P : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, f t
  have hP : Continuous P := intervalIntegral.continuous_primitive hf 0
  have hEq (u : ℝ) (hu : 0 ≤ u) :
      (∫ t in Icc (-u) u, f t) = P u - P (-u) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
    exact (intervalIntegral.integral_interval_sub_left (hf 0 u) (hf 0 (-u))).symm
  have hcont : ContinuousAt (fun u : ℝ => P u - P (-u)) h :=
    hP.continuousAt.sub (hP.comp continuous_neg).continuousAt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hh] with u hu
  exact hEq u hu.le
end SpringerLean