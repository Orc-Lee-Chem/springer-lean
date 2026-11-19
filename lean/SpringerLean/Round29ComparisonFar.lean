import SpringerLean.Round29ActualFar
import SpringerLean.Round13Mean

open MeasureTheory Set Metric

namespace SpringerLean

/-- The arcsine comparison segment potential has the same quadratic
far-field bound, with its exact radius-two source bound. -/
theorem comparisonSegmentPotential_far_quadratic
    (z : ℂ) (hz : (4 : ℝ) < ‖z‖) :
    |comparisonSegmentPotential z - Real.log ‖z‖| ≤
      (4 : ℝ) / ‖z‖ ^ 2 := by
  let W : ℂ → ℂ := fun ζ => ((2 * ζ.re : ℝ) : ℂ)
  have hW : ContinuousOn W (sphere (0 : ℂ) 1) := by
    dsimp [W]
    fun_prop
  have hreal : CircleIntegrable (fun ζ : ℂ => 2 * ζ.re) 0 1 := by
    have hc : ContinuousOn (fun ζ : ℂ => 2 * ζ.re) (sphere (0 : ℂ) 1) := by
      fun_prop
    exact hc.circleIntegrable (by norm_num)
  have hmean : Real.circleAverage W 0 1 = 0 := by
    have hmap := Complex.ofRealCLM.circleAverage_comp_comm hreal
    have heq : Real.circleAverage W 0 1 =
        Complex.ofRealCLM (Real.circleAverage (fun ζ : ℂ => 2 * ζ.re) 0 1) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply, W] using hmap
    rw [heq, comparisonCircle_projection_circleAverage_zero (r := 1) (by norm_num)]
    simp
  have hbound : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖W ζ‖ ≤ (2 : ℝ) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hre : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
    have hWnorm : ‖W ζ‖ = |2 * ζ.re| := by simp [W]
    rw [hWnorm, abs_mul]
    have htwo : |(2:ℝ)| = 2 := by norm_num
    rw [htwo, hnorm] at *
    nlinarith
  have h := circleAverage_log_norm_sub_far_of_mean_zero W hW hmean 2
    (by norm_num) hbound z (by norm_num at *; exact hz)
  simpa [comparisonSegmentPotential, W, show (2:ℝ)^2 = 4 by norm_num] using h
end SpringerLean