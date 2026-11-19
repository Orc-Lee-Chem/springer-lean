import SpringerLean.Round20PotentialPos

open MeasureTheory Metric MeromorphicOn

namespace SpringerLean

/-- Jensen's formula gives a lower bound for the circle logarithmic norm
of an analytic function by its nonzero center value. -/
theorem analytic_circleAverage_log_norm_ge_center
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤
      Real.circleAverage (fun u : ℂ => Real.log ‖f u‖) 0 1 := by
  have hf' : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hf
  have hJ := hf'.circleAverage_log_norm (by norm_num : (1 : ℝ) ≠ 0) h0
  rw [hJ]
  have hsum : 0 ≤ ∑ᶠ u,
      (divisor f (closedBall (0 : ℂ) |(1 : ℝ)|)) u *
        Real.log (1 * ‖(0 : ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
    · by_cases hu0 : u = 0
      · subst u
        rw [AnalyticOnNhd.divisor_apply hf' (by simp),
          (hf' 0 (by simp)).analyticOrderAt_eq_zero.mpr h0]
        simp
      · have hdiv : 0 ≤ ((divisor f (closedBall (0 : ℂ) |(1 : ℝ)|)) u : ℝ) := by
          exact_mod_cast (AnalyticOnNhd.divisor_nonneg hf') u
        have hnorm : ‖(0 : ℂ) - u‖ ≤ 1 := by
          simpa only [mem_closedBall, dist_eq_norm', abs_one] using hu
        have hnormpos : 0 < ‖(0 : ℂ) - u‖ := by
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu0))
        have hlog : 0 ≤ Real.log (1 * ‖(0 : ℂ) - u‖⁻¹) := by
          rw [one_mul]
          exact Real.log_nonneg ((one_le_inv₀ hnormpos).mpr hnorm)
        exact mul_nonneg hdiv hlog
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith

end SpringerLean
