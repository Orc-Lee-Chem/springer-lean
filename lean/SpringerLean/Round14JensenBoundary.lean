import SpringerLean.Round14Potential

open MeasureTheory Metric

namespace SpringerLean

/-- Jensen's formula with possible zeros on the integration circle. The
boundary-zero terms vanish, so no boundary nonvanishing premise is needed. -/
theorem circleAverage_log_norm_of_no_openDisk_zeros
    (f : ℂ → ℂ)
    (hAnal : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0)
    (hno : ∀ u : ℂ, ‖u‖ < 1 → f u ≠ 0) :
    Real.circleAverage (fun u : ℂ => Real.log ‖f u‖) 0 1 =
      Real.log ‖f 0‖ := by
  have hAnal' : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hAnal
  have hJ := hAnal'.circleAverage_log_norm
    (R := (1 : ℝ)) (c := (0 : ℂ)) (by norm_num) hf0
  norm_num at hJ
  have hterm (u : ℂ) :
      -((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u : ℝ) *
        Real.log ‖u‖) = 0 := by
    by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
    · have hle : ‖u‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right, abs_one] using hu
      by_cases hlt : ‖u‖ < 1
      · have horder : analyticOrderAt f u = 0 :=
          ((hAnal' u hu).analyticOrderAt_eq_zero).mpr (hno u hlt)
        rw [MeromorphicOn.divisor_apply hAnal'.meromorphicOn hu,
          (hAnal' u hu).meromorphicOrderAt_eq, horder]
        simp
      · have heq : ‖u‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
        simp [heq]
    · have hdiv : MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u = 0 := by
        have hu' : u ∉ closedBall (0 : ℂ) 1 := by simpa using hu
        rw [MeromorphicOn.divisor_def]
        simp [hu']
      rw [hdiv]
      simp
  have hsum :
      (∑ᶠ u : ℂ, -((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u : ℝ) *
        Real.log ‖u‖)) = 0 :=
    finsum_eq_zero_of_forall_eq_zero hterm
  rw [hsum] at hJ
  simpa only [zero_add] using hJ

end SpringerLean