import SpringerLean.Round27LogDoubleCircle

open MeasureTheory Set Metric

namespace SpringerLean

/-- Global circular submean for the actual regularized boundary logarithmic
potential. This holds at every center and for every positive radius, even
when the outer circle crosses the actual boundary curve. -/
theorem regularExterior_boundary_potential_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 ≤
      Real.circleAverage
        (fun u : ℂ => Real.circleAverage
          (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - u‖) 0 1) w ρ := by
  let G := rescaleExterior s F
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn G (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hz : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hz).continuousAt.continuousWithinAt
  obtain ⟨M, hM0, hM⟩ :=
    regularExterior_boundary_curve_norm_bounded F hc hs0 hs1
  by_cases hw : w ∈ G '' sphere (0 : ℂ) 1
  · obtain ⟨ζ, hζ, rfl⟩ := hw
    have hζnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hzero := regularExterior_curve_boundary_log_potential_zero
      F hc hs0 hs1 hζnorm
    change Real.circleAverage
      (fun η : ℂ => Real.log ‖G η - G ζ‖) 0 1 = 0 at hzero
    rw [hzero]
    apply Real.circleAverage_nonneg_of_nonneg
    intro u hu
    exact regularExterior_boundary_potential_nonneg F hc hs0 hs1 u
  · have h := boundary_log_potential_circle_submean_of_not_mem_curve
        G hG M hM w hw ρ hρ
    simpa only [G, norm_sub_rev] using h

end SpringerLean