import SpringerLean.DiskCoeff
import Mathlib.MeasureTheory.Integral.CircleAverage

namespace SpringerLean
set_option Elab.async false

/-- Cauchy's coefficient estimate with the actual circle average retained,
rather than replacing it by a maximum. Coefficients are derivative-read. -/
theorem analytic_actualTaylorCoeff_norm_le_circleAverage
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) R)) (n : ℕ) :
    ‖actualTaylorCoeff h n‖ ≤ Real.circleAverage (fun ζ => ‖h ζ‖) 0 1 := by
  have hd : DifferentiableOn ℂ h (Metric.closedBall (0 : ℂ) 1) :=
    hh.differentiableOn.mono (Metric.closedBall_subset_ball hR)
  have hp := hd.hasFPowerSeriesOnBall (R := (1 : NNReal)) (by norm_num)
  have hz : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball,dist_self]
    linarith
  have hcanon := (hh 0 hz).hasFPowerSeriesAt
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hcanon
  norm_num at heq
  have hn := norm_cauchyPowerSeries_le h 0 1 n
  rw [heq] at hn
  simpa [FormalMultilinearSeries.ofScalars,actualTaylorCoeff,
    Real.circleAverage,norm_smul,smul_eq_mul] using hn

end SpringerLean
