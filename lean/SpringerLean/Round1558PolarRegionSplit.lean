import SpringerLean.Round1557ActualPowerCircleOrder

open MeasureTheory Set Metric

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Split a compact polar region at one interior radius. The common
circle has zero planar measure, so no boundary term appears. -/
theorem greenPolarRegion_integral_split
    (f : ℂ → ℝ) {a c b : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn f (closedBall (0:ℂ) b)) :
    (∫ z in greenPolarRegion a b, f z) =
      (∫ z in greenPolarRegion a c, f z) +
        (∫ z in greenPolarRegion c b, f z) := by
  let g : ℝ → ℝ := fun r => r*(2*Real.pi)*Real.circleAverage f 0 r
  have hsub : closedBall (0:ℂ) c ⊆ closedBall 0 b := by
    intro z hz
    have hdist : dist z (0:ℂ) ≤ c := by simpa only [mem_closedBall] using hz
    exact mem_closedBall.mpr (hdist.trans hcb)
  have hfc : ContinuousOn f (closedBall (0:ℂ) c) := hf.mono hsub
  have hga : IntegrableOn g (Icc a c) :=
    radial_circleAverage_integrableOn_of_continuousOn_closedBall f ha hfc
  have hgb : IntegrableOn g (Icc c b) :=
    radial_circleAverage_integrableOn_of_continuousOn_closedBall f (ha.trans hac) hf
  have hgab : IntervalIntegrable g volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hac).2 hga
  have hgcb : IntervalIntegrable g volume c b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcb).2 hgb
  rw [greenPolarRegion_integral_eq_radial_circleAverage f ha hf,
      greenPolarRegion_integral_eq_radial_circleAverage f ha hfc,
      greenPolarRegion_integral_eq_radial_circleAverage f (ha.trans hac) hf]
  change (∫ r in Icc a b, g r) =
    (∫ r in Icc a c, g r) + (∫ r in Icc c b, g r)
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (hac.trans hcb),
      ←intervalIntegral.integral_of_le hac,
      ←intervalIntegral.integral_of_le hcb]
  exact (intervalIntegral.integral_add_adjacent_intervals hgab hgcb).symm

end SpringerLean

#print axioms SpringerLean.greenPolarRegion_integral_split
