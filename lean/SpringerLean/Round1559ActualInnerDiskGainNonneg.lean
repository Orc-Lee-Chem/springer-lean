import SpringerLean.Round1558PolarRegionSplit

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The projected positive-power saving is nonnegative throughout every
compact disk strictly inside the unit disk. -/
theorem actualHarmonic_positivePower_innerDisk_gain_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ ∫ z in greenPolarRegion 0 a,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m := by
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  let f : ℂ → ℝ := fun z => Y z-X z
  have hsub : closedBall (0:ℂ) a ⊆ ball 0 1 := by
    intro z hz
    have hn : ‖z‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right] using hn.trans_lt ha1
  have hH := (actualHarmonic_continuousOn_unitBall F hc).mono hsub
  have hX : ContinuousOn X (closedBall (0:ℂ) a) := by
    have hproj : ContinuousOn
        (fun z : ℂ => (conj ξ*actualHarmonic F z).re)
        (closedBall (0:ℂ) a) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_const.mul hH)
    exact (continuous_max.comp_continuousOn
      (hproj.prodMk continuousOn_const)).pow m
  have hY : ContinuousOn Y (closedBall (0:ℂ) a) := by
    dsimp [Y]
    fun_prop
  have hf : ContinuousOn f (closedBall (0:ℂ) a) := hY.sub hX
  have hSphere (r : ℝ) (hra : r ≤ a) :
      sphere (0:ℂ) r ⊆ closedBall 0 a := by
    intro z hz
    have hn : ‖z‖ = r := by simpa [mem_sphere,dist_zero_right] using hz
    simpa only [mem_closedBall,dist_zero_right,hn] using hra
  have hcircle (r : ℝ) (hr : r ∈ Icc (0:ℝ) a) :
      0 ≤ Real.circleAverage f 0 r := by
    have hYi : CircleIntegrable Y 0 r :=
      (hY.mono (hSphere r hr.2)).circleIntegrable hr.1
    have hXi : CircleIntegrable X 0 r :=
      (hX.mono (hSphere r hr.2)).circleIntegrable hr.1
    have hsubAvg := Real.circleAverage_fun_sub hYi hXi
    change Real.circleAverage f 0 r =
      Real.circleAverage Y 0 r-Real.circleAverage X 0 r at hsubAvg
    rw [hsubAvg]
    exact sub_nonneg.mpr
      (actualHarmonic_inner_positivePower_le_cosine
        F hc ξ hξ hr.1 (hr.2.trans_lt ha1) hm)
  change 0 ≤ ∫ z in greenPolarRegion 0 a, f z
  rw [greenPolarRegion_integral_eq_radial_circleAverage f (by norm_num) hf]
  apply setIntegral_nonneg
  · exact measurableSet_Icc
  intro r hr
  exact mul_nonneg (mul_nonneg hr.1 (by positivity)) (hcircle r hr)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_innerDisk_gain_nonneg
