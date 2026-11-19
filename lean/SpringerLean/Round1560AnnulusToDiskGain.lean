import SpringerLean.Round1559ActualInnerDiskGainNonneg

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Any strict actual annulus gain persists on the whole interior disk of
the same outer radius; the inner complement has nonnegative gain by
untruncated convex order. -/
theorem actualHarmonic_positivePower_annulus_to_disk_gain
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1)
    {m : ℕ} (hm : 1 ≤ m) {T : ℝ}
    (hgain : T <
      ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
      (∫ z in greenPolarRegion a b,
        (max (2*z.re) 0)^m-
          (max ((conj ξ*actualHarmonic F z).re) 0)^m)) :
    T < ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
      (∫ z in greenPolarRegion 0 b,
        (max (2*z.re) 0)^m-
          (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  let f : ℂ → ℝ := fun z => Y z-X z
  let N : ℝ := ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹
  have hsub : closedBall (0:ℂ) b ⊆ ball 0 1 := by
    intro z hz
    have hn : ‖z‖ ≤ b := by simpa only [mem_closedBall,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right] using hn.trans_lt hb1
  have hH := (actualHarmonic_continuousOn_unitBall F hc).mono hsub
  have hX : ContinuousOn X (closedBall (0:ℂ) b) := by
    have hproj : ContinuousOn
        (fun z : ℂ => (conj ξ*actualHarmonic F z).re)
        (closedBall (0:ℂ) b) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_const.mul hH)
    exact (continuous_max.comp_continuousOn
      (hproj.prodMk continuousOn_const)).pow m
  have hY : ContinuousOn Y (closedBall (0:ℂ) b) := by
    dsimp [Y]
    fun_prop
  have hf : ContinuousOn f (closedBall (0:ℂ) b) := hY.sub hX
  have hinner := actualHarmonic_positivePower_innerDisk_gain_nonneg
    F hc ξ hξ ha0 (hab.trans_lt hb1) hm
  change 0 ≤ ∫ z in greenPolarRegion 0 a, f z at hinner
  have hsplit := greenPolarRegion_integral_split f (by norm_num) ha0 hab hf
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hinnerScaled := mul_nonneg hN hinner
  change T < N*(∫ z in greenPolarRegion a b, f z) at hgain
  change T < N*(∫ z in greenPolarRegion 0 b, f z)
  calc
    T < N*(∫ z in greenPolarRegion a b, f z) := hgain
    _ ≤ N*((∫ z in greenPolarRegion 0 a, f z) +
        (∫ z in greenPolarRegion a b, f z)) := by nlinarith [hinnerScaled]
    _ = N*(∫ z in greenPolarRegion 0 b, f z) := by rw [←hsplit]

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_annulus_to_disk_gain
