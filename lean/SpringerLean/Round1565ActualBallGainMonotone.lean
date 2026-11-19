import SpringerLean.Round1564InnerBallGainLimit

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The actual projected power gain on inner balls increases with radius.
Only integral monotonicity is asserted; the integrand may change sign. -/
theorem actualHarmonic_positivePower_ball_gain_mono
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {b₀ b : ℝ} (hb₀0 : 0 ≤ b₀) (hb₀b : b₀ ≤ b) (hb1 : b < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    (∫ z in ball (0:ℂ) b₀,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m) ≤
    ∫ z in ball (0:ℂ) b,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m := by
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  let f : ℂ → ℝ := fun z => Y z-X z
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
  have hring := actualHarmonic_positivePower_annulus_gain_nonneg
    F hc ξ hξ hb₀0 hb₀b hb1 hm
  change 0 ≤ ∫ z in greenPolarRegion b₀ b, f z at hring
  have hsplit := greenPolarRegion_integral_split f (by norm_num) hb₀0 hb₀b hf
  have hball₀ := setIntegral_congr_set (f := f) (greenPolarRegion_zero_ae_ball b₀)
  have hball := setIntegral_congr_set (f := f) (greenPolarRegion_zero_ae_ball b)
  rw [hball₀,hball] at hsplit
  change (∫ z in ball (0:ℂ) b, f z) =
    (∫ z in ball (0:ℂ) b₀, f z) +
      (∫ z in greenPolarRegion b₀ b, f z) at hsplit
  change (∫ z in ball (0:ℂ) b₀, f z) ≤ ∫ z in ball (0:ℂ) b, f z
  linarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_ball_gain_mono
