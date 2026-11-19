import SpringerLean.Round1551AnnulusCircleGainTransfer

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- A quantitative annulus gain for the actual harmonic filling,
with the exact normalized area measure `π⁻¹ dA`. The outer radius b
remains below one so no boundary trace is invoked. -/
theorem actualHarmonic_positivePower_thinAnnulus_integral_gain
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1)
    {h d : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {m : ℕ} (hm : 1500 ≤ m) (hD : (m:ℝ)*d ≤ 3/20)
    {b : ℝ} (hb : 1-Real.sqrt d/16 ≤ b) (hb1 : b < 1) :
    let a := 1-Real.sqrt d/16
    let K := (9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*d^2*Real.sqrt d
    K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ)) ≤
      Real.pi⁻¹ *
        (∫ z in greenPolarRegion a b,
          (max (2*z.re) 0)^m-
            (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
  dsimp only
  let a : ℝ := 1-Real.sqrt d/16
  let K : ℝ := (9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*d^2*Real.sqrt d
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  let f : ℂ → ℝ := fun z => Y z-X z
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hab : a ≤ b := hb
  have ha : 0 ≤ a := by
    have hpb := thinAnnulus_peak_parameter_bounds hm hd0 hD
      (show 1-Real.sqrt d/16 ≤ a by rfl) ha1
    dsimp [a] at hpb ⊢
    linarith [hpb.2.2]
  have hsub : closedBall (0:ℂ) b ⊆ ball 0 1 := by
    intro z hz
    have hn : ‖z‖ ≤ b := by
      simpa only [mem_closedBall,dist_zero_right] using hz
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
  have hSphere (r : ℝ) (hrb : r ≤ b) :
      sphere (0:ℂ) r ⊆ closedBall 0 b := by
    intro z hz
    have hn : ‖z‖=r := by simpa [mem_sphere,dist_zero_right] using hz
    simpa only [mem_closedBall,dist_zero_right,hn] using hrb
  have hcircle (r : ℝ) (hr : r ∈ Icc a b) :
      K*(2*r)^(m-2) ≤ Real.circleAverage f 0 r := by
    have hr0 : 0 < r := by
      have hb0 := thinAnnulus_peak_parameter_bounds hm hd0 hD
        (show 1-Real.sqrt d/16 ≤ a by rfl) ha1
      have haPos : (99/100:ℝ) ≤ a := by
        simpa only [a] using hb0.2.2
      linarith [hr.1,haPos]
    have hbase := actualHarmonic_inner_positivePower_thinAnnulus_gain
      F hc ξ hξ hh0 hhpi hd hd0 hcap hm hD hr.1 (hr.2.trans_lt hb1)
    have hYi : CircleIntegrable Y 0 r :=
      (hY.mono (hSphere r hr.2)).circleIntegrable hr0.le
    have hXi : CircleIntegrable X 0 r :=
      (hX.mono (hSphere r hr.2)).circleIntegrable hr0.le
    have hsubAvg := Real.circleAverage_fun_sub hYi hXi
    change Real.circleAverage f 0 r =
      Real.circleAverage Y 0 r-Real.circleAverage X 0 r at hsubAvg
    rw [hsubAvg]
    dsimp [K,Y,X]
    nlinarith [hbase]
  have htransfer := annulus_power_circle_gain_transfer f ha hab hf
    (by omega : 2 ≤ m) K hcircle
  dsimp [f,Y,X,K,a] at htransfer ⊢
  exact htransfer

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_thinAnnulus_integral_gain
