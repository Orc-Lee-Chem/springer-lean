import SpringerLean.Round1541PeakArcCircleLoss

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The semicircle integral from Round1541 is exactly the loss in the
project's normalized circle averages at inner radius r. -/
theorem clippedTangentPower_peak_circleAverage_loss
    {r v M : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hM0 : 0 ≤ M) (hMq : M ≤ 2*r-v)
    {m : ℕ} (hm : 2 ≤ m) :
    (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
      Real.circleAverage
        (fun z : ℂ => (max (2*z.re) 0)^m) 0 r -
      Real.circleAverage
        (fun z : ℂ => clippedTangentPower M m (2*z.re)) 0 r := by
  let f : ℝ → ℝ := fun x => (max x 0)^m
  let t : ℝ → ℝ := clippedTangentPower M m
  let g : ℝ → ℝ := fun x => f (r*x)-t (r*x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have ht : Continuous t := by
    have hc := (clippedTangentPower_convexOn hM0 (by omega : 1 ≤ m)).continuousOn
      isOpen_univ
    simpa [t] using hc
  have hg : Continuous g := by
    dsimp [g]
    fun_prop (disch := assumption)
  have havg := evenCos_circleAverage_eq_integral g hg
  have hfun (z : ℂ) : g (2*z.re) = f (2*((r:ℂ)*z).re)-
      t (2*((r:ℂ)*z).re) := by
    dsimp [g]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    congr 1 <;> ring
  have hI1 : CircleIntegrable (fun z : ℂ => f (2*((r:ℂ)*z).re)) 0 1 :=
    (by fun_prop (disch := exact hf.continuousOn) :
      ContinuousOn (fun z : ℂ => f (2*((r:ℂ)*z).re)) (sphere 0 1)).circleIntegrable
        (by norm_num)
  have hI2 : CircleIntegrable (fun z : ℂ => t (2*((r:ℂ)*z).re)) 0 1 :=
    (by fun_prop (disch := exact ht.continuousOn) :
      ContinuousOn (fun z : ℂ => t (2*((r:ℂ)*z).re)) (sphere 0 1)).circleIntegrable
        (by norm_num)
  have hrewrite : Real.circleAverage (fun z : ℂ => g (2*z.re)) 0 1 =
      Real.circleAverage (fun z : ℂ => f (2*z.re)) 0 r -
      Real.circleAverage (fun z : ℂ => t (2*z.re)) 0 r := by
    simp_rw [hfun]
    rw [Real.circleAverage_fun_sub hI1 hI2,
      circleAverage_mul_radius_zero (fun z : ℂ => f (2*z.re)) r,
      circleAverage_mul_radius_zero (fun z : ℂ => t (2*z.re)) r]
  have hmodel : (∫ θ in (0:ℝ)..Real.pi,g (2*Real.cos θ)) =
      (∫ θ in (0:ℝ)..Real.pi,
        (max (2*r*Real.cos θ) 0)^m-
          clippedTangentPower M m (2*r*Real.cos θ)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [g,f,t]
    ring
  rw [hrewrite,hmodel] at havg
  change (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
      (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
    Real.circleAverage (fun z : ℂ => f (2*z.re)) 0 r -
      Real.circleAverage (fun z : ℂ => t (2*z.re)) 0 r
  rw [havg]
  simpa only [one_div] using
    (clippedTangentPower_peakArc_semicircle_loss
      hr0 hr1 hv0 hv1 hM0 hMq hm)

end SpringerLean

#print axioms SpringerLean.clippedTangentPower_peak_circleAverage_loss
