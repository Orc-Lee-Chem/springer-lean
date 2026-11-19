import SpringerLean.Round27LogKernel

open MeasureTheory Metric

namespace SpringerLean

/-- The maximum of a real harmonic function and zero satisfies the local
circle submean inequality. This analytic bridge avoids manipulating the
logarithmic pole when a potential is locally a maximum of a harmonic
inverse-branch logarithm and zero. -/
theorem max_harmonic_zero_circle_submean
    {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c |ρ|)) :
    max (f c) 0 ≤
      Real.circleAverage (fun z : ℂ => max (f z) 0) c ρ := by
  have hcont : ContinuousOn f (sphere c |ρ|) :=
    hf.continuousOn.mono sphere_subset_closedBall
  have hInt : CircleIntegrable f c ρ := hcont.circleIntegrable'
  have hMaxCont : ContinuousOn (fun z : ℂ => max (f z) 0) (sphere c |ρ|) :=
    continuous_max.comp_continuousOn (hcont.prodMk continuousOn_const)
  have hMaxInt : CircleIntegrable (fun z : ℂ => max (f z) 0) c ρ :=
    hMaxCont.circleIntegrable'
  have h1 : f c ≤ Real.circleAverage (fun z : ℂ => max (f z) 0) c ρ := by
    rw [← hf.circleAverage_eq]
    apply Real.circleAverage_mono hInt hMaxInt
    intro z hz
    exact le_max_left _ _
  have h0 : 0 ≤ Real.circleAverage (fun z : ℂ => max (f z) 0) c ρ := by
    have hconst : CircleIntegrable (fun _ : ℂ => (0 : ℝ)) c ρ :=
      circleIntegrable_const _ _ _
    have hle := Real.circleAverage_mono hconst hMaxInt
      (fun z hz => le_max_right (f z) 0)
    simpa only [Real.circleAverage_const] using hle
  exact max_le h1 h0

end SpringerLean
