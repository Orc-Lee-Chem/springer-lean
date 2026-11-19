import SpringerLean.Round13Poisson

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual smooth harmonic filling equals the normalized Poisson
average of its values on the unit circle. -/
theorem regularHarmonic_poisson_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • regularHarmonic s F ζ)
      0 1 = regularHarmonic s F z := by
  have hnot : z ∉ sphere (0 : ℂ) 1 := by
    intro hzs
    have hlt : ‖z‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hz
    have heq : ‖z‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hzs
    linarith
  have hkernel : ContinuousOn (poissonKernel 0 z) (sphere (0 : ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simpa only [abs_one] using
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere
          (c := (0 : ℂ)) (w := z) (R := (1 : ℝ))
          (by simpa only [abs_one] using hnot)))
  have hGcont : ContinuousOn (regularForwardGerm s F)
      (closedBall (0 : ℂ) 1) := by
    have hlarge : 1 < s⁻¹ := by
      have h := one_div_lt_one_div_of_lt hs0 hs1
      simpa only [one_div, inv_one] using h
    have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
      intro ζ hζ
      exact lt_of_le_of_lt hζ hlarge
    exact (regularForwardGerm_analyticOnNhd F hc hs0).continuousOn.mono hsub
  have hGconj : ContinuousOn
      (fun ζ : ℂ => regularForwardGerm s F (conj ζ))
      (sphere (0 : ℂ) 1) := by
    apply hGcont.comp Complex.continuous_conj.continuousOn
    intro ζ hζ
    have hζ' : ζ ∈ closedBall (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall hζ
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hζ'
  have hIdInt : CircleIntegrable
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 :=
    (hkernel.smul continuousOn_id).circleIntegrable (by norm_num)
  have hGInt : CircleIntegrable
      (fun ζ : ℂ => (poissonKernel 0 z ζ) •
        regularForwardGerm s F (conj ζ)) 0 1 :=
    (hkernel.smul hGconj).circleIntegrable (by norm_num)
  have hIdPoisson : Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 = z := by
    have h := ((differentiable_id : Differentiable ℂ (fun ζ : ℂ => ζ)).diffContOnCl
      (s := ball (0 : ℂ) 1)).circleAverage_poissonKernel_smul hz
    change Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 = z at h
    exact h
  have hGPoisson := regularForwardGerm_conj_poisson F hc hs0 hs1 hz
  calc
    Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 z ζ) • regularHarmonic s F ζ) 0 1 =
      Real.circleAverage (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 +
        Real.circleAverage
          (fun ζ : ℂ => (poissonKernel 0 z ζ) •
            regularForwardGerm s F (conj ζ)) 0 1 := by
              simpa only [regularHarmonic, smul_add] using
                Real.circleAverage_fun_add hIdInt hGInt
    _ = regularHarmonic s F z := by
      rw [hIdPoisson, hGPoisson]
      rfl

/-- The boundary integrand is the actual regularized exterior map, not a
separately postulated boundary extension. -/
theorem regularHarmonic_poisson_actualBoundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • rescaleExterior s F ζ)
      0 1 = regularHarmonic s F z := by
  calc
    Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 z ζ) • rescaleExterior s F ζ)
        0 1 =
      Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 z ζ) • regularHarmonic s F ζ)
        0 1 := by
          apply Real.circleAverage_congr_sphere
          intro ζ hζ
          have hnorm : ‖ζ‖ = 1 := by
            simpa only [mem_sphere, dist_zero_right, abs_one] using hζ
          change (poissonKernel 0 z ζ) • rescaleExterior s F ζ =
            (poissonKernel 0 z ζ) • regularHarmonic s F ζ
          rw [regularHarmonic_unitCircle_eq_actual F hs0 hnorm]
    _ = regularHarmonic s F z :=
      regularHarmonic_poisson_circleAverage F hc hs0 hs1 hz

end SpringerLean
