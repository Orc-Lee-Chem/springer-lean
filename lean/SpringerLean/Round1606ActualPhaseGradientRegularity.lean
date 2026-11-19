import SpringerLean.Round1605ActualPhaseFluxS

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The actual horizontal and vertical gradient components of U are
differentiable at every interior point. This supplies the analytic
premise of the J_P product rule. -/
theorem actualHarmonicPhase_gradient_coordinates_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℝ
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) (1:ℂ)) z ∧
    DifferentiableAt ℝ
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) Complex.I) z := by
  let H := actualHarmonic F
  let C : ℂ → ℂ := fun w => deriv (exteriorForwardGerm F) (conj w)
  let W : ℂ → ℂ := fun w => beta*(H w)^(k-1)
  have hW : DifferentiableAt ℝ W z :=
    (actualHarmonic_phasePower_hasFDerivAt_real F hc k beta hz).differentiableAt
  have hC : DifferentiableAt ℝ C z :=
    (actualHarmonic_deriv_hasFDerivAt_real F hc hz).differentiableAt
  have hplus : DifferentiableAt ℝ (fun w => (1:ℂ)+C w) z :=
    (differentiableAt_const (x := z) (1:ℂ)).add hC
  have hminus : DifferentiableAt ℝ (fun w => (1:ℂ)-C w) z :=
    (differentiableAt_const (x := z) (1:ℂ)).sub hC
  have hXexplicit : DifferentiableAt ℝ
      (fun w => (k:ℝ)*(W w*(1+C w)).im) z := by
    have hprod := hW.mul hplus
    exact (Complex.imCLM.differentiableAt.comp z hprod).const_mul (k:ℝ)
  have hYexplicit : DifferentiableAt ℝ
      (fun w => (k:ℝ)*(W w*(1-C w)).re) z := by
    have hprod := hW.mul hminus
    exact (Complex.reCLM.differentiableAt.comp z hprod).const_mul (k:ℝ)
  have hzball : z ∈ Metric.ball (0:ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hnhds : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball (0:ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds hzball
  have hXeq :
      (fun w : ℂ => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) (1:ℂ))
        =ᶠ[𝓝 z]
      (fun w : ℂ => (k:ℝ)*(W w*(1+C w)).im) := by
    filter_upwards [hnhds] with w hw
    have hw' : ‖w‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hx := (actualHarmonicPhaseField_gradient_coordinates F hc k beta hw').1
    simpa [W, H, C, mul_assoc, Complex.mul_im] using hx
  have hYeq :
      (fun w : ℂ => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) Complex.I)
        =ᶠ[𝓝 z]
      (fun w : ℂ => (k:ℝ)*(W w*(1-C w)).re) := by
    filter_upwards [hnhds] with w hw
    have hw' : ‖w‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hy := (actualHarmonicPhaseField_gradient_coordinates F hc k beta hw').2
    simpa [W, H, C, mul_assoc, Complex.mul_re] using hy
  exact ⟨hXexplicit.congr_of_eventuallyEq hXeq,
    hYexplicit.congr_of_eventuallyEq hYeq⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_gradient_coordinates_differentiableAt
