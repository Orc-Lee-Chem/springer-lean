import SpringerLean.Round1746ActualTimeLocalLipschitz

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Both actual phase-gradient coordinates are C1 on the source disk,
including filling zeros. This supplies the smooth factor of J_P. -/
theorem actualHarmonicPhase_gradient_coordinates_contDiffAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ 1
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) (1 : ℂ)) z ∧
    ContDiffAt ℝ 1
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) Complex.I) z := by
  let H := actualHarmonic F
  let C : ℂ → ℂ := fun w => deriv (exteriorForwardGerm F) (conj w)
  let W : ℂ → ℂ := fun w => (k : ℂ)*beta*(H w)^(k-1)
  have hH : ContDiffAt ℝ 1 H z := actualHarmonic_contDiffAt_real F hc hz
  have hzc : conj z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using hz
  have ha := exteriorForwardGerm_analyticOnNhd_unitBall F hc (conj z) hzc
  have hconj : ContDiffAt ℝ 1 (fun w : ℂ => conj w) z :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt
  have hC : ContDiffAt ℝ 1 C z :=
    ha.deriv.restrictScalars.contDiffAt.comp z hconj
  have hW : ContDiffAt ℝ 1 W z :=
    contDiffAt_const.mul (hH.pow (k-1))
  have hX : ContDiffAt ℝ 1 (fun w => (W w*(1+C w)).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z
      (hW.mul (contDiffAt_const.add hC))
  have hY : ContDiffAt ℝ 1 (fun w => (W w*(1-C w)).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z
      (hW.mul (contDiffAt_const.sub hC))
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hnhds : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball (0 : ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds hzball
  have hXe : (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) (1 : ℂ))
      =ᶠ[𝓝 z] (fun w => (W w*(1+C w)).im) := by
    filter_upwards [hnhds] with w hw
    have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact (actualHarmonicPhaseField_gradient_coordinates F hc k beta hw').1
  have hYe : (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) Complex.I)
      =ᶠ[𝓝 z] (fun w => (W w*(1-C w)).re) := by
    filter_upwards [hnhds] with w hw
    have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact (actualHarmonicPhaseField_gradient_coordinates F hc k beta hw').2
  exact ⟨hX.congr_of_eventuallyEq hXe, hY.congr_of_eventuallyEq hYe⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_gradient_coordinates_contDiffAt
