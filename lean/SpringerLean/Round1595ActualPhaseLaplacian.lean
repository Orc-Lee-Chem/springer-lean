import SpringerLean.Round1594PhaseProductSecondDerivative

open scoped Topology ComplexConjugate
open Filter

namespace SpringerLean
set_option maxHeartbeats 1000000

/-- The actual phase field has the stated Cartesian Laplacian at every
point of the open source disk. The second derivative of the forward
germ cancels between the horizontal and vertical terms. -/
theorem actualHarmonicPhaseLaplacian_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    actualHarmonicPhaseLaplacian F k beta z =
      4*(k:ℝ)*((k:ℝ)-1)*
        (beta*(actualHarmonic F z)^(k-2)*
          deriv (exteriorForwardGerm F) (conj z)).im := by
  let H := actualHarmonic F
  let C : ℂ → ℂ := fun w => deriv (exteriorForwardGerm F) (conj w)
  let W : ℂ → ℂ := fun w => beta*(H w)^(k-1)
  have hWdiff : DifferentiableAt ℝ W z :=
    (actualHarmonic_phasePower_hasFDerivAt_real F hc k beta hz).differentiableAt
  have hCdiff : DifferentiableAt ℝ C z :=
    (actualHarmonic_deriv_hasFDerivAt_real F hc hz).differentiableAt
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
  have hWcoords := actualHarmonic_phasePower_gradient_coordinates
    F hc k hk beta hz
  have hCcoords := actualHarmonic_deriv_gradient_coordinates F hc hz
  let d := deriv (deriv (exteriorForwardGerm F)) (conj z)
  let a : ℂ := beta*((k:ℂ)-1)*(H z)^(k-2)
  have hXder :
      (fderiv ℝ (fun w => (k:ℝ)*(W w*(1+C w)).im) z) (1:ℂ) =
      (k:ℝ)*((a*(1+C z)^2+W z*d).im) := by
    rw [fderiv_real_const_mul_apply,
      fderiv_im_product_one_add W C z (1:ℂ) hWdiff hCdiff]
    rw [hWcoords.1, hCcoords.1]
    dsimp only [a, d, W, H, C]
    congr 1
    congr 1
    ring
  have hYder :
      (fderiv ℝ (fun w => (k:ℝ)*(W w*(1-C w)).re) z) Complex.I =
      (k:ℝ)*((a*Complex.I*(1-C z)^2+W z*Complex.I*d).re) := by
    rw [fderiv_real_const_mul_apply,
      fderiv_re_product_one_sub W C z Complex.I hWdiff hCdiff]
    rw [hWcoords.2, hCcoords.2]
    dsimp only [a, d, W, H, C]
    congr 1
    congr 1
    ring
  change (fderiv ℝ
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) (1:ℂ)) z)
      (1:ℂ) +
    (fderiv ℝ
      (fun w => (fderiv ℝ (actualHarmonicPhaseField F k beta) w) Complex.I) z)
      Complex.I = _
  rw [hXeq.fderiv_eq, hYeq.fderiv_eq, hXder, hYder]
  have halgebra := phase_laplacian_coordinate_algebra a (W z) (C z) d
  have hcast : ((k:ℂ)-1) = ((k:ℝ)-1) := by norm_cast
  have hfactor : (a*C z).im =
      ((k:ℝ)-1)*(beta*(H z)^(k-2)*C z).im := by
    have heq : a*C z = (((k:ℝ)-1:ℝ):ℂ)*
        (beta*(H z)^(k-2)*C z) := by
      dsimp only [a]
      rw [hcast]
      push_cast
      ring
    rw [heq]
    simp [Complex.mul_im]
  rw [hfactor] at halgebra
  dsimp only [H, C] at halgebra ⊢
  nlinarith [halgebra]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseLaplacian_eq
