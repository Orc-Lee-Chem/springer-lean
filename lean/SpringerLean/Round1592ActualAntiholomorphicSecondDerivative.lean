import SpringerLean.Round1591PhaseLaplacianAlgebra

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual derivative coefficient c(z)=g'(conj z) is real
differentiable in the open disk, with its antiholomorphic derivative. -/
theorem actualHarmonic_deriv_hasFDerivAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasFDerivAt
      (fun w : ℂ => deriv (exteriorForwardGerm F) (conj w))
      (((deriv (deriv (exteriorForwardGerm F)) (conj z)) •
        (1 : ℂ →L[ℝ] ℂ)).comp
          Complex.conjCLE.toContinuousLinearMap) z := by
  have hzc : conj z ∈ Metric.ball (0:ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right,
      ← Complex.star_def, norm_star] using hz
  have ha : AnalyticAt ℂ (exteriorForwardGerm F) (conj z) :=
    exteriorForwardGerm_analyticOnNhd_unitBall F hc (conj z) hzc
  have hda : AnalyticAt ℂ (deriv (exteriorForwardGerm F)) (conj z) :=
    ha.deriv
  have hd : HasDerivAt (deriv (exteriorForwardGerm F))
      (deriv (deriv (exteriorForwardGerm F)) (conj z)) (conj z) :=
    hda.differentiableAt.hasDerivAt
  have hconj : HasFDerivAt (fun w : ℂ => conj w)
      Complex.conjCLE.toContinuousLinearMap z := by
    convert (Complex.conjCLE.hasFDerivAt (x := z)) using 1
    funext u
    simp
  exact hd.complexToReal_fderiv.comp z hconj

/-- The horizontal and vertical coordinate derivatives of the actual
antiholomorphic coefficient have opposite complex phases. -/
theorem actualHarmonic_deriv_gradient_coordinates
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (fun w : ℂ => deriv (exteriorForwardGerm F) (conj w)) z)
        (1:ℂ) = deriv (deriv (exteriorForwardGerm F)) (conj z) ∧
    (fderiv ℝ (fun w : ℂ => deriv (exteriorForwardGerm F) (conj w)) z)
        Complex.I = -(Complex.I *
          deriv (deriv (exteriorForwardGerm F)) (conj z)) := by
  have h := (actualHarmonic_deriv_hasFDerivAt_real F hc hz).fderiv
  constructor
  · rw [h]
    simp
  · rw [h]
    simp [Complex.conj_I, mul_comm]

end SpringerLean

#print axioms SpringerLean.actualHarmonic_deriv_hasFDerivAt_real
#print axioms SpringerLean.actualHarmonic_deriv_gradient_coordinates
