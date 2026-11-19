import SpringerLean.Round1572PhaseGradientLinearBound

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The real derivative of `z+g(conj z)` has operator norm at most
`1+|g'|`, with no assumption on the derivative. -/
theorem harmonic_real_derivative_opNorm_le (c : ℂ) :
    ‖(1 : ℂ →L[ℝ] ℂ) +
      ((c • (1 : ℂ →L[ℝ] ℂ)).comp
        Complex.conjCLE.toContinuousLinearMap)‖ ≤ 1+‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro v
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply]
  have hconj : Complex.conjCLE.toContinuousLinearMap v = conj v := by simp
  rw [hconj]
  calc
    ‖v + c • conj v‖ ≤ ‖v‖ + ‖c • conj v‖ := norm_add_le _ _
    _ = (1+‖c‖)*‖v‖ := by
      rw [norm_smul,Complex.norm_conj]
      ring

/-- The corresponding bound for the actual harmonic filling at every
point of the source disk. -/
theorem actualHarmonic_fderiv_norm_le_one_add_forwardDeriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖fderiv ℝ (actualHarmonic F) z‖ ≤
      1+‖deriv (exteriorForwardGerm F) (conj z)‖ := by
  rw [(actualHarmonic_hasFDerivAt_real F hc hz).fderiv]
  exact harmonic_real_derivative_opNorm_le _

end SpringerLean

#print axioms SpringerLean.harmonic_real_derivative_opNorm_le
#print axioms SpringerLean.actualHarmonic_fderiv_norm_le_one_add_forwardDeriv
