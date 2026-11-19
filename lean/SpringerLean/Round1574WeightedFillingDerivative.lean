import SpringerLean.Round1573FillingDerivativeNorm

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The zero-safe actual form of the manuscript's radial modulus
derivative estimate. The norm of the real derivative of `H` bounds
every directional derivative of `|H|` where the latter exists. -/
theorem actualHarmonic_weighted_fderiv_le_phase_gradient
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (k:ℝ)*‖actualHarmonic F z‖^(k-1)*
      ‖fderiv ℝ (actualHarmonic F) z‖ ≤
    2*(k:ℝ)*‖actualHarmonic F z‖^(k-1)+
      Real.sqrt
        (((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2+
          ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2) := by
  let A : ℝ := (k:ℝ)*‖actualHarmonic F z‖^(k-1)
  let c : ℝ := ‖deriv (exteriorForwardGerm F) (conj z)‖
  let p : ℝ := Real.sqrt
    (((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2+
      ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH := actualHarmonic_fderiv_norm_le_one_add_forwardDeriv F hc hz
  have hP := actualHarmonicPhaseField_deriv_norm_linear_bound F hc k β hβ hz
  change A*c ≤ A+p at hP
  have hmul := mul_le_mul_of_nonneg_left hH hA
  change A*‖fderiv ℝ (actualHarmonic F) z‖ ≤ A*(1+c) at hmul
  have hgoal : A*‖fderiv ℝ (actualHarmonic F) z‖ ≤ 2*A+p := by
    nlinarith
  convert hgoal using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_weighted_fderiv_le_phase_gradient
