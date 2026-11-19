import SpringerLean.Round1571PhaseGradientDriftBound

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The actual derivative estimate in a zero-safe form. Multiplication
by `k |H|^(k-1)` avoids dividing by a quantity that vanishes at zeros
of the filling. -/
theorem actualHarmonicPhaseField_deriv_norm_linear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (k:ℝ)*‖actualHarmonic F z‖^(k-1)*
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ≤
    (k:ℝ)*‖actualHarmonic F z‖^(k-1)+
      Real.sqrt
        (((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2+
          ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2) := by
  let A : ℝ := (k:ℝ)*‖actualHarmonic F z‖^(k-1)
  let c : ℝ := ‖deriv (exteriorForwardGerm F) (conj z)‖
  let Q : ℝ :=
    ((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2+
      ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hbase := actualHarmonicPhaseField_gradient_controls_deriv_excess
    F hc k β hβ hz
  change (A*(c-1))^2 ≤ Q at hbase
  have hp : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hsq : |A*(c-1)|^2 ≤ (Real.sqrt Q)^2 := by
    simpa only [sq_abs,Real.sq_sqrt hQ] using hbase
  have habs : |A*(c-1)| ≤ Real.sqrt Q :=
    (sq_le_sq₀ (abs_nonneg _) hp).mp hsq
  have hlinear : A*(c-1) ≤ Real.sqrt Q :=
    (le_abs_self _).trans habs
  change A*c ≤ A+Real.sqrt Q
  nlinarith

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseField_deriv_norm_linear_bound
