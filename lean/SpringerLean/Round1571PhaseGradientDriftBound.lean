import SpringerLean.Round1570PhasePotentialIntegrable

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The real phase gradient controls the excess norm of the
antiholomorphic derivative. This is the algebraic derivative bound
used before the signed multiplier integration. -/
theorem phase_gradient_controls_antiholomorphic_excess (W c : ℂ) :
    (‖W‖*(‖c‖-1))^2 ≤
      (W*(1+c)).im^2+(W*(1-c)).re^2 := by
  have hbase := phase_gradient_coordinate_algebra W c
  have hre := (abs_le.mp (Complex.abs_re_le_norm (W^2*c))).2
  have hmul : ‖W^2*c‖ = ‖W‖^2*‖c‖ := by
    rw [norm_mul,norm_pow]
  rw [hmul] at hre
  rw [hbase]
  nlinarith [hre]

/-- The derivative estimate holds pointwise for the actual harmonic
filling and every unit phase, including zeros of the filling. -/
theorem actualHarmonicPhaseField_gradient_controls_deriv_excess
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (((k:ℝ)*‖actualHarmonic F z‖^(k-1))*
      (‖deriv (exteriorForwardGerm F) (conj z)‖-1))^2 ≤
      ((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2+
        ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2 := by
  let H : ℂ := actualHarmonic F z
  let c : ℂ := deriv (exteriorForwardGerm F) (conj z)
  let W : ℂ := (k:ℂ)*β*H^(k-1)
  have hW : ‖W‖ = (k:ℝ)*‖H‖^(k-1) := by
    dsimp [W]
    rw [norm_mul,norm_mul,norm_pow,hβ]
    simp
  have hbase := phase_gradient_controls_antiholomorphic_excess W c
  obtain ⟨hx,hy⟩ := actualHarmonicPhaseField_gradient_coordinates
    F hc k β hz
  change (fderiv ℝ (actualHarmonicPhaseField F k β) z) 1 =
      (W*(1+c)).im at hx
  change (fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I =
      (W*(1-c)).re at hy
  rw [←hx,←hy,hW] at hbase
  exact hbase

end SpringerLean

#print axioms SpringerLean.phase_gradient_controls_antiholomorphic_excess
#print axioms SpringerLean.actualHarmonicPhaseField_gradient_controls_deriv_excess
