import SpringerLean.Round1712PhaseFieldAtFillingZero

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- The square of the actual phase gradient is integrable on the
source unit disk. This is the L2 input for the radial-cutoff flux
argument, stated without assuming a bounded derivative of the
analytic germ near the boundary. -/
theorem actualHarmonicPhaseGradientSq_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    IntegrableOn
      (fun z : ℂ =>
        ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ))^2 +
        ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I)^2)
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball (0 : ℂ) 1
  let m : ℕ := 2 * k - 2
  let w : ℂ → ℝ := fun z => ‖actualHarmonic F z‖^m
  let d2 : ℂ → ℝ := fun z =>
    ‖deriv (exteriorForwardGerm F) (conj z)‖^2
  let c : ℂ → ℝ := fun z =>
    (beta^2 * actualHarmonic F z^m *
      deriv (exteriorForwardGerm F) (conj z)).re
  obtain ⟨hw, hwd⟩ := actualHarmonic_weighted_integrableOn F hc m
  have hcInt : IntegrableOn c D :=
    actualHarmonic_phase_cross_integrableOn F hc m beta
  have hsum : IntegrableOn (fun z => w z + w z * d2 z) D :=
    hw.add hwd
  have hcomb : IntegrableOn
      (fun z => (k : ℝ)^2 * (w z + w z * d2 z) -
        2 * (k : ℝ)^2 * c z) D :=
    (hsum.const_mul _).sub (hcInt.const_mul _)
  apply hcomb.congr_fun
  · intro z hz
    have hz1 : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hgrad := actualHarmonicPhaseField_gradient_sq
      F hc hk beta hbeta hz1
    dsimp only [w, d2, c, m]
    rw [hgrad]
    ring
  · exact Metric.isOpen_ball.measurableSet

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseGradientSq_integrableOn
