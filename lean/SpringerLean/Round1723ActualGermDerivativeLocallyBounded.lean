import SpringerLean.Round1722ActualPhaseGradientPowerBound

open Filter
open scoped ComplexConjugate Topology

namespace SpringerLean

/-- The actual analytic derivative appearing in the harmonic filling is
bounded on a neighborhood of each source interior point. The bound
is local and is valid even when g' is unbounded near the unit circle. -/
theorem actualHarmonic_germ_deriv_locally_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z in 𝓝 z₀,
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ≤ C := by
  let c : ℂ → ℂ := fun z =>
    deriv (exteriorForwardGerm F) (conj z)
  have hcont : ContinuousAt c z₀ :=
    (actualHarmonic_deriv_hasFDerivAt_real F hc hz₀).continuousAt
  have hnear : ∀ᶠ z in 𝓝 z₀,
      dist (c z) (c z₀) < 1 :=
    hcont.eventually (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  refine ⟨1 + ‖c z₀‖, by positivity, ?_⟩
  filter_upwards [hnear] with z hz
  have htri := norm_add_le (c z - c z₀) (c z₀)
  have hsum : (c z - c z₀) + c z₀ = c z := by ring
  rw [hsum] at htri
  rw [dist_eq_norm] at hz
  linarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_germ_deriv_locally_bounded
