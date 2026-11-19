import SpringerLean.Round1720FluxZeroPowerCriterion

open Filter Asymptotics
open scoped Topology

namespace SpringerLean

/-- Differentiability of the actual harmonic filling gives the local
linear vanishing estimate at each interior zero, without any global
bound on the analytic derivative. -/
theorem actualHarmonic_local_linear_at_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1)
    (hzero : actualHarmonic F z₀ = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z in 𝓝 z₀,
        ‖actualHarmonic F z‖ ≤ C * ‖z - z₀‖ := by
  have hBig :=
    (actualHarmonic_hasFDerivAt_real F hc hz₀).isBigO_sub
  obtain ⟨C, hC, hbound⟩ := hBig.exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound.bound] with z hz
  simpa [hzero] using hz

end SpringerLean

#print axioms SpringerLean.actualHarmonic_local_linear_at_zero
