import SpringerLean.Round1723ActualGermDerivativeLocallyBounded

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- At every source interior point the two phase-gradient coordinates
are locally bounded by a fixed multiple of |H|^(k-1). -/
theorem actualHarmonicPhase_gradient_locally_power_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z in 𝓝 z₀,
        |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)| ≤
          C * ‖actualHarmonic F z‖^(k - 1) ∧
        |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I| ≤
          C * ‖actualHarmonic F z‖^(k - 1) := by
  obtain ⟨C₀, hC₀, hderiv⟩ :=
    actualHarmonic_germ_deriv_locally_bounded F hc hz₀
  have hball : ∀ᶠ z in 𝓝 z₀, ‖z‖ < 1 := by
    have hzmem : z₀ ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz₀
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with z hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨(k : ℝ) * (1 + C₀), by positivity, ?_⟩
  filter_upwards [hderiv, hball] with z hcz hz
  obtain ⟨hx, hy⟩ :=
    actualHarmonicPhase_gradient_coordinates_abs_le
      F hc k beta hbeta hz
  have hfac : 0 ≤ (k : ℝ) * ‖actualHarmonic F z‖^(k - 1) := by positivity
  have hlim : (k : ℝ) * ‖actualHarmonic F z‖^(k - 1) *
      (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) ≤
      ((k : ℝ) * (1 + C₀)) *
        ‖actualHarmonic F z‖^(k - 1) := by
    have hmono := mul_le_mul_of_nonneg_left
      (add_le_add_left hcz 1) hfac
    nlinarith
  exact ⟨hx.trans hlim, hy.trans hlim⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_gradient_locally_power_bounded
