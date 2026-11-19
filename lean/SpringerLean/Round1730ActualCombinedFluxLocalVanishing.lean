import SpringerLean.Round1729ActualCombinedFluxPowerBound

open Filter
open scoped Topology

namespace SpringerLean

/-- The actual signed combined flux vanishes locally to order
2k-1 in the harmonic filling, including at other zeros in the
neighborhood. -/
theorem actualEnergyFluxField_locally_power_bounded_at_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1)
    (hzero : actualHarmonic F z₀ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ z in 𝓝 z₀,
        ‖actualEnergyFluxField F k beta z‖ ≤
          C * ‖actualHarmonic F z‖^(2 * k - 1) := by
  obtain ⟨Cchi, hchi⟩ := energyMultipliers_bounded.1
  obtain ⟨Cf, hf⟩ := energyMultipliers_bounded.2.1
  obtain ⟨Cs, hs⟩ := energyMultipliers_bounded.2.2
  obtain ⟨Cg, hCg, hgrad⟩ :=
    actualHarmonicPhase_gradient_locally_power_bounded
      F hc k (by omega) beta hbeta hz₀
  have hball : ∀ᶠ z in 𝓝 z₀, ‖z‖ < 1 := by
    have hzmem : z₀ ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz₀
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with z hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hCchi : 0 ≤ Cchi := (abs_nonneg _).trans (hchi 0 (by norm_num))
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hf 0 (by norm_num))
  have hCs : 0 ≤ Cs := (abs_nonneg _).trans (hs 0 (by norm_num))
  let C := 2 * Cchi * Cg + 8 * ((k : ℝ) - 1) * Cf +
    4 * ((k : ℝ) - 1) * Cs
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hball, hgrad] with z hz hgradz
  have ht : 0 ≤ actualHarmonicMultiplierTime F k z :=
    actualHarmonicMultiplierTime_nonneg F k hz
  by_cases hH : actualHarmonic F z = 0
  · have hJ :=
      (actualEnergyFluxFields_zero_at_filling_zero
        F hc k hk beta hz hH).2.2.2
    rw [hJ, norm_zero, hH, norm_zero]
    simp [C, zero_pow (by omega : 2 * k - 1 ≠ 0)]
  · exact actualEnergyFluxField_norm_le_power F k hk beta z hbeta hH
      Cchi Cf Cs Cg (hchi _ ht) (hf _ ht) (hs _ ht)
      hgradz.1 hgradz.2

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_locally_power_bounded_at_zero
