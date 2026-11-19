import SpringerLean.Round1730ActualCombinedFluxLocalVanishing

open Filter
open scoped Topology

namespace SpringerLean

/-- The actual signed phase-energy flux, with its zero-divisor
extension, has zero real fderiv at every interior zero of the
harmonic filling. No isolated-zero assumption is used. -/
theorem actualEnergyFluxField_hasFDerivAt_zero_at_filling_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1)
    (hzero : actualHarmonic F z₀ = 0) :
    HasFDerivAt (actualEnergyFluxField F k beta)
      (0 : ℂ →L[ℝ] ℂ) z₀ := by
  let n := 2 * k - 1
  obtain ⟨CH, hCH, hHbound⟩ :=
    actualHarmonic_local_linear_at_zero F hc hz₀ hzero
  obtain ⟨CJ, hCJ, hJbound⟩ :=
    actualEnergyFluxField_locally_power_bounded_at_zero
      F hc k hk beta hbeta hz₀ hzero
  have hpower : ∀ᶠ z in 𝓝 z₀,
      ‖actualEnergyFluxField F k beta z‖ ≤
        (CJ * CH^n) * ‖z - z₀‖^n := by
    filter_upwards [hHbound, hJbound] with z hHz hJz
    have hp : ‖actualHarmonic F z‖^n ≤
        (CH * ‖z - z₀‖)^n :=
      pow_le_pow_left₀ (norm_nonneg _) hHz n
    calc
      ‖actualEnergyFluxField F k beta z‖ ≤
          CJ * ‖actualHarmonic F z‖^n := hJz
      _ ≤ CJ * (CH * ‖z - z₀‖)^n :=
        mul_le_mul_of_nonneg_left hp hCJ
      _ = (CJ * CH^n) * ‖z - z₀‖^n := by rw [mul_pow]; ring
  have hJzero :=
    (actualEnergyFluxFields_zero_at_filling_zero
      F hc k hk beta hz₀ hzero).2.2.2
  exact hasFDerivAt_zero_of_power_bound
    (actualEnergyFluxField F k beta) z₀ n (by dsimp [n]; omega)
    hJzero (CJ * CH^n) hpower

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_hasFDerivAt_zero_at_filling_zero
