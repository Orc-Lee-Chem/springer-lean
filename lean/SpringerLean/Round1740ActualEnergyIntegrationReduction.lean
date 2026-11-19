import SpringerLean.Round1739LipschitzSliceFTC
import SpringerLean.Round1713ActualPhaseGradientSqIntegrable

open MeasureTheory Metric

namespace SpringerLean

/-- Exact reduction of the actual all-disk phase-energy theorem to a
single analytic divergence integral. The two extra premises are the
compact-support/collar task; all pointwise and L1 hypotheses have
already been proved from the original exterior class. -/
theorem actualHarmonicPhaseEnergy_of_flux_divergence_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    (hDivInt : IntegrableOn
      (actualCartesianDiv (actualEnergyFluxField F k beta))
      (ball (0 : ℂ) 1))
    (hDivZero :
      ∫ z in ball (0 : ℂ) 1,
        actualCartesianDiv (actualEnergyFluxField F k beta) z
        ∂volume = 0) :
    (k : ℝ)^2 * actualHarmonicPhasePotential F k beta ≤
      (25 / 16 : ℝ) * actualHarmonicPhaseEnergy F k beta := by
  let D : Set ℂ := ball 0 1
  let μ : Measure ℂ := volume.restrict D
  let V : ℂ → ℝ := actualHarmonicPhasePotentialDensity F k beta
  let P : ℂ → ℝ := fun z =>
    ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ))^2 +
    ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I)^2
  let Q : ℂ → ℝ := actualCartesianDiv (actualEnergyFluxField F k beta)
  let b : ℝ := (k : ℝ) / (4 * ((k : ℝ) - 1))
  have hk1 : 1 ≤ k := by omega
  have hV : Integrable V μ :=
    actualHarmonicPhasePotentialDensity_integrableOn_unitDisk
      F hc hk1 beta hbeta
  have hP : Integrable P μ :=
    actualHarmonicPhaseGradientSq_integrableOn F hc k hk1 beta hbeta
  have hQ : Integrable Q μ := hDivInt
  have hpoint : ∀ᵐ z ∂μ,
      (k : ℝ)^2 * V z + b * Q z ≤ (25 / 16 : ℝ) * P z := by
    filter_upwards
      [ae_restrict_of_ae
        (actualHarmonicPhase_pointwise_disk_ae F hc k hk beta hbeta),
       ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with z h hz
    have hz' : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    exact h hz'
  have hraw :
      (k : ℝ)^2 * (∫ z in D, V z ∂volume) ≤
        (25 / 16 : ℝ) * (∫ z in D, P z ∂volume) := by
    have hQzero : ∫ z, Q z ∂μ = 0 := by
      simpa only [μ, D, Q] using hDivZero
    have hmain := integral_mono_ae
      ((hV.const_mul _).add (hQ.const_mul _))
      (hP.const_mul _) hpoint
    rw [integral_add' (hV.const_mul _) (hQ.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_const_mul, hQzero] at hmain
    simpa [μ, D, V, P, Q, b] using hmain
  have hpi : 0 ≤ (Real.pi : ℝ)⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hraw hpi
  change (k : ℝ)^2 * (Real.pi⁻¹ * ∫ z in D, V z ∂volume) ≤
    (25 / 16 : ℝ) * (Real.pi⁻¹ * ∫ z in D, P z ∂volume)
  nlinarith [hscaled]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseEnergy_of_flux_divergence_zero
