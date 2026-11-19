import SpringerLean.Round1745ActualCollarErrorLimit

open MeasureTheory Filter Metric
open scoped Topology

namespace SpringerLean

/-- The actual global energy theorem now reduces only to the
fixed-cutoff integration-by-parts statements. Both collar limits are
derived from the original map class, and no unweighted divergence
integrability is assumed. -/
theorem actualHarmonicPhaseEnergy_of_cutoff_flux_balance
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hweighted : ∀ j, IntegrableOn
      (fun z => radialEnergyCutoff (ε j) z *
        actualCartesianDiv (actualEnergyFluxField F k beta) z)
      (ball (0 : ℂ) 1))
    (hbalance : ∀ j,
      (∫ z in ball (0 : ℂ) 1, radialEnergyCutoff (ε j) z *
        actualCartesianDiv (actualEnergyFluxField F k beta) z ∂volume) =
      -(∫ z in ball (0 : ℂ) 1,
        actualEnergyCutoffError F k beta (ε j) z ∂volume)) :
    (k : ℝ)^2 * actualHarmonicPhasePotential F k beta ≤
      (25 / 16 : ℝ) * actualHarmonicPhaseEnergy F k beta := by
  let μ : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  let V := actualHarmonicPhasePotentialDensity F k beta
  let P : ℂ → ℝ := fun z =>
    ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ))^2 +
    ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I)^2
  let e : ℂ → ℝ := fun z => (k : ℝ)^2 * V z
  let f : ℂ → ℝ := fun z => (25 / 16 : ℝ) * P z
  let q := actualCartesianDiv (actualEnergyFluxField F k beta)
  let b : ℝ := (k : ℝ)/(4*((k : ℝ)-1))
  let η : ℕ → ℂ → ℝ := fun j => radialEnergyCutoff (ε j)
  let B : ℕ → ℝ := fun j => ∫ z, actualEnergyCutoffError F k beta (ε j) z ∂μ
  have hk1 : 1 ≤ k := by omega
  have he : Integrable e μ :=
    (actualHarmonicPhasePotentialDensity_integrableOn_unitDisk
      F hc hk1 beta hbeta).const_mul _
  have hf : Integrable f μ :=
    (actualHarmonicPhaseGradientSq_integrableOn F hc k hk1 beta hbeta).const_mul _
  have hηmeas (j : ℕ) : AEStronglyMeasurable (η j) μ :=
    radialEnergyCutoff_continuous.aestronglyMeasurable
  have hηbound (j : ℕ) : ∀ᵐ z ∂μ, 0 ≤ η j z ∧ η j z ≤ 1 :=
    Filter.Eventually.of_forall (radialEnergyCutoff_bounds (ε j))
  have hae0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hηlim : ∀ᵐ z ∂μ, Tendsto (fun j => η j z) atTop (𝓝 1) := by
    filter_upwards [ae_restrict_of_ae hae0,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz0 hz
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    apply tendsto_const_nhds.congr'
    filter_upwards [radialEnergyCutoff_eventually_one ε hε hlim hz0 hz'] with j hj
    exact hj.symm
  have hpoint : ∀ᵐ z ∂μ, e z + b*q z ≤ f z := by
    filter_upwards [ae_restrict_of_ae
      (actualHarmonicPhase_pointwise_disk_ae F hc k hk beta hbeta),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hp hz
    exact hp (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hBlim : Tendsto B atTop (𝓝 0) :=
    actualEnergyCutoffError_integral_tendsto_zero F hc k (by omega)
      beta hbeta ε hε hlim
  have hraw := integral_energy_le_of_cutoff_flux_balance μ e f q b η B
    he hf hηmeas hηbound hηlim hpoint hweighted hbalance hBlim
  have hraw' : (k : ℝ)^2 * (∫ z, V z ∂μ) ≤
      (25 / 16 : ℝ) * (∫ z, P z ∂μ) := by
    simpa only [e, f, integral_const_mul] using hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw'
    (inv_nonneg.mpr Real.pi_pos.le)
  change (k : ℝ)^2 * (Real.pi⁻¹ * ∫ z, V z ∂μ) ≤
    (25 / 16 : ℝ) * (Real.pi⁻¹ * ∫ z, P z ∂μ)
  nlinarith [hscaled]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhaseEnergy_of_cutoff_flux_balance
