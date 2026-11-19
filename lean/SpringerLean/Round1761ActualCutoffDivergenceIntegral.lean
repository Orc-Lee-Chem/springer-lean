import SpringerLean.Round1759LipschitzCartesianDivergence
import SpringerLean.Round1760ActualCutoffDivergenceProduct

open MeasureTheory Filter Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

theorem actualEnergyCutoffError_integrableOn_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (actualEnergyCutoffError F k beta ε) (ball (0 : ℂ) 1) := by
  let μ : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  obtain ⟨C, hC, hbound⟩ :=
    actualEnergyCutoffError_common_majorant F hc k hk beta hbeta
  have hL : AEMeasurable (fderiv ℝ (radialEnergyCutoff ε)) μ :=
    (measurable_fderiv ℝ _).aemeasurable
  have hJ := (actualEnergyFluxField_aestronglyMeasurable_unitDisk
    F hc k beta).aemeasurable
  have happ : Continuous (fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2) := by fun_prop
  have hmeas : AEStronglyMeasurable (actualEnergyCutoffError F k beta ε) μ :=
    (happ.measurable.comp_aemeasurable (hL.prodMk hJ)).aestronglyMeasurable
  have hmajor := (actualForwardDerivative_boundaryMajorant_integrableOn F hc).const_mul C
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
  rw [Real.norm_eq_abs]
  exact hbound ε hε z (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- The divergence of the actual compactly cut flux is integrable
with zero disk integral, by the Lipschitz coordinate theorem. -/
theorem actualEnergyCutoffFlux_divergence_integral_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    IntegrableOn (actualCartesianDiv (actualEnergyCutoffFlux F k beta ε))
      (ball (0 : ℂ) 1) ∧
    (∫ z in ball (0 : ℂ) 1,
      actualCartesianDiv (actualEnergyCutoffFlux F k beta ε) z ∂volume) = 0 := by
  let J := actualEnergyCutoffFlux F k beta ε
  obtain ⟨K, hK⟩ := actualEnergyCutoffFlux_lipschitz F hc k hk beta hbeta hε hε1
  have hzero (z : ℂ) (hz : 1 ≤ ‖z‖) : J z = 0 := by
    simp [J, actualEnergyCutoffFlux,
      radialEnergyCutoff_eq_zero_outer hε (by linarith : 1-ε ≤ ‖z‖)]
  obtain ⟨hInt, hIntegral⟩ :=
    integral_actualCartesianDiv_zero_of_lipschitz_unit_support J K hK hzero
  have hout (z : ℂ) (hz : z ∉ ball (0 : ℂ) 1) : actualCartesianDiv J z = 0 := by
    have hz1 : 1 ≤ ‖z‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hlt : 1-ε < ‖z‖ := by linarith
    have heq : J =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hlt)]
        with w hw
      simp [J, actualEnergyCutoffFlux, radialEnergyCutoff_eq_zero_outer hε hw.le]
    have hre : (fun w => (J w).re) =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℝ)) :=
      heq.mono (fun w hw => by simpa [hw])
    have him : (fun w => (J w).im) =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℝ)) :=
      heq.mono (fun w hw => by simpa [hw])
    have hrd : fderiv ℝ (fun w => (J w).re) z = 0 := by simpa using hre.fderiv_eq (𝕜 := ℝ)
    have hid : fderiv ℝ (fun w => (J w).im) z = 0 := by simpa using him.fderiv_eq (𝕜 := ℝ)
    simp [actualCartesianDiv, hrd, hid]
  exact ⟨hInt.integrableOn,
    (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hIntegral⟩

/-- The fixed-cutoff weighted divergence is integrable, and its
integral is precisely minus the actual cutoff boundary error. -/
theorem actualEnergyFlux_cutoff_integration_by_parts
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    IntegrableOn (fun z => radialEnergyCutoff ε z *
      actualCartesianDiv (actualEnergyFluxField F k beta) z) (ball (0 : ℂ) 1) ∧
    (∫ z in ball (0 : ℂ) 1, radialEnergyCutoff ε z *
      actualCartesianDiv (actualEnergyFluxField F k beta) z ∂volume) =
      -(∫ z in ball (0 : ℂ) 1, actualEnergyCutoffError F k beta ε z ∂volume) := by
  let μ : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  obtain ⟨hCutInt, hCutZero⟩ := actualEnergyCutoffFlux_divergence_integral_zero
    F hc k hk beta hbeta hε hε1
  have hErrInt := actualEnergyCutoffError_integrableOn_unitDisk F hc k hk beta hbeta hε
  have heq : (fun z => radialEnergyCutoff ε z *
      actualCartesianDiv (actualEnergyFluxField F k beta) z) =ᵐ[μ]
      (fun z => actualCartesianDiv (actualEnergyCutoffFlux F k beta ε) z -
        actualEnergyCutoffError F k beta ε z) := by
    filter_upwards [ae_restrict_of_ae
      (actualEnergyCutoffFlux_divergence_product_ae F hc k hk beta hbeta hε),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hp hz
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    linarith [hp hz']
  refine ⟨(hCutInt.sub hErrInt).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub hCutInt hErrInt, hCutZero]
  ring

end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_cutoff_integration_by_parts
