import SpringerLean.SingleRampPointwise
import SpringerLean.SingleRampRegularity
import SpringerLean.AnalyticFluxCutoff
import SpringerLean.ActualSignedBridge

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean.AnalyticRevision

noncomputable section

/-- The pointwise flux estimate covers the whole open disk almost
everywhere, including the multiplier level and the filling zeros. -/
theorem ramp_pointwise_disk_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < 1 →
      DifferentiableAt ℝ (rampFlux F k β) z ∧
      (k:ℝ)^2 * actualHarmonicPhasePotentialDensity F k β z +
        (k:ℝ)/(4*((k:ℝ)-1))*actualCartesianDiv (rampFlux F k β) z ≤
      (7/3:ℝ) *
        ((fderiv ℝ (actualHarmonicPhaseField F k β) z (1:ℂ))^2 +
          (fderiv ℝ (actualHarmonicPhaseField F k β) z Complex.I)^2) := by
  filter_upwards [ramp_hasFDerivAt_ae F hc k] with z hm hz
  by_cases hH : actualHarmonic F z = 0
  · have hJ := rampFlux_hasFDerivAt_zero F hc k (by omega) β hβ hz hH
    refine ⟨hJ.differentiableAt, ?_⟩
    have hre : HasFDerivAt (fun w => (rampFlux F k β w).re) (0 : ℂ →L[ℝ] ℝ) z := by
      simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp z hJ
    have him : HasFDerivAt (fun w => (rampFlux F k β w).im) (0 : ℂ →L[ℝ] ℝ) z := by
      simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp z hJ
    simp [actualHarmonicPhasePotentialDensity,hH,actualCartesianDiv,hre.fderiv,him.fderiv]
    positivity
  · have hz₀ : z ≠ 0 := by
      rintro rfl
      exact hH (by simp [actualHarmonic, exteriorForwardGerm_zero])
    exact ramp_pointwise_regular F hc k hk β hβ hz hz₀ hH
      (hm ((actualMultiplierRegularSet_mem_iff F z).mpr ⟨hz,hH,hz₀⟩))

/-- The actual energy bound with the capped linear multiplier. -/
theorem actualHarmonicPhase_energy_le_seven_thirds
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    (k:ℝ)^2 * actualHarmonicPhasePotential F k β ≤
      (7/3:ℝ) * actualHarmonicPhaseEnergy F k β := by
  let J := rampFlux F k β
  let V := actualHarmonicPhasePotentialDensity F k β
  let U := actualHarmonicPhaseField F k β
  let P : ℂ → ℝ := fun z => (fderiv ℝ U z (1:ℂ))^2 + (fderiv ℝ U z Complex.I)^2
  have hk₂ : 2 ≤ k := by omega
  obtain ⟨C,hC,hJ⟩ := rampFlux_norm_le_boundary_distance F hc k hk₂ β hβ
  let M : ℂ → ℝ := fun z => C*(1 + ‖deriv (exteriorForwardGerm F) (conj z)‖)
  have hpoint := ramp_pointwise_disk_ae F hc k hk β hβ
  have hraw := cutFlux_integral_le J (fun z => (k:ℝ)^2*V z) (fun z => (7/3:ℝ)*P z)
    M ((k:ℝ)/(4*((k:ℝ)-1)))
    (fun _ hz hz₀ => rampFlux_locally_lipschitz_punctured_disk F hc k hk₂ β hβ hz hz₀)
    ((rampFlux_continuousOn_unitDisk F hc k hk₂ β hβ).aestronglyMeasurable isOpen_ball.measurableSet)
    (hpoint.mono (fun _ hp hz => (hp hz).1))
    ((actualHarmonicPhasePotentialDensity_integrableOn_unitDisk F hc (by omega) β hβ).const_mul _)
    ((actualHarmonicPhaseGradientSq_integrableOn F hc k (by omega) β hβ).const_mul _)
    ((actualForwardDerivative_boundaryMajorant_integrableOn F hc).const_mul C)
    (fun _ _ => by dsimp [M]; positivity)
    (fun z hz => by simpa only [M,J,mul_assoc,mul_left_comm] using hJ z hz)
    (hpoint.mono (fun _ hp hz => (hp hz).2))
  rw [integral_const_mul, integral_const_mul] at hraw
  have hscale := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr Real.pi_pos.le)
  change (k:ℝ)^2*(Real.pi⁻¹ * ∫ z in ball (0:ℂ) 1, V z) ≤
    (7/3:ℝ)*(Real.pi⁻¹ * ∫ z in ball (0:ℂ) 1, P z)
  simpa only [mul_left_comm] using hscale

/-- The phase selected by the actual coefficient pays the \(3/14\)
potential term and half of the omitted moment. -/
theorem exteriorInverseCoeff_exists_singleRamp_signed_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) (hk : 751 ≤ k) :
    ∃ β : ℂ, ‖β‖ = 1 ∧
      ‖exteriorInverseCoeff F (2*k-1)‖ ≤
        actualHarmonicMoment F (2*k-2) -
          (3/14:ℝ)*actualHarmonicPhasePotential F k β -
          actualOmittedMoment F (2*k-2)/2 :=
  signedCost_of_singleRampEnergy F hc k (by omega)
    (fun β hβ => actualHarmonicPhase_energy_le_seven_thirds F hc k hk β hβ)

def singleRampSignedDensity (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) : ℝ :=
  (‖actualHarmonic F z‖^(2*k-2) -
    (3/14:ℝ)*actualHarmonicPhasePotentialDensity F k β z)/(2:ℝ)^(2*k-2)

theorem singleRampSignedDensity_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    IntegrableOn (singleRampSignedDensity F k β) (ball (0:ℂ) 1) := by
  have hM := (actualHarmonic_weighted_integrableOn F hc (2*k-2)).1
  have hV := actualHarmonicPhasePotentialDensity_integrableOn_unitDisk F hc hk β hβ
  exact (hM.sub (hV.const_mul (3/14:ℝ))).div_const _

theorem singleRampSignedDensity_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    Real.pi⁻¹*(∫ z in ball (0:ℂ) 1, singleRampSignedDensity F k β z) =
      (actualHarmonicMoment F (2*k-2) -
        (3/14:ℝ)*actualHarmonicPhasePotential F k β)/(2:ℝ)^(2*k-2) := by
  have hM := (actualHarmonic_weighted_integrableOn F hc (2*k-2)).1
  have hV := actualHarmonicPhasePotentialDensity_integrableOn_unitDisk F hc hk β hβ
  unfold singleRampSignedDensity actualHarmonicMoment actualHarmonicPhasePotential
  rw [integral_div, integral_sub hM (hV.const_mul _), integral_const_mul]
  ring

theorem exteriorInverseCoeff_candidate_exists_singleRamp_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1):ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ β : ℂ, ‖β‖ = 1 ∧
      (catalan (k-1):ℝ)/(2:ℝ)^(2*k-2) ≤
        Real.pi⁻¹*(∫ z in ball (0:ℂ) 1, singleRampSignedDensity F k β z) := by
  obtain ⟨β,hβ,hS⟩ := exteriorInverseCoeff_exists_singleRamp_signed_bound F hc k hk
  refine ⟨β,hβ,?_⟩
  rw [singleRampSignedDensity_integral F hc (by omega : 1 ≤ k) β hβ]
  have hA : 0 ≤ actualOmittedMoment F (2*k-2) := by
    unfold actualOmittedMoment
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end
end SpringerLean.AnalyticRevision

#print axioms SpringerLean.AnalyticRevision.actualHarmonicPhase_energy_le_seven_thirds
#print axioms SpringerLean.AnalyticRevision.exteriorInverseCoeff_exists_singleRamp_signed_bound
#print axioms SpringerLean.AnalyticRevision.exteriorInverseCoeff_candidate_exists_singleRamp_integral
