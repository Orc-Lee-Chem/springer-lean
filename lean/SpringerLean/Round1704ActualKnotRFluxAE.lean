import SpringerLean.Round1703ActualKnotPFluxAE
import SpringerLean.Round1614ActualPhaseFluxR

open MeasureTheory

namespace SpringerLean

/-- The actual radial flux retains the printed one-sided slope formula
almost everywhere on a physical knot level. -/
theorem actualEnergyFluxRdiv_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        let U := actualHarmonicPhaseField F k beta
        let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
        let t := actualHarmonicMultiplierTime F k
        let phi := fun w => energyMultiplierF (t w)
        let fp : ℝ := (energyMultiplierEndpointRaw
          (⟨2 * i.val, by omega⟩ : Fin 43)).fp
        let u := U z / y z
        let yr := (fderiv ℝ y z) (z / ‖z‖)
        let Ur := (fderiv ℝ U z) (z / ‖z‖)
        actualEnergyFluxRdiv F k beta z =
          (y z / ‖z‖ * phi z - (phi z + t z * fp) * yr -
            (k : ℝ) * fp) * u^2 + 2 * phi z * u * Ur := by
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k,
      actualHarmonicMultiplier_all_knot_slope_chain_rules_ae F hc k]
    with z hdiff hchain i hreg hlevel
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let phi : ℂ → ℝ := fun w =>
    energyMultiplierF (actualHarmonicMultiplierTime F k w)
  let fp : ℝ := (energyMultiplierEndpointRaw
    (⟨2 * i.val, by omega⟩ : Fin 43)).fp
  have hphi := (hdiff i hreg hlevel).2.1
  have hfp := (hchain i hreg hlevel).2.1
  have hrad : (fderiv ℝ phi z) (z / ‖z‖) =
      fp * (fderiv ℝ (actualHarmonicMultiplierTime F k) z) (z / ‖z‖) := by
    simpa only [phi, fp, smul_apply, smul_eq_mul] using
      congrArg (fun L : ℂ →L[ℝ] ℝ => L (z / ‖z‖)) hfp
  have hR := actualHarmonic_phaseFluxR_divergence
    F hc k beta phi fp hball hz0 hH hphi.differentiableAt hrad
  simpa only [actualEnergyFluxRdiv, phi, fp] using hR

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxRdiv_knot_ae
