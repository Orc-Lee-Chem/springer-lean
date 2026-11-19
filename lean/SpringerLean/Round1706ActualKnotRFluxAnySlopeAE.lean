import SpringerLean.Round1705ActualKnotSFluxAE

open MeasureTheory

namespace SpringerLean

/-- Since the actual time fderiv vanishes almost everywhere on a knot
level, the radial-flux formula may use either printed one-sided slope,
or indeed any real slope. -/
theorem actualEnergyFluxRdiv_knot_anySlope_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        ∀ fp : ℝ,
          let U := actualHarmonicPhaseField F k beta
          let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
          let t := actualHarmonicMultiplierTime F k
          let phi := fun w => energyMultiplierF (t w)
          let u := U z / y z
          let yr := (fderiv ℝ y z) (z / ‖z‖)
          let Ur := (fderiv ℝ U z) (z / ‖z‖)
          actualEnergyFluxRdiv F k beta z =
            (y z / ‖z‖ * phi z - (phi z + t z * fp) * yr -
              (k : ℝ) * fp) * u^2 + 2 * phi z * u * Ur := by
  have htime : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (actualHarmonicMultiplierTime F k) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
        F hc k (energyMultiplierKnotTime i))
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k,
      htime] with z hdiff ht i hreg hlevel fp
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let phi : ℂ → ℝ := fun w =>
    energyMultiplierF (actualHarmonicMultiplierTime F k w)
  have hphi := (hdiff i hreg hlevel).2.1
  have htime0 := ht i hreg hlevel
  have hrad : (fderiv ℝ phi z) (z / ‖z‖) =
      fp * (fderiv ℝ (actualHarmonicMultiplierTime F k) z) (z / ‖z‖) := by
    simp [phi, hphi.fderiv, htime0]
  have hR := actualHarmonic_phaseFluxR_divergence
    F hc k beta phi fp hball hz0 hH hphi.differentiableAt hrad
  simpa only [actualEnergyFluxRdiv, phi] using hR

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxRdiv_knot_anySlope_ae
