import SpringerLean.Round1706ActualKnotRFluxAnySlopeAE
import SpringerLean.Round1645ActualChiGradientCancellation

open MeasureTheory

namespace SpringerLean

/-- The signed chi-gradient cancellation remains valid at an actual
physical knot for any slope, since both the multiplier and time
gradients vanish there almost everywhere. -/
theorem actualEnergyMultiplier_chi_gradient_identity_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        ∀ cp : ℝ,
          let U := actualHarmonicPhaseField F k beta
          let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
          let t := actualHarmonicMultiplierTime F k
          let chi : ℂ → ℝ := fun w => energyMultiplierChi (t w)
          let ux := (fderiv ℝ U z) (1 : ℂ)
          let uy := (fderiv ℝ U z) Complex.I
          let u := U z / y z
          U z * ((fderiv ℝ chi z) (1 : ℂ) * ux +
            (fderiv ℝ chi z) Complex.I * uy) =
          -cp * ((k : ℝ) * u * (fderiv ℝ U z) (z / ‖z‖) +
            t z * u * ((fderiv ℝ y z) (1 : ℂ) * ux +
              (fderiv ℝ y z) Complex.I * uy)) := by
  have htime : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (actualHarmonicMultiplierTime F k) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
        F hc k (energyMultiplierKnotTime i))
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k,
      htime] with z hcomp ht i hreg hlevel cp
  obtain ⟨hz, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  let chi : ℂ → ℝ := fun w => energyMultiplierChi (t w)
  have hchi := (hcomp i hreg hlevel).1
  have ht0 := ht i hreg hlevel
  have hchi1 : (fderiv ℝ chi z) (1 : ℂ) =
      cp * (fderiv ℝ t z) (1 : ℂ) := by
    simp [chi, t, hchi.fderiv, ht0]
  have hchiI : (fderiv ℝ chi z) Complex.I =
      cp * (fderiv ℝ t z) Complex.I := by
    simp [chi, t, hchi.fderiv, ht0]
  have ht1 := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH (1 : ℂ)
  have htI := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH Complex.I
  have hr := source_radius_fderiv_coordinates hz0
  have hUr := fderiv_radial_cartesian U z hz0
  have hy0 : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  dsimp only at hchi1 hchiI ht1 htI hUr ⊢
  rw [hchi1, hchiI, ht1, htI, hr.1, hr.2, hUr]
  field_simp [hy0, norm_ne_zero_iff.mpr hz0]
  ring

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_chi_gradient_identity_knot_ae
