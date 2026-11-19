import SpringerLean.Round1644SourceRadiusCartesianDerivative

namespace SpringerLean

/-- Exact chi-cutoff derivative in the actual phase flux. The radial
term is kept signed so it can combine with the R flux before bounds. -/
theorem actualEnergyMultiplier_chi_gradient_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let chi : ℂ → ℝ := fun w => energyMultiplierChi (t w)
    let cp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).cp
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let u := U z/y z
    U z *
      ((fderiv ℝ chi z) (1:ℂ)*ux +
       (fderiv ℝ chi z) Complex.I*uy) =
      -cp*((k:ℝ)*u*(fderiv ℝ U z) (z/‖z‖) +
        t z*u*((fderiv ℝ y z) (1:ℂ)*ux+
          (fderiv ℝ y z) Complex.I*uy)) := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  have hchi1 := (actualEnergyMultiplier_cell_directional_derivatives
    F hc k i hz hz0 hH hleft hright (1:ℂ)).1
  have hchiI := (actualEnergyMultiplier_cell_directional_derivatives
    F hc k i hz hz0 hH hleft hright Complex.I).1
  have ht1 := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH (1:ℂ)
  have htI := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH Complex.I
  have hr := source_radius_fderiv_coordinates hz0
  have hUr := fderiv_radial_cartesian U z hz0
  have hy0 : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  dsimp only at hchi1 hchiI ht1 htI hUr ⊢
  rw [hchi1,hchiI,ht1,htI,hr.1,hr.2,hUr]
  field_simp [hy0, norm_ne_zero_iff.mpr hz0]
  ring

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_chi_gradient_identity
