import SpringerLean.Round1633ExplicitEnergyCertificate

namespace SpringerLean

/-- Actual radial flux with the explicit 22-node multiplier and its
exact printed slope on any open affine cell. -/
theorem actualHarmonic_phaseFluxR_explicit_cell
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
    let phi : ℂ → ℝ := fun w => energyMultiplierF (t w)
    let fp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).fp
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      ((y z/‖z‖)*phi z - (phi z+t z*fp)*yr -
        (k:ℝ)*fp)*u^2 + 2*phi z*u*Ur := by
  have hderivs := energyMultiplierSpline_derivs_on_open_cell i
    (actualHarmonicMultiplierTime F k z) hleft hright
  have hf := hderivs.2.1
  have h := actualHarmonic_phaseFluxR_of_outer_multiplier
    F hc k beta energyMultiplierF hz hz0 hH hf.1
  dsimp only at h ⊢
  rw [hf.2] at h
  exact h

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxR_explicit_cell
