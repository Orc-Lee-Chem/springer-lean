import SpringerLean.Round1676ActualTailMultiplierDerivatives
import SpringerLean.Round1668ActualCombinedFluxDefinitions

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- On the constant multiplier tail, all cutoff-gradient terms vanish
in the actual P, R and S flux divergences. -/
theorem actualEnergyFlux_tail_formulas
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (htail : 1 < actualHarmonicMultiplierTime F k z) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k z
    let chi := energyMultiplierChi t
    let f := energyMultiplierF t
    let sigma := energyMultiplierSigma t
    let Q := (conj (actualHarmonic F z))⁻¹
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let u := U z/y z
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    let yr := (fderiv ℝ y z) (z/‖z‖)
    actualEnergyFluxPdiv F k beta z =
      chi*(ux^2+uy^2)+chi*U z*actualHarmonicPhaseLaplacian F k beta z ∧
    actualEnergyFluxRdiv F k beta z =
      ((y z/‖z‖)*f-f*yr)*u^2+2*f*u*Ur ∧
    actualEnergyFluxSdiv F k beta z =
      2*sigma*U z*(Q.re*ux+Q.im*uy)-
        2*sigma*(U z)^2*
          (deriv (exteriorForwardGerm F) (conj z) /
            (actualHarmonic F z)^2).re := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k z
  let chi := energyMultiplierChi t
  let f := energyMultiplierF t
  let sigma := energyMultiplierSigma t
  let Q := (conj (actualHarmonic F z))⁻¹
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let u := U z/y z
  let Ur := (fderiv ℝ U z) (z/‖z‖)
  let yr := (fderiv ℝ y z) (z/‖z‖)
  let cχ : ℂ → ℝ := fun w => energyMultiplierChi
    (actualHarmonicMultiplierTime F k w)
  let cσ : ℂ → ℝ := fun w => energyMultiplierSigma
    (actualHarmonicMultiplierTime F k w)
  have hdiff := actualEnergyMultiplier_compositions_differentiableAt_tail
    F hc k hz hz0 hH htail
  have hzero1 := actualEnergyMultiplier_tail_directional_derivatives
    F hc k hz hz0 hH htail (1:ℂ)
  have hzeroI := actualEnergyMultiplier_tail_directional_derivatives
    F hc k hz hz0 hH htail Complex.I
  have hP0 := actualHarmonic_phaseFluxP_divergence
    F hc k beta cχ hz hdiff.1
  have hR0 := actualHarmonic_phaseFluxR_of_outer_multiplier
    F hc k beta energyMultiplierF hz hz0 hH
    (energyMultiplierSpline_derivs_on_tail t htail).2.1.1
  have hS0 := actualHarmonic_phaseFluxS_divergence
    F hc k beta cσ hz hH hdiff.2.2
  have hf0 := (energyMultiplierSpline_derivs_on_tail t htail).2.1.2
  dsimp only at hP0 hR0 hS0 hzero1 hzeroI ⊢
  refine ⟨?_, ?_, ?_⟩
  · change actualEnergyFluxPdiv F k beta z = _ at hP0
    rw [hzero1.1, hzeroI.1] at hP0
    convert hP0 using 1 <;> ring
  · change actualEnergyFluxRdiv F k beta z = _ at hR0
    rw [hf0] at hR0
    convert hR0 using 1 <;> ring
  · change actualEnergyFluxSdiv F k beta z = _ at hS0
    rw [hzero1.2.2, hzeroI.2.2] at hS0
    convert hS0 using 1 <;> ring

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_tail_formulas
