import SpringerLean.Round1677ActualTailFluxes
import SpringerLean.Round1667SignedFluxLedger

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- Signed combined-flux identity on the constant tail t>1. -/
theorem actualEnergyFlux_signed_ledger_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
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
    let drift := U z*(Q.re*ux+Q.im*uy)
    let ctrace := (U z)^2 *
      (deriv (exteriorForwardGerm F) (conj z) /
        (actualHarmonic F z)^2).re
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    b*actualEnergyFluxDiv F k beta z =
      b*chi*(ux^2+uy^2)-
      (k:ℝ)^2*chi*u^2+
      (k:ℝ)*(chi-sigma)*drift+
      2*(k:ℝ)*f*u*Ur-
      (k:ℝ)*f*yr*u^2+
      (k:ℝ)*(y z/‖z‖)*f*u^2+
      (k:ℝ)*sigma*ctrace := by
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
  let drift := U z*(Q.re*ux+Q.im*uy)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  have hK : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hforms := actualEnergyFlux_tail_formulas
    F hc k beta hz hz0 hH htail
  have hPDE0 := actualHarmonicPhase_fluxPS_drift_cancellation
    F hc k hk beta chi sigma hz hH
  have hP : actualEnergyFluxPdiv F k beta z =
      chi*(ux^2+uy^2)+chi*(U z*actualHarmonicPhaseLaplacian F k beta z)-
        0*((k:ℝ)*u*Ur+t*0) := by
    convert hforms.1 using 1 <;> ring
  have hR : actualEnergyFluxRdiv F k beta z =
      ((y z/‖z‖)*f-(f+t*0)*yr-(k:ℝ)*0)*u^2+
      2*f*u*Ur := by
    convert hforms.2.1 using 1 <;> ring
  have hS : actualEnergyFluxSdiv F k beta z =
      2*sigma*drift+0-2*sigma*ctrace := by
    convert hforms.2.2 using 1 <;> ring
  have hPDE : chi*(U z*actualHarmonicPhaseLaplacian F k beta z)-
      4*((k:ℝ)-1)*sigma*drift =
      4*((k:ℝ)-1)*(chi-sigma)*drift-
        4*(k:ℝ)*((k:ℝ)-1)*chi*u^2 := by
    convert hPDE0 using 1 <;> ring
  have hledger := energyFlux_signed_ledger
    (K := (k:ℝ)) (χ := chi) (f := f) (σ := sigma)
    (t := t) (cp := 0) (fp := 0)
    (p2 := ux^2+uy^2) (u := u) (drift := drift)
    (ur := Ur) (yr := yr) (yOverR := y z/‖z‖)
    (ugrad := 0) (sigmaGrad := 0)
    (ctrace := ctrace)
    (lap := U z*actualHarmonicPhaseLaplacian F k beta z)
    (P := actualEnergyFluxPdiv F k beta z)
    (R := actualEnergyFluxRdiv F k beta z)
    (S := actualEnergyFluxSdiv F k beta z)
    hK hP hR hS hPDE
  change b*(actualEnergyFluxPdiv F k beta z+
    4*((k:ℝ)-1)*actualEnergyFluxRdiv F k beta z-
    2*((k:ℝ)-1)*actualEnergyFluxSdiv F k beta z) = _
  convert hledger using 1 <;> ring

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_signed_ledger_tail
