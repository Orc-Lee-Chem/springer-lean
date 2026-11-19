import SpringerLean.Round1668ActualCombinedFluxDefinitions

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- The exact signed local divergence of the combined actual multiplier
flux on an open affine cell. No cost has yet been bounded by modulus. -/
theorem actualEnergyFlux_signed_ledger_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let chi := energyMultiplierChi (t z)
    let f := energyMultiplierF (t z)
    let sigma := energyMultiplierSigma (t z)
    let cp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).cp
    let fp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).fp
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    let Q := (conj (actualHarmonic F z))⁻¹
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let u := U z/y z
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let drift := U z*(Q.re*ux+Q.im*uy)
    let ugrad := u*((fderiv ℝ y z) (1:ℂ)*ux+
      (fderiv ℝ y z) Complex.I*uy)
    let sigmaGrad := (U z)^2 *
      ((fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) (1:ℂ)*Q.re+
       (fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) Complex.I*Q.im)
    let ctrace := (U z)^2 *
      (deriv (exteriorForwardGerm F) (conj z) /
        (actualHarmonic F z)^2).re
    b*actualEnergyFluxDiv F k beta z =
      b*chi*(ux^2+uy^2)-
      (k:ℝ)^2*(chi+fp)*u^2+
      (k:ℝ)*(chi-sigma)*drift+
      (k:ℝ)*(2*f-b*cp)*u*Ur-
      (k:ℝ)*(f+t z*fp)*yr*u^2+
      (k:ℝ)*(y z/‖z‖)*f*u^2-
      b*cp*t z*ugrad-
      ((k:ℝ)/2)*sigmaGrad+
      (k:ℝ)*sigma*ctrace := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  let chi := energyMultiplierChi (t z)
  let f := energyMultiplierF (t z)
  let sigma := energyMultiplierSigma (t z)
  let cp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).cp
  let fp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).fp
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let u := U z/y z
  let Ur := (fderiv ℝ U z) (z/‖z‖)
  let yr := (fderiv ℝ y z) (z/‖z‖)
  let drift := U z*(Q.re*ux+Q.im*uy)
  let ugrad := u*((fderiv ℝ y z) (1:ℂ)*ux+
    (fderiv ℝ y z) Complex.I*uy)
  let sigmaGrad := (U z)^2 *
    ((fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) (1:ℂ)*Q.re+
     (fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) Complex.I*Q.im)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  have hK : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hP0 := actualHarmonic_phaseFluxP_explicit_cell
    F hc k beta i hz hz0 hH hleft hright
  have hchi := actualEnergyMultiplier_chi_gradient_identity
    F hc k beta i hz hz0 hH hleft hright
  have hR0 := actualHarmonic_phaseFluxR_explicit_cell
    F hc k beta i hz hz0 hH hleft hright
  have hS0 := actualHarmonic_phaseFluxS_explicit_cell
    F hc k beta i hz hz0 hH hleft hright
  have hPDE0 := actualHarmonicPhase_fluxPS_drift_cancellation
    F hc k hk beta chi sigma hz hH
  dsimp only at hP0 hchi hR0 hS0 hPDE0 ⊢
  have hP : actualEnergyFluxPdiv F k beta z =
      chi*(ux^2+uy^2)+chi*(U z*actualHarmonicPhaseLaplacian F k beta z)-
        cp*((k:ℝ)*u*Ur+t z*ugrad) := by
    change actualEnergyFluxPdiv F k beta z = _ at hP0
    rw [hchi] at hP0
    convert hP0 using 1 <;> ring
  have hR : actualEnergyFluxRdiv F k beta z =
      ((y z/‖z‖)*f-(f+t z*fp)*yr-(k:ℝ)*fp)*u^2+
      2*f*u*Ur := by
    exact hR0
  have hS : actualEnergyFluxSdiv F k beta z =
      2*sigma*drift+sigmaGrad-2*sigma*ctrace := by
    change actualEnergyFluxSdiv F k beta z = _ at hS0
    convert hS0 using 1 <;> ring
  have hPDE : chi*(U z*actualHarmonicPhaseLaplacian F k beta z)-
      4*((k:ℝ)-1)*sigma*drift =
      4*((k:ℝ)-1)*(chi-sigma)*drift-
        4*(k:ℝ)*((k:ℝ)-1)*chi*u^2 := by
    convert hPDE0 using 1 <;> ring
  have hledger := energyFlux_signed_ledger
    (K := (k:ℝ)) (χ := chi) (f := f) (σ := sigma)
    (t := t z) (cp := cp) (fp := fp)
    (p2 := ux^2+uy^2) (u := u) (drift := drift)
    (ur := Ur) (yr := yr) (yOverR := y z/‖z‖)
    (ugrad := ugrad) (sigmaGrad := sigmaGrad)
    (ctrace := ctrace)
    (lap := U z*actualHarmonicPhaseLaplacian F k beta z)
    (P := actualEnergyFluxPdiv F k beta z)
    (R := actualEnergyFluxRdiv F k beta z)
    (S := actualEnergyFluxSdiv F k beta z)
    hK hP hR hS hPDE
  simpa only [actualEnergyFluxDiv] using hledger

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_signed_ledger_cell
