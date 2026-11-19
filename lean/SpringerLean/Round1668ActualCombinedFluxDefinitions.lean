import SpringerLean.Round1667SignedFluxLedger
import SpringerLean.Round1666ActualSigmaGradientCost

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- Cartesian divergence of the actual phase-gradient flux, with the
globally defined chi spline. -/
def actualEnergyFluxPdiv (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  let U := actualHarmonicPhaseField F k beta
  let chi : ℂ → ℝ := fun w => energyMultiplierChi
    (actualHarmonicMultiplierTime F k w)
  (fderiv ℝ (fun w => chi w*U w*(fderiv ℝ U w (1:ℂ))) z) (1:ℂ) +
  (fderiv ℝ (fun w => chi w*U w*(fderiv ℝ U w Complex.I)) z) Complex.I

/-- Cartesian divergence of the actual radial flux. -/
def actualEnergyFluxRdiv (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let phi : ℂ → ℝ := fun w => energyMultiplierF
    (actualHarmonicMultiplierTime F k w)
  (fderiv ℝ
    (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
  (fderiv ℝ
    (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I

/-- Cartesian divergence of the actual inverse-filling drift flux. -/
def actualEnergyFluxSdiv (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  let U := actualHarmonicPhaseField F k beta
  let sigma : ℂ → ℝ := fun w => energyMultiplierSigma
    (actualHarmonicMultiplierTime F k w)
  let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
  (fderiv ℝ (fun w => sigma w*(U w)^2*(Q w).re) z) (1:ℂ) +
  (fderiv ℝ (fun w => sigma w*(U w)^2*(Q w).im) z) Complex.I

/-- The one combined flux used in the eventual disk integral. -/
def actualEnergyFluxDiv (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  actualEnergyFluxPdiv F k beta z +
    4*((k:ℝ)-1)*actualEnergyFluxRdiv F k beta z -
    2*((k:ℝ)-1)*actualEnergyFluxSdiv F k beta z

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFluxDiv
