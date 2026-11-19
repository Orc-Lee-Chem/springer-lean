import SpringerLean.Round1716ActualPhaseFieldPowerBound
import SpringerLean.Round1668ActualCombinedFluxDefinitions

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- Cartesian P flux as an actual complex-valued vector field. -/
def actualEnergyFluxPField (F : ℂ → ℂ) (k : ℕ)
    (beta z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k beta
  let chi := energyMultiplierChi (actualHarmonicMultiplierTime F k z)
  Complex.mk
    (chi * U z * (fderiv ℝ U z) (1 : ℂ))
    (chi * U z * (fderiv ℝ U z) Complex.I)

/-- Cartesian R flux. The zero-divisor convention sets its value to
zero at a filling zero and at the source center. -/
def actualEnergyFluxRField (F : ℂ → ℂ) (k : ℕ)
    (beta z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k beta
  let phi := energyMultiplierF (actualHarmonicMultiplierTime F k z)
  let y := ‖actualHarmonic F z‖
  Complex.mk
    ((phi * (U z)^2 / y) * z.re / ‖z‖)
    ((phi * (U z)^2 / y) * z.im / ‖z‖)

/-- Cartesian S flux. -/
def actualEnergyFluxSField (F : ℂ → ℂ) (k : ℕ)
    (beta z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k beta
  let sigma := energyMultiplierSigma (actualHarmonicMultiplierTime F k z)
  let Q := (conj (actualHarmonic F z))⁻¹
  Complex.mk (sigma * (U z)^2 * Q.re)
    (sigma * (U z)^2 * Q.im)

/-- The signed combined actual phase-energy flux used for disk
integration. -/
def actualEnergyFluxField (F : ℂ → ℂ) (k : ℕ)
    (beta z : ℂ) : ℂ :=
  actualEnergyFluxPField F k beta z +
    (4 * ((k : ℝ) - 1)) • actualEnergyFluxRField F k beta z -
    (2 * ((k : ℝ) - 1)) • actualEnergyFluxSField F k beta z

def actualCartesianDiv (J : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ (fun w => (J w).re) z) (1 : ℂ) +
    (fderiv ℝ (fun w => (J w).im) z) Complex.I

theorem actualEnergyFluxPdiv_eq_cartesianDiv
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) :
    actualEnergyFluxPdiv F k beta z =
      actualCartesianDiv (actualEnergyFluxPField F k beta) z := by
  rfl

theorem actualEnergyFluxRdiv_eq_cartesianDiv
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) :
    actualEnergyFluxRdiv F k beta z =
      actualCartesianDiv (actualEnergyFluxRField F k beta) z := by
  rfl

theorem actualEnergyFluxSdiv_eq_cartesianDiv
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) :
    actualEnergyFluxSdiv F k beta z =
      actualCartesianDiv (actualEnergyFluxSField F k beta) z := by
  rfl

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFluxPdiv_eq_cartesianDiv
#print axioms SpringerLean.actualEnergyFluxRdiv_eq_cartesianDiv
#print axioms SpringerLean.actualEnergyFluxSdiv_eq_cartesianDiv
