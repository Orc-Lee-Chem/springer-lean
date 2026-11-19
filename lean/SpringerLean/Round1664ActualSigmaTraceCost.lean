import SpringerLean.Round1663DriftTraceCost
import SpringerLean.Round1660EnergySplineNonnegative

open scoped ComplexConjugate

namespace SpringerLean

/-- The signed sigma trace in the actual phase flux is paid by one
potential term and one mixed phase-gradient term. -/
theorem actualHarmonicPhase_sigma_trace_cost_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let y := ‖actualHarmonic F z‖
    let t := actualHarmonicMultiplierTime F k z
    let sigma := energyMultiplierSigma t
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    sigma*(U z)^2*
      (deriv (exteriorForwardGerm F) (conj z) /
        (actualHarmonic F z)^2).re ≤
      sigma*((U z/y)^2+|U z/y| * p/(k:ℝ)) := by
  let U := actualHarmonicPhaseField F k beta
  let y := ‖actualHarmonic F z‖
  let t := actualHarmonicMultiplierTime F k z
  let sigma := energyMultiplierSigma t
  let p := Real.sqrt
    (((fderiv ℝ U z) (1:ℂ))^2+
     ((fderiv ℝ U z) Complex.I)^2)
  have hs : 0 ≤ sigma :=
    (energyMultiplierSpline_nonneg t
      (actualHarmonicMultiplierTime_nonneg F k hz)).2.2
  have htrace := phase_drift_trace_cost_le
    (actualHarmonic F z)
    (deriv (exteriorForwardGerm F) (conj z)) hH (U z)
  have hanti := actualHarmonicPhase_antiholomorphic_cost_le
    F hc k hk beta hbeta hz hH
  dsimp only at hanti ⊢
  calc
    sigma*(U z)^2*
      (deriv (exteriorForwardGerm F) (conj z) /
        (actualHarmonic F z)^2).re =
      sigma*((U z)^2*
        (deriv (exteriorForwardGerm F) (conj z) /
          (actualHarmonic F z)^2).re) := by ring
    _ ≤ sigma*(‖deriv (exteriorForwardGerm F) (conj z)‖*
          (U z/y)^2) := mul_le_mul_of_nonneg_left htrace hs
    _ ≤ sigma*((U z/y)^2+|U z/y| * p/(k:ℝ)) :=
      mul_le_mul_of_nonneg_left hanti hs

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_sigma_trace_cost_le
