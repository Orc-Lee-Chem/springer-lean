import SpringerLean.Round1679ActualTailFluxCost
import SpringerLean.Round1599PhaseFluxCancellation

namespace SpringerLean
noncomputable section

/-- The actual phase-field C=25/16 inequality on the open constant
tail beyond the final multiplier knot. -/
theorem actualHarmonicPhase_pointwise_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (htail : 1 < actualHarmonicMultiplierTime F k z) :
    let U := actualHarmonicPhaseField F k beta
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    let u := U z/‖actualHarmonic F z‖
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    (k:ℝ)^2*u^2+b*actualEnergyFluxDiv F k beta z ≤
      (25/16)*p^2 := by
  let U := actualHarmonicPhaseField F k beta
  let p := Real.sqrt
    (((fderiv ℝ U z) (1:ℂ))^2+
     ((fderiv ℝ U z) Complex.I)^2)
  let u := U z/‖actualHarmonic F z‖
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  let t := actualHarmonicMultiplierTime F k z
  let v := energyMultiplierSplineValue t
  have hk2 : 2 ≤ k := by omega
  have hK : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hv := energyMultiplierSplineValue_eq_tail t
    (by rw [energyMultiplierKnotTime_last]; exact htail.le)
  have hslopes :
      ((energyMultiplierEndpointRaw 42).cp:ℝ) = 0 ∧
      ((energyMultiplierEndpointRaw 42).fp:ℝ) = 0 ∧
      ((energyMultiplierEndpointRaw 42).sp:ℝ) = 0 := by
    norm_num [energyMultiplierEndpointRaw, energyMultiplierNode,
      energyMultiplierSlope]
  have hprofile : EnergyMultiplierProfileAt t v 0 0 0 := by
    refine ⟨rfl, Or.inr ?_⟩
    exact ⟨hv, hslopes.1.symm, hslopes.2.1.symm, hslopes.2.2.symm⟩
  have hcost := actualEnergyFlux_cost_le_tail
    F hc k hk2 beta hbeta hz hz0 hH htail
  have hledger := energyMultiplier_local_cost_ledger
    (k:ℝ) hK v 0 0 0 p |u|
  rw [sq_abs] at hledger
  have hflux :
      let A := energyMultiplierA (1/(k:ℝ)) 0 0 v
      let B := energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) 0 0 0 v
      let D := energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) 0 v
      (k:ℝ)^2*A*u^2+b*actualEnergyFluxDiv F k beta z ≤
        D*p^2+(k:ℝ)*B*|u| * p := by
    dsimp only at hcost hledger ⊢
    nlinarith [hcost,hledger]
  exact phaseEnergy_pointwise_of_flux_bound hk ht hprofile hp hflux

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_tail
