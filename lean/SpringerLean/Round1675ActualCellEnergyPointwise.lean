import SpringerLean.Round1674ActualFluxCost
import SpringerLean.Round1599PhaseFluxCancellation

namespace SpringerLean
noncomputable section

/-- The actual phase-field energy inequality pointwise on every open
affine cell, before knot and zero-set treatment and disk integration. -/
theorem actualHarmonicPhase_pointwise_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
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
  let r₀ := energyMultiplierEndpointRaw (2*i.val)
  let cp : ℝ := r₀.cp
  let fp : ℝ := r₀.fp
  let sp : ℝ := r₀.sp
  have hk2 : 2 ≤ k := by omega
  have hK : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have htimes := energyMultiplier_cell_endpoint_times i
  have hleft0 : (energyMultiplierEndpointRaw (2*i.val)).t ≤ t := by
    rw [htimes.1]
    exact le_of_lt hleft
  have hright0 : t ≤ (energyMultiplierEndpointRaw (2*i.val+1)).t := by
    rw [htimes.2]
    exact le_of_lt hright
  obtain ⟨lam, hlam0, hlam1, htime⟩ :=
    energyMultiplier_cell_time_surjective i t hleft0 hright0
  have hv := energyMultiplierSplineValue_eq_cell i lam t htime
    (le_of_lt hleft) (le_of_lt hright)
  have hprofile : EnergyMultiplierProfileAt t v cp fp sp := by
    refine ⟨rfl, Or.inl ?_⟩
    exact ⟨i, lam, hlam0, hlam1, hv, rfl, rfl, rfl⟩
  have hcost := actualEnergyFlux_cost_le_cell
    F hc k hk2 beta hbeta i hz hz0 hH hleft hright
  have hledger := energyMultiplier_local_cost_ledger
    (k:ℝ) hK v cp fp sp p |u|
  rw [sq_abs] at hledger
  have hflux :
      let A := energyMultiplierA (1/(k:ℝ)) fp sp v
      let B := energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) cp fp sp v
      let D := energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) cp v
      (k:ℝ)^2*A*u^2+b*actualEnergyFluxDiv F k beta z ≤
        D*p^2+(k:ℝ)*B*|u| * p := by
    dsimp only at hcost hledger ⊢
    nlinarith [hcost,hledger]
  exact phaseEnergy_pointwise_of_flux_bound hk ht hprofile hp hflux

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_cell
