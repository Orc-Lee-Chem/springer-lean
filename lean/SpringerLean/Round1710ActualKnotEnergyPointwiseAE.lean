import SpringerLean.Round1709ActualKnotFluxCostAE
import SpringerLean.Round1675ActualCellEnergyPointwise

open MeasureTheory

namespace SpringerLean
noncomputable section

/-- The actual C=25/16 pointwise phase-energy estimate at all physical
multiplier knots, almost everywhere on their possibly positive-area
level sets. -/
theorem actualHarmonicPhase_pointwise_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        let U := actualHarmonicPhaseField F k beta
        let p := Real.sqrt
          (((fderiv ℝ U z) (1 : ℂ))^2 +
           ((fderiv ℝ U z) Complex.I)^2)
        let u := U z / ‖actualHarmonic F z‖
        let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
        (k : ℝ)^2 * u^2 + b * actualEnergyFluxDiv F k beta z ≤
          (25 / 16) * p^2 := by
  filter_upwards
    [actualEnergyFlux_cost_le_knot_ae F hc k (by omega) beta hbeta]
    with z hcostAE i hreg hlevel
  obtain ⟨hz, _, _⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let U := actualHarmonicPhaseField F k beta
  let p := Real.sqrt
    (((fderiv ℝ U z) (1 : ℂ))^2 +
     ((fderiv ℝ U z) Complex.I)^2)
  let u := U z / ‖actualHarmonic F z‖
  let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
  let t := actualHarmonicMultiplierTime F k z
  let v := energyMultiplierSplineValue t
  have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
  obtain ⟨cp, fp, sp, hprofile⟩ :=
    energyMultiplierSpline_profile_exists t ht
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hcost := hcostAE i hreg hlevel cp fp sp
  have hledger := energyMultiplier_local_cost_ledger
    (k : ℝ) (by exact_mod_cast (by omega : 1 < k))
    v cp fp sp p |u|
  rw [sq_abs] at hledger
  have hflux :
      let A := energyMultiplierA (1 / (k : ℝ)) fp sp v
      let B := energyMultiplierB (1 / (k : ℝ))
        (1 / ((k : ℝ) - 1))
        ((k : ℝ) / (4 * ((k : ℝ) - 1))) cp fp sp v
      let D := energyMultiplierD (1 / ((k : ℝ) - 1))
        (k : ℝ) cp v
      (k : ℝ)^2 * A * u^2 + b * actualEnergyFluxDiv F k beta z ≤
        D * p^2 + (k : ℝ) * B * |u| * p := by
    dsimp only at hcost hledger ⊢
    nlinarith [hcost, hledger]
  exact phaseEnergy_pointwise_of_flux_bound hk ht hprofile hp hflux

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_knot_ae
